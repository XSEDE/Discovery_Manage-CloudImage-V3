#!/usr/bin/env python3

# Copy Jetstream cloud image information from a source (API) to the destination (warehouse)
import argparse
from collections import Counter
import copy
import datetime
from datetime import datetime, timezone, tzinfo, timedelta
from hashlib import md5
import http.client as httplib
import io
import json
import logging
import logging.handlers
import os
import psycopg2
import pwd
import re
import shutil
import signal
import ssl
import sys
from time import sleep
from urllib.parse import urlparse
import pytz
Central = pytz.timezone('US/Central')
UTC = pytz.timezone('UTC')

import django
django.setup()
from django.forms.models import model_to_dict
from django.utils.dateparse import parse_datetime
from django_markup.markup import formatter
from resource_v3.models import *
from processing_status.process import ProcessingActivity

import elasticsearch_dsl.connections
from elasticsearch import Elasticsearch, RequestsHttpConnection

import pdb

def datetime_localparse(indate):
    try:
        return(parse_datetime(indate))
    except:
        return(indate)
    
def datetime_standardize(indate):
    # Localize as Central and convert to UTC
    if isinstance(indate, datetime):
        return(Central.localize(indate).astimezone(tz = UTC))
    else:
        return(indate)

class Format_Description():
#   Initialize a Description that may be html or markup text
#   Functions that append markup
#   Finally convert everything to html using django-markup (don't convert initial if it's already html)
    def __init__(self, value):
        self.markup_stream = io.StringIO()
        self.markup_settings = {'warning_stream': self.markup_stream } # Docutils settings
        self.initial = None
        self.added = None
        if value is None:
            return
        clean_value = value.rstrip()
        if len(clean_value) == 0:
            return
        self.initial = clean_value
    def append(self, value):
        clean_value = value.rstrip()
        if len(clean_value) > 0:
            if self.added is None:
                self.added = clean_value
            else:
                self.added += '\n{0}'.format(clean_value)
    def blank_line(self): # Forced blank line used to start a markup list
        if self.initial or self.added:  # If we have something, prevents blank initial line
            if self.added:
                self.added += '\n'
            else:
                self.added = '\n'
    def html(self, ID=None): # If an ID is provided, log it to record what resource had the warnings
        if self.initial is None and self.added is None:
            return(None)
        initial_html = self.initial and self.initial[:1] == '<'
        if initial_html:
            formatin = '%%INITIAL%%{0}'.format(self.added)
        else:
            formatin = '{0}{1}'.format(self.initial or '', self.added)
        formatout = formatter(formatin, filter_name='restructuredtext', settings_overrides=self.markup_settings)
        warnings = self.markup_stream.getvalue()
        if warnings:
            logger = logging.getLogger('DaemonLog')
            if ID:
                logger.warning('markup warnings for ID: {}'.format(ID))
            for line in warnings.splitlines():
                logger.warning('markup: {}'.format(line))
        if initial_html:
            output = formatout.replace('%%INITIAL%%', self.initial, 1)
        else:
            output = formatout
        return(output)

class HandleLoad():
    def __init__(self):
        parser = argparse.ArgumentParser(epilog='File SRC|DEST syntax: file:<file path and name')
        parser.add_argument('-s', '--source', action='store', dest='src', \
                            help='Content source {postgresql} (default=postgresql)')
        parser.add_argument('-d', '--destination', action='store', dest='dest', \
                            help='Content destination {analyze or warehouse} (default=analyze)')
        parser.add_argument('--ignore_dates', action='store_true', \
                            help='Ignore dates and force full resource refresh')
        parser.add_argument('-l', '--log', action='store', \
                            help='Logging level override to config (default=warning)')
        parser.add_argument('-c', '--config', action='store', default='./route_cloudimage_v3.conf', \
                            help='Configuration file default=./route_cloudimage_v3.conf')
        parser.add_argument('--verbose', action='store_true', \
                            help='Verbose output')
        parser.add_argument('--dev', action='store_true', \
                            help='Running in development environment')
        parser.add_argument('--pdb', action='store_true', \
                            help='Run with Python debugger')
        self.args = parser.parse_args()

        if self.args.pdb:
            pdb.set_trace()

        # Load configuration file
        config_path = os.path.abspath(self.args.config)
        try:
            with open(config_path, 'r') as file:
                conf = file.read()
                file.close()
        except IOError as e:
            raise
        try:
            self.config = json.loads(conf)
        except ValueError as e:
            print('Error "{}" parsing config={}'.format(e, config_path))
            sys.exit(1)

        # Initialize logging from arguments, or config file, or default to WARNING as last resort
        loglevel_str = (self.args.log or self.config.get('LOG_LEVEL', 'WARNING')).upper()
        loglevel_num = getattr(logging, loglevel_str, None)
        if not isinstance(loglevel_num, int):
            raise ValueError('Invalid log level: {}'.format(loglevel_num))
        self.logger = logging.getLogger('DaemonLog')
        self.logger.setLevel(loglevel_num)
        self.formatter = logging.Formatter(fmt='%(asctime)s.%(msecs)03d %(levelname)s %(message)s', \
                                           datefmt='%Y/%m/%d %H:%M:%S')
        self.handler = logging.handlers.TimedRotatingFileHandler(self.config['LOG_FILE'], when='W6', \
                                                                 backupCount = 999, utc = True)
        self.handler.setFormatter(self.formatter)
        self.logger.addHandler(self.handler)

        # Docutils settings
        self.markup_stream = io.StringIO()
        self.markup_settings = {'warning_stream': self.markup_stream }

        # Verify arguments and parse compound arguments
        SOURCE_URL = getattr(self.args, 'src') or self.config.get('SOURCE_URL', None)
        if not SOURCE_URL:
            self.logger.error('Source was not specified')
            sys.exit(1)
        try:
            self.SOURCE_PARSE = urlparse(SOURCE_URL)
        except:
            self.logger.error('Source is missing or invalid')
            sys.exit(1)

        if self.SOURCE_PARSE.scheme not in ['file', 'http', 'https', 'postgresql']:
            self.logger.error('Source not {file, http, https, postgresql}')
            sys.exit(1)
        if not len(self.SOURCE_PARSE.path or '') >= 1:
            self.logger.error('Source is missing a database name')
            sys.exit(1)

        DEST_URL = getattr(self.args, 'dest') or self.config.get('DESTINATION', 'analyze')
        if not DEST_URL:
            self.logger.error('Destination was not specified')
            sys.exit(1)
        try:
            self.DEST_PARSE = urlparse(DEST_URL)
        except:
            self.logger.error('Destination is missing or invalid')
            sys.exit(1)

        if self.DEST_PARSE.scheme not in ['file', 'analyze', 'warehouse']:
            self.logger.error('Destination not {file, analyze, warehouse}')
            sys.exit(1)

        if self.SOURCE_PARSE.scheme in ['file'] and self.DEST_PARSE.scheme in ['file']:
            self.logger.error('Source and Destination can not both be a {file}')
            sys.exit(1)

        # Initialize appliation variables
        self.memory = {}
        self.PROVIDER_URNMAP = self.memory['provider_urnmap'] = {}
        self.Affiliation = 'xsede.org'
        self.URNPrefix = 'urn:ogf:glue2:'
        self.WAREHOUSE_API_PREFIX = 'http://localhost:8000' if self.args.dev else 'https://info.xsede.org/wh1'
        self.WAREHOUSE_API_VERSION = 'v3'
        self.WAREHOUSE_CATALOG = 'ResourceV3'

        # Loading all the Catalog entries for our affiliation
        self.CATALOGS = {}
        for cat in ResourceV3Catalog.objects.filter(Affiliation__exact=self.Affiliation):
            self.CATALOGS[cat.ID] = model_to_dict(cat)

        self.DefaultValidity = timedelta(days = 14)

        self.STEPS = []
        for stepconf in self.config['STEPS']:
            if not stepconf.get('LOCALTYPE'):
                self.logger.error('Step LOCALTYPE is missing or invalid')
                sys.exit(1)
            if not stepconf.get('CATALOGURN'):
                self.logger.error('Step "{}" CATALOGURN is missing or invalid'.format(stepconf.get('LOCALTYPE')))
                sys.exit(1)
            if stepconf['CATALOGURN'] not in self.CATALOGS:
                self.logger.error('Step "{}" CATALOGURN is not define in Resource Catalogs'.format(stepconf.get('LOCALTYPE')))
                sys.exit(1)
            myCAT = self.CATALOGS[stepconf['CATALOGURN']]
            stepconf['SOURCEURL'] = myCAT['CatalogAPIURL']
            
            try:
                #SRCURL = urlparse(stepconf['SOURCEURL'])
                SRCURL = urlparse("sql:SELECT * FROM resource")
            except:
                self.logger.error('Step SOURCE is missing or invalid')
                sys.exit(1)
            if SRCURL.scheme not in ['sql']:
                self.logger.error('Source must be one of {sql}')
                sys.exit(1)
            stepconf['SRCURL'] = SRCURL

            try:
                DSTURL = urlparse(stepconf['DESTINATION'])
            except:
                self.logger.error('Step DESTINATION is missing or invalid')
                sys.exit(1)
            if DSTURL.scheme not in ['function']:
                self.logger.error('Destination must be one of {function}')
                sys.exit(1)
            stepconf['DSTURL'] = DSTURL
            # Merge CATALOG config and STEP config, with latter taking precendence
            self.STEPS.append({**self.CATALOGS[stepconf['CATALOGURN']], **stepconf})
            
        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)
        self.logger.critical('Starting program={} pid={}, uid={}({})'.format(os.path.basename(__file__), os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

    def Connect_Source(self, urlparse): # TODO
        [host, port] = urlparse.netloc.split(':')
        port = port or '5432'
        database = urlparse.path.strip('/')
        conn_string = "host='{}' port='{}' dbname='{}' user='{}' password='{}'".format(host, port, database, self.config['SOURCE_DBUSER'], self.config['SOURCE_DBPASS'] )
        # get a connection, if a connect cannot be made an exception will be raised here
        conn = psycopg2.connect(conn_string)
        # conn.cursor will return a cursor object, you can use this cursor to perform queries
        cursor = conn.cursor()
        self.logger.critical('Connected to PostgreSQL database {} as {}'.format(database, self.config['SOURCE_DBUSER']))
        return(cursor)
 
    def Connect_Elastic(self):
        if 'ELASTIC_HOSTS' in self.config:
            self.logger.critical('Warehouse elastichost={}'.format(self.config['ELASTIC_HOSTS']))
            self.ESEARCH = elasticsearch_dsl.connections.create_connection( \
                hosts = self.config['ELASTIC_HOSTS'], \
                connection_class = RequestsHttpConnection, \
                timeout = 10)
            ResourceV3Index.init()
        else:
            self.ESEARCH = None
    
    def Disconnect_Source(self, cursor):
        cursor.close()
  
    def CATALOGURN_to_URL(self, id):
        return('{}/resource-api/{}/catalog/id/{}/'.format(self.WAREHOUSE_API_PREFIX, self.WAREHOUSE_API_VERSION, id))

    def format_GLOBALURN(self, *args):
        newargs = list(args)
        newargs[0] = newargs[0].rstrip(':')
        return(':'.join(newargs))

    def Retrieve_CloudImages(self, localtype, config):
        import urllib.request, json 
        
        results = []
        nexturl = "https://use.jetstream-cloud.org/api/v2/images?format=json"
        while (nexturl != None):
            with urllib.request.urlopen(nexturl) as url:
                data = json.loads(url.read().decode())
            nexturl = data["next"]
            results = results + data["results"]

        content = {}
        resources = []
        appenvs = []
        for image in results:
            if image.get('description','').startswith('Imported Application -'):
                continue
            resource={}
            resource["ID"] = self.format_GLOBALURN(config['URNPREFIX'], image["uuid"])
            resource["EntityJSON"] = copy.copy(image)
            resource["CreationTime"] = datetime.now(timezone.utc).isoformat()
            resource["Affiliation"] = "xsede.org"
            resource["LocalID"] = image["id"]
            resource["LocalURL"] = image["url"]
            resource["Name"] = image["name"]
#           Replaced on 2020-12-23
#            if len(image["description"]) < 500:
#                resource["ShortDescription"] = image["description"]
#                resource["Description"] = image["description"]
#            else:
#                resource["ShortDescription"] = image["description"].split('\n',2)[0]
#                resource["Description" ] = image["description"]
            resource["ShortDescription"] = None
            resource["Description"] = image["description"]
            resource["Type"] = "Cloud Image"
            resource["QualityLevel"] = "Production"
            resource["ProviderID"] = 'urn:ogf:glue2:info.xsede.org:resource:rdr:resource.organizations:561'
            tag_keywords = ""
            try:
                delimiter = ""
                for tag in image["tags"]:
                    tag_keywords += delimiter+tag["name"]
                    delimiter = " "
            except:
                tag_keywords = None

            resource["Keywords"] = tag_keywords[:500]
            if image["end_date"] != None:
                enddate = datetime.fromtimestamp(id["end_date"])
                validity_td = enddate - dt
                print("validity time is ", validity_td.total_seconds())
                resource["Validity"] = validity_td.total_seconds()
            else:
                resource["Validity"] = None
            res_associations = []
            associations = ""
            for version in image["versions"]:
                appenv = {}
                appenv["AppName"] = image["name"]
                appenv["AppVersion"] = version["name"]
                appenv["Description"] = image["description"]
                appenv["Name"] = image["name"]+"-"+version["name"]
                appenv["ID"] = "urn:glue2:ApplicationEnvironment:"+appenv["Name"]
                res_associations.append("ApplicationEnvironmentID:"+appenv["ID"])
                appenvs.append(appenv)
            try:
                for assoc in res_associations:
                    associations += ","+assoc
            except:
                associations = None
            resource["Associations"] = ""

            resources.append(resource)
            
        content[localtype] = resources
        return(content)

    def Read_SQL(self, cursor, sql, localtype):
        try:
            cursor.execute(sql)
        except psycopg2.Error as e:
            self.logger.error('Failed "{}" with {}: {}'.format(sql, e.pgcode, e.pgerror))
            sys.exit(1)

        COLS = [desc.name for desc in cursor.description]
        DATA = []
        for row in cursor.fetchall():
            DATA.append(dict(zip(COLS, row)))
        return({localtype: DATA})

    #
    # Delete old items (those in 'cur') that weren't updated (those in 'new')
    #
    def Delete_OLD(self, me, cur, new):
        for URN in [id for id in cur if id not in new]:
            try:
                ResourceV3Index.get(id = URN).delete()
            except Exception as e:
                self.logger.error('{} deleting Elastic id={}: {}'.format(type(e).__name__, URN, e))
            try:
                ResourceV3Relation.objects.filter(FirstResourceID__exact = URN).delete()
                ResourceV3.objects.get(pk = URN).delete()
                ResourceV3Local.objects.get(pk = URN).delete()
            except Exception as e:
                self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, URN, e))
            else:
                self.logger.info('{} deleted ID={}'.format(me, URN))
                self.STATS.update({me + '.Delete'})
        return()
    #
    # Update relations and delete relations for myURN that weren't just updated (newURNS)
    #
    def Update_REL(self, myURN, newRELATIONS):
        newURNS = []
        for relatedID in newRELATIONS:
            try:
                relationURN = ':'.join([myURN, md5(relatedID.encode('UTF-8')).hexdigest()])
                relation, created = ResourceV3Relation.objects.get_or_create(
                            ID = relationURN,
                            FirstResourceID = myURN,
                            SecondResourceID = relatedID,
                            RelationType = newRELATIONS[relatedID],
                     )
                relation.save()
            except Exception as e:
                msg = '{} saving Relation ID={}: {}'.format(type(e).__name__, relationURN, e)
                self.logger.error(msg)
                return(False, msg)
            newURNS.append(relationURN)
        try: # Delete myURN relations that weren't just added/updated (newURNS)
            ResourceV3Relation.objects.filter(FirstResourceID__exact = myURN).exclude(ID__in = newURNS).delete()
        except Exception as e:
            self.logger.error('{} deleting Relations for Resource ID={}: {}'.format(type(e).__name__, myURN, e))

    def Warehouse_Resources(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Software'
        myRESTYPE = 'Cloud Image'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items in database
        new = {}   # New/updated items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item
            
        self.RESOURCE_CONTYPE = contype
        for item in content[contype]:
            id_str = str(item['LocalID'])
            myGLOBALURN = item['ID']

            LocalURL = item.get('LocalURL')
            if not LocalURL:
                LocalURL = config.get('SOURCEDEFAULTURL')
                if LocalURL:
                    LocalURL += id_str       # SOURCEDEFAULTURL is a prefix that the ID can be appended to
                
            myNEWRELATIONS = {} # The new relations for this item, key=related ID, value=relation type
            myProviderID = item.get('ProviderID')
            if myProviderID:
                myNEWRELATIONS[myProviderID] = 'Provided By'

            mySupportID = 'urn:ogf:glue2:info.xsede.org:resource:rsp:support.organizations:drupalnodeid:1553'
            myNEWRELATIONS[mySupportID] = 'Supported By'
            
            myHostedID = 'urn:ogf:glue2:info.xsede.org:resource:rdr:resource.base:68'
            myNEWRELATIONS[myHostedID] = 'Hosted On'
                
            try:
                local, created = ResourceV3Local.objects.get_or_create(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = id_str,
                            LocalType = contype,
                            LocalURL = LocalURL,
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item['EntityJSON'],
                    )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                Description = Format_Description(item.get('Description'))
                Description.append('Related Jetstream resources:')
                Description.blank_line()
                Description.append('- View in source catalog: https://use.jetstream-cloud.org/application/images/{}'.format(item.get('LocalID','')))
                Description.append('- Access source catalog: https://use.jetstream-cloud.org/application/images/search')
                Description.append('- Quick Start Guide: https://wiki.jetstream-cloud.org/Quick+Start+Guide')
                Description.append('- Introduction Workshop: https://cvw.cac.cornell.edu/jetstream/')
#                if not bool(BeautifulSoup(Description, "html.parser").find()):      # Test for pre-existing HTML
                resource, created = ResourceV3.objects.get_or_create(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = id_str,
                            QualityLevel = item.get('QualityLevel', None),
                            Name = item.get('Name', None),
                            ResourceGroup = myRESGROUP,
                            Type = item.get('Type', None),
                            ShortDescription = item.get('ShortDescription', None),
                            ProviderID = myProviderID,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = item.get('topics', None),
                            Keywords = item.get('Keywords', None),
                            StartDateTime = item.get('StartDateTime', None),
                            EndDateTime = item.get('EndDateTime', None),
                            Audience = self.Affiliation,
                    )
                resource.save()
                resource.indexing()
            except Exception as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)

            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.STATS.update({me + '.Update'})
            self.logger.debug('{} updated ID={}'.format(contype, myGLOBALURN))

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.log_target(me)
        return(True, '')

    def SaveDaemonLog(self, path):
        # Save daemon log file using timestamp only if it has anything unexpected in it
        try:
            with open(path, 'r') as file:
                lines = file.read()
                if not re.match('^started with pid \d+$', lines) and not re.match('^$', lines):
                    nowstr = datetime.strftime(datetime.now(), '%Y-%m-%d_%H:%M:%S')
                    newpath = '{}.{}'.format(path, nowstr)
                    shutil.move(path, newpath)
                    print('SaveDaemonLog as {}'.format(newpath))
        except Exception as e:
            print('Exception in SaveDaemonLog({})'.format(path))
        return

    def exit_signal(self, signal, frame):
        self.logger.critical('Caught signal={}, exiting...'.format(signal))
        sys.exit(0)

    def run(self):
        while True:
            if self.SOURCE_PARSE.scheme == 'postgresql':
                CURSOR = self.Connect_Source(self.SOURCE_PARSE)
            self.Connect_Elastic()
            self.STATS = Counter()
            self.PROCESSING_SECONDS = {}

            for stepconf in self.STEPS:
                start_utc = datetime.now(timezone.utc)
                pa_application = os.path.basename(__file__)
                pa_function = stepconf['DSTURL'].path
                pa_topic = stepconf['LOCALTYPE']
                pa_about = self.Affiliation
                pa_id = '{}:{}:{}:{}->{}'.format(pa_application, pa_function, pa_topic,
                    stepconf['SRCURL'].scheme, stepconf['DSTURL'].scheme)
                pa = ProcessingActivity(pa_application, pa_function, pa_id , pa_topic, pa_about)

                if stepconf['SRCURL'].scheme != 'sql':   # This is already checked in __inir__
                    self.logger.error('Source scheme must be "sql"')
                    sys.exit(1)
                if stepconf['DSTURL'].scheme != 'function':     # This is already checked in __inir__
                    self.logger.error('Destination scheme must be "function"')
                    sys.exit(1)

                # Retrieve from SOURCE
                content = self.Retrieve_CloudImages(stepconf['LOCALTYPE'], stepconf)
                # Content does not have the expected results
                if stepconf['LOCALTYPE'] not in content:
                    (rc, message) = (False, 'JSON results is missing the \'{}\' element'.format(stepconf['LOCALTYPE']))
                    self.logger.error(message)
                    pa.FinishActivity(rc, message)
                    continue

                (rc, message) = getattr(self, pa_function)(content, stepconf['LOCALTYPE'], stepconf)
                if not rc and message == '':  # No errors
                    message = 'Executed {} in {:.3f}/seconds'.format(pa_function,
                            (datetime.now(timezone.utc) - start_utc).total_seconds())
                pa.FinishActivity(rc, message)

            # Not disconnecting from Elasticsearch
            #self.Disconnect_Source(CURSOR)
            break

    def log_target(self, me):
        summary_msg = 'Processed {} in {:.3f}/seconds: {}/updates, {}/deletes, {}/skipped'.format(me,
            self.PROCESSING_SECONDS[me],
            self.STATS[me + '.Update'], self.STATS[me + '.Delete'], self.STATS[me + '.Skip'])
        self.logger.info(summary_msg)

if __name__ == '__main__':
    try:
        router = HandleLoad()
        myrouter = router.run()
    except Exception as e:
        msg = '{} Exception: {}'.format(type(e).__name__, e)
        router.logger.error(msg)
        sys.exit(1)
    else:
        sys.exit(0)
