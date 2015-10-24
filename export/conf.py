import os
import sys
import gc
import java.lang.Runtime
import copy
from time import gmtime, strftime

# these are the jar file provided with binnavi 4
sys.path.append("../BinNavi.jar")
sys.path.append("../REIL.jar")
sys.path.append("../postgresql-9.1-901.jdbc4.jar")

from BinNavi.API.plugins import StandAlone
from BinNavi.API.reil.mono import *
from BinNavi.API.helpers import *
from BinNavi.API.helpers.Tree import *
from BinNavi.API.reil.ReilHelpers import *
from BinNavi.API.disassembly.ViewGraphHelpers import *
from BinNavi.API.disassembly import EdgeType
from BinNavi.API.reil import OperandType
from BinNavi.API.disassembly import FunctionType
from sets import Set
import time

##################### User var #############################
binnavi_db_url = "localhost"
binnavi_db_name = "binnavi"
binnavi_db_user = "user"
binnavi_db_pass = "pass"


##################### Global var ############################
list_addr_malloc=[] # list of @ to function malloc, realloc etc
list_addr_free=[] # list of @ to function free, g_free etc

# List of wrapper to free
list_func_to_free=["freeaddrinfo","_free",".free","destroy_pool","__m_free","free","xmlFreeFunc","xmlMemFree","_TIFFfree","._TIFFfree",".g_free",".g_list_free",".g_slist_free",".realloc","jas_free","jas_realloc"]

# List of wrapper to malloc
list_func_to_alloc=["calloc","getaddrinfo","xmalloc","xmalloc_set_program_name","_malloc",".malloc",".strdup",".__strdup",".calloc",".realloc","m_malloc","malloc","xmlMemMalloc","xmlMallocLoc","xmlMallocFunc","xmlMallocAtomicLoc","sub_804C540","zcalloc","_TIFFmalloc","._TIFFmalloc","png_malloc","png_malloc_war",".g_malloc0",".g_try_malloc",".g_malloc_n",".g_malloc0_n",".g_malloc",".g_strdup",".g_strdup_printf","jas_malloc","jas_realloc"]
# sub_804C540 pr expr

list_func_analysis_retn_call=[]

