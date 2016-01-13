##### global definition 
path_binnavi    = "PATH_TO_BINNAVI"
path_dependency = "PATH_TO_GUEB+"/dependency/"

binnavi_host        = 'localhost'
binnavi_db_name     = 'GUEB-bin6-ida68'
binnavi_db_username = 'postgres'
binnavi_db_password = 'admin'
binnavi_collab_name = 'Monty'
##########

import sys

# import all jar needed

sys.path.append(path_binnavi+'binnavi-all.jar')
sys.path.append(path_binnavi+'reil.jar')
sys.path.append(path_dependency+'protobuf-java-3.0.0-pre.jar')
sys.path.append(path_dependency+'gueb.jar')

from com.google.security.zynamics.binnavi.API.plugins import StandAlone
from com.google.security.zynamics.binnavi.API.disassembly import FunctionType
from com.google.security.zynamics.reil.algorithms.mono import InstructionGraph 
from com.google.protobuf import *
from com.proto import  *


## export f to p
## addr_call will be useful in a next version (for library importation)
def exportLib(f,addr_call,p):
    f.load()
    floGraph=f.getGraph()
    name=f.getName()
    address_entry=f.getAddress().toLong()*0x100
    addr_to_call=addr_call*0x100

    func=Program.function.newBuilder()

    func.name=name
    func.numberUnlooping=1 # 1unrolling once for all by default
    index=0

    bfReil=f.getReilCode()
    bfReilGraph=bfReil.getGraph()

    for n in floGraph:
	for instr in n.getInstructions():
		if(instr.getMnemonic()=="retn"):
			reil=instr.getReilCode().getNodes()
			for reil_instr in reil :
				a=reil_instr
                                func.addRetns(a.getAddress().toLong()+3)
    for n in floGraph:
	for instr in n.getInstructions():
		if(instr.getMnemonic()=="call"):
			reil=instr.getReilCode().getNodes()
			for reil_instr in reil :
				a=reil_instr
                                func.addCalls(a.getAddress().toLong()+4)
    func.eip=address_entry
    func.addrToCall=addr_to_call
  

    for blocks in bfReilGraph:
		for reil_instru in blocks.getInstructions():
		        node=Program.node.newBuilder()

			op1=reil_instru.getFirstOperand()
			op2=reil_instru.getSecondOperand()
			op3=reil_instru.getThirdOperand()
			op1Val=str(op1.getValue())
			op2Val=str(op2.getValue())
			op3Val=str(op3.getValue())
			if op1Val=="":
				op1Val=" "
			if op2Val=="":
				op2Val=" "
			if op3Val=="":
				op3Val=" "
			node.addr=reil_instru.getAddress().toLong()
			node.nodeDesc=str(reil_instru.getMnemonic())+","+str(op1.getSize())+","+str(op1.getType())+","+op1Val+","+str(op2.getSize())+","+str(op2.getType())+","+op2Val+","+str(op3.getSize())+","+str(op3.getType())+","+op3Val
			func.addNodes(node) 
                block=Program.block.newBuilder()
                block.addr=blocks.getAddress().toLong()
		for inst in blocks.getInstructions():
                        block.addNodesAddr(inst.getAddress().toLong())
                func.addBlocks(block)
		for child in blocks.getChildren():
                        block_relation=Program.block_relation.newBuilder()
                        block_relation.father=blocks.getAddress().toLong()
                        block_relation.son=child.getAddress().toLong()
                        func.addBlockRelations(block_relation)
    p.addFunctions(func)

def find_lib(name,lib):
    for l in lib :
        if (l.getName() == name[1::]) :
            return l
    return None

def list_modules(db) :
    return map(lambda x : x.getName(), db.getModules())

def find_mod(db,name):
    return filter(lambda x : x.getName() == name,db.getModules())[0] 

def list_func(mod):
    mod.load()
    return map(lambda x : x.getName(), mod.getFunctions())

def connect(host,dbname,user,password,collabname):
    pi = StandAlone.getPluginInterface()
    dbm = pi.databaseManager
    dbm.addDatabase(
    "database_description",  # database description
    "org.postgresql.Driver", # database driver
    host,         # database host
    dbname,         # database name
    user,         # database user
    password,     # database password
    collabname,        # collaboration name
    False,                   # save password
    False)                   # auto connect
    db = dbm.databases[0]
    db.connect()
    db.load()
    return db

def export_mod(mod,list_func_to_alloc,list_func_to_free): 
    libs=[]

    p= Program.program.newBuilder()

    heap_func=Program.heap_functions.newBuilder()

    for f in mod.getFunctions():
	print f.getName()
        if list_func_to_alloc.count(str(f.getName())) and list_func_to_free.count(str(f.getName())) :
            heap_func.addCallToMalloc(f.getAddress().toLong());
            heap_func.addCallToFree(f.getAddress().toLong());
        elif list_func_to_alloc.count(str(f.getName())):
            print "Alloc %d" % f.getAddress().toLong()
            heap_func.addCallToMalloc(f.getAddress().toLong());
        elif list_func_to_free.count(str(f.getName())):
            heap_func.addCallToFree(f.getAddress().toLong());
	elif f.getType()==FunctionType.Normal:
	     exportLib(f,f.getAddress().toLong(),p)
	else :
             l = find_lib (f.getName(),libs)
             if(l!=None and l.getType() == FunctionType.Normal):
                print "Lib %s : %x -> %x " % (f.getName(),f.getAddress().toLong(),l.getAddress().toLong())
                exportLib(l,f.getAddress().toLong(),p)


    for f in libs:
	print f.getName()
        if list_func_to_alloc.count(str(f.getName())) and list_func_to_free.count(str(f.getName())) :
            f.load()
            heap_func.addCallToMalloc(f.getAddress().toLong());
            heap_func.addCallToFree(f.getAddress().toLong());
        elif list_func_to_alloc.count(str(f.getName())):
            f.load()
            heap_func.addCallToMalloc(f.getAddress().toLong());
        elif list_func_to_free.count(str(f.getName())):
            f.load()
            heap_func.addCallToFree(f.getAddress().toLong());
	elif f.getType()==FunctionType.Normal:
	     exportLib(f,f.getAddress().toLong(),p)
	else :
             l = find_lib (f.getName(),libs)
             if(l!=None and l.getType() == FunctionType.Normal):
                print "Lib %s : %x -> %x " % (f.getName(),f.getAddress().toLong(),l.getAddress().toLong())
                exportLib(l,f.getAddress().toLong(),p)

    func_root=[]
    call_graph=mod.getCallgraph ()   
    for f in call_graph.getNodes ():
        if not f.getParents() and f.getFunction().getType()==FunctionType.Normal:
            func_root.append(f.getFunction().getName())

    p.setHeapFunc(heap_func)

    f_save=open(mod.getName(),"w")
 


    p.build().writeTo(f_save)
    f_save.close()

    f_root=open(mod.getName()+"-entry-points","w")
    f_root.write("\n".join(func_root))
    f_root.close()

