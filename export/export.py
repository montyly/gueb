from conf import *
import sys

# path to the proto file
sys.path.append(".")

from com.proto import * ;
from com.google.protobuf import *;

def exportSql(f,mod,p):

    f.load()
    floGraph=f.getGraph()
    name=f.getName()
    address_entry=f.getAddress().toLong()*0x100

    func=Program.function.newBuilder()

    func.name=name
    func.numberUnlooping=1 # 1unrolling once for all 
    index=0

    bfReil=f.getReilCode()
    bfReilGraph=bfReil.getGraph()
    instGraph = InstructionGraph.create(bfReilGraph)

    for n in floGraph:
	for instr in n.getInstructions():
		if(instr.getMnemonic()=="retn"):
			reil=instr.getReilCode().getNodes()
			for reil_instr in reil :
				a=reil_instr
                                func.addRetns(a.getAddress().toLong()+3)
			#	c_retn.write(str(a.getAddress().toLong()+3)+"\n")
    for n in floGraph:
	for instr in n.getInstructions():
		if(instr.getMnemonic()=="call"):
			reil=instr.getReilCode().getNodes()
			for reil_instr in reil :
				a=reil_instr
                                func.addCalls(a.getAddress().toLong()+3)

    func.eip=address_entry
    for blocks in bfReilGraph:
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

    for inst in instGraph:
                
        node=Program.node.newBuilder()

	reil_instru=inst.getInstruction()
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
    p.addFunctions(func)


from threading import Thread, InterruptedException

def main():
    gc.enable()
    
    binNaviProxy = StandAlone.getPluginInterface()

    p= Program.program.newBuilder()
    
    binNaviProxy.databaseManager.addDatabase("","org.postgresql.Driver",binnavi_db_url,binnavi_db_name,binnavi_db_user,binnavi_db_pass,False,False)
    db=binNaviProxy.databaseManager.databases[0]
    db.connect()
    db.load()
    mods=db.getModules()

    i=0
    for q in mods:
        print str(i)+" "+q.getName()
        i=i+1
    id=int(raw_input("Enter the id of module : "))

    mod=mods[id]
    mod.load()

    heap_func=Program.heap_functions.newBuilder()

    for f in mod.getFunctions():
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
	     exportSql(f,mod,p)
	else :
	     list_func_analysis_retn_call.append(str(f.getAddress().toLong())) 

    func_root=[]
    call_graph=mod.getCallgraph ()   
    for f in call_graph.getNodes ():
        if not f.getParents() and f.getFunction().getType()==FunctionType.Normal:
            func_root.append(f.getFunction().getName())

    p.setHeapFunc(heap_func)

    f_save=open(mods[id].getName(),"w")
 


    p.build().writeTo(f_save)
    f_save.close()

    f_root=open(mods[id].getName()+"-entry-points","w")
    f_root.write("\n".join(func_root))
    f_root.close()

    sys.exit(0)

if __name__ == '__main__':
    main()
