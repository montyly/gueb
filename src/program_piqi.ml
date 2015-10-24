module rec Program_piqi:
  sig
    type uint64 = int64
    type heap_functions = Heap_functions.t
    type node = Node.t
    type block = Block.t
    type block_relation = Block_relation.t
    type function_ = Function_.t
    type program = Program.t
  end = Program_piqi
and Heap_functions:
  sig
    type t = {
      mutable call_to_malloc: Program_piqi.uint64 list;
      mutable call_to_free: Program_piqi.uint64 list;
    }
  end = Heap_functions
and Node:
  sig
    type t = {
      mutable addr: Program_piqi.uint64;
      mutable node_desc: string;
    }
  end = Node
and Block:
  sig
    type t = {
      mutable addr: Program_piqi.uint64;
      mutable nodes_addr: Program_piqi.uint64 list;
    }
  end = Block
and Block_relation:
  sig
    type t = {
      mutable father: Program_piqi.uint64;
      mutable son: Program_piqi.uint64;
    }
  end = Block_relation
and Function_:
  sig
    type t = {
      mutable name: string;
      mutable nodes: Program_piqi.node list;
      mutable blocks: Program_piqi.block list;
      mutable block_relations: Program_piqi.block_relation list;
      mutable calls: Program_piqi.uint64 list;
      mutable retns: Program_piqi.uint64 list;
      mutable eip: Program_piqi.uint64;
      mutable number_unlooping: Program_piqi.uint64;
    }
  end = Function_
and Program:
  sig
    type t = {
      mutable functions: Program_piqi.function_ list;
      mutable heap_func: Program_piqi.heap_functions;
    }
  end = Program


let rec parse_uint64 x = Piqirun.int64_of_varint x
and packed_parse_uint64 x = Piqirun.int64_of_packed_varint x

and parse_string x = Piqirun.string_of_block x

and parse_heap_functions x =
  let x = Piqirun.parse_record x in
  let _call_to_malloc, x = Piqirun.parse_repeated_field 1 parse_uint64 x in
  let _call_to_free, x = Piqirun.parse_repeated_field 2 parse_uint64 x in
  Piqirun.check_unparsed_fields x;
  {
    Heap_functions.call_to_malloc = _call_to_malloc;
    Heap_functions.call_to_free = _call_to_free;
  }

and parse_node x =
  let x = Piqirun.parse_record x in
  let _addr, x = Piqirun.parse_required_field 1 parse_uint64 x in
  let _node_desc, x = Piqirun.parse_required_field 2 parse_string x in
  Piqirun.check_unparsed_fields x;
  {
    Node.addr = _addr;
    Node.node_desc = _node_desc;
  }

and parse_block x =
  let x = Piqirun.parse_record x in
  let _addr, x = Piqirun.parse_required_field 1 parse_uint64 x in
  let _nodes_addr, x = Piqirun.parse_repeated_field 2 parse_uint64 x in
  Piqirun.check_unparsed_fields x;
  {
    Block.addr = _addr;
    Block.nodes_addr = _nodes_addr;
  }

and parse_block_relation x =
  let x = Piqirun.parse_record x in
  let _father, x = Piqirun.parse_required_field 1 parse_uint64 x in
  let _son, x = Piqirun.parse_required_field 2 parse_uint64 x in
  Piqirun.check_unparsed_fields x;
  {
    Block_relation.father = _father;
    Block_relation.son = _son;
  }

and parse_function_ x =
  let x = Piqirun.parse_record x in
  let _name, x = Piqirun.parse_required_field 1 parse_string x in
  let _nodes, x = Piqirun.parse_repeated_field 2 parse_node x in
  let _blocks, x = Piqirun.parse_repeated_field 3 parse_block x in
  let _block_relations, x = Piqirun.parse_repeated_field 4 parse_block_relation x in
  let _calls, x = Piqirun.parse_repeated_field 5 parse_uint64 x in
  let _retns, x = Piqirun.parse_repeated_field 6 parse_uint64 x in
  let _eip, x = Piqirun.parse_required_field 7 parse_uint64 x in
  let _number_unlooping, x = Piqirun.parse_required_field 8 parse_uint64 x in
  Piqirun.check_unparsed_fields x;
  {
    Function_.name = _name;
    Function_.nodes = _nodes;
    Function_.blocks = _blocks;
    Function_.block_relations = _block_relations;
    Function_.calls = _calls;
    Function_.retns = _retns;
    Function_.eip = _eip;
    Function_.number_unlooping = _number_unlooping;
  }

and parse_program x =
  let x = Piqirun.parse_record x in
  let _functions, x = Piqirun.parse_repeated_field 1 parse_function_ x in
  let _heap_func, x = Piqirun.parse_required_field 2 parse_heap_functions x in
  Piqirun.check_unparsed_fields x;
  {
    Program.functions = _functions;
    Program.heap_func = _heap_func;
  }


let rec gen__uint64 code x = Piqirun.int64_to_varint code x
and packed_gen__uint64 x = Piqirun.int64_to_packed_varint x

and gen__string code x = Piqirun.string_to_block code x

and gen__heap_functions code x =
  let _call_to_malloc = Piqirun.gen_repeated_field 1 gen__uint64 x.Heap_functions.call_to_malloc in
  let _call_to_free = Piqirun.gen_repeated_field 2 gen__uint64 x.Heap_functions.call_to_free in
  Piqirun.gen_record code (_call_to_malloc :: _call_to_free :: [])

and gen__node code x =
  let _addr = Piqirun.gen_required_field 1 gen__uint64 x.Node.addr in
  let _node_desc = Piqirun.gen_required_field 2 gen__string x.Node.node_desc in
  Piqirun.gen_record code (_addr :: _node_desc :: [])

and gen__block code x =
  let _addr = Piqirun.gen_required_field 1 gen__uint64 x.Block.addr in
  let _nodes_addr = Piqirun.gen_repeated_field 2 gen__uint64 x.Block.nodes_addr in
  Piqirun.gen_record code (_addr :: _nodes_addr :: [])

and gen__block_relation code x =
  let _father = Piqirun.gen_required_field 1 gen__uint64 x.Block_relation.father in
  let _son = Piqirun.gen_required_field 2 gen__uint64 x.Block_relation.son in
  Piqirun.gen_record code (_father :: _son :: [])

and gen__function_ code x =
  let _name = Piqirun.gen_required_field 1 gen__string x.Function_.name in
  let _nodes = Piqirun.gen_repeated_field 2 gen__node x.Function_.nodes in
  let _blocks = Piqirun.gen_repeated_field 3 gen__block x.Function_.blocks in
  let _block_relations = Piqirun.gen_repeated_field 4 gen__block_relation x.Function_.block_relations in
  let _calls = Piqirun.gen_repeated_field 5 gen__uint64 x.Function_.calls in
  let _retns = Piqirun.gen_repeated_field 6 gen__uint64 x.Function_.retns in
  let _eip = Piqirun.gen_required_field 7 gen__uint64 x.Function_.eip in
  let _number_unlooping = Piqirun.gen_required_field 8 gen__uint64 x.Function_.number_unlooping in
  Piqirun.gen_record code (_name :: _nodes :: _blocks :: _block_relations :: _calls :: _retns :: _eip :: _number_unlooping :: [])

and gen__program code x =
  let _functions = Piqirun.gen_repeated_field 1 gen__function_ x.Program.functions in
  let _heap_func = Piqirun.gen_required_field 2 gen__heap_functions x.Program.heap_func in
  Piqirun.gen_record code (_functions :: _heap_func :: [])


let gen_uint64 x = gen__uint64 (-1) x
let gen_string x = gen__string (-1) x
let gen_heap_functions x = gen__heap_functions (-1) x
let gen_node x = gen__node (-1) x
let gen_block x = gen__block (-1) x
let gen_block_relation x = gen__block_relation (-1) x
let gen_function_ x = gen__function_ (-1) x
let gen_program x = gen__program (-1) x


let rec default_uint64 () = 0L
and default_string () = ""
and default_heap_functions () =
  {
    Heap_functions.call_to_malloc = [];
    Heap_functions.call_to_free = [];
  }
and default_node () =
  {
    Node.addr = default_uint64 ();
    Node.node_desc = default_string ();
  }
and default_block () =
  {
    Block.addr = default_uint64 ();
    Block.nodes_addr = [];
  }
and default_block_relation () =
  {
    Block_relation.father = default_uint64 ();
    Block_relation.son = default_uint64 ();
  }
and default_function_ () =
  {
    Function_.name = default_string ();
    Function_.nodes = [];
    Function_.blocks = [];
    Function_.block_relations = [];
    Function_.calls = [];
    Function_.retns = [];
    Function_.eip = default_uint64 ();
    Function_.number_unlooping = default_uint64 ();
  }
and default_program () =
  {
    Program.functions = [];
    Program.heap_func = default_heap_functions ();
  }


let piqi = "\226\202\2304\007program\226\231\249\238\001\023piqi/program.proto.piqi\162\244\146\155\011\tcom.proto\218\244\134\182\012\128\001\138\233\142\251\014z\210\203\242$/\232\146\150q\002\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\014call-to-malloc\210\171\158\194\006\006uint64\210\203\242$-\232\146\150q\004\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\012call-to-free\210\171\158\194\006\006uint64\218\164\238\191\004\014heap-functions\218\244\134\182\012i\138\233\142\251\014c\210\203\242$%\232\146\150q\002\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\004addr\210\171\158\194\006\006uint64\210\203\242$*\232\146\150q\004\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\tnode-desc\210\171\158\194\006\006string\218\164\238\191\004\004node\218\244\134\182\012k\138\233\142\251\014e\210\203\242$%\232\146\150q\002\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\004addr\210\171\158\194\006\006uint64\210\203\242$+\232\146\150q\004\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\nnodes-addr\210\171\158\194\006\006uint64\218\164\238\191\004\005block\218\244\134\182\012o\138\233\142\251\014i\210\203\242$'\232\146\150q\002\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\006father\210\171\158\194\006\006uint64\210\203\242$$\232\146\150q\004\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\003son\210\171\158\194\006\006uint64\218\164\238\191\004\014block-relation\218\244\134\182\012\133\003\138\233\142\251\014\254\002\210\203\242$%\232\146\150q\002\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\004name\210\171\158\194\006\006string\210\203\242$$\232\146\150q\004\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\005nodes\210\171\158\194\006\004node\210\203\242$&\232\146\150q\006\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\006blocks\210\171\158\194\006\005block\210\203\242$8\232\146\150q\b\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\015block-relations\210\171\158\194\006\014block-relation\210\203\242$&\232\146\150q\n\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\005calls\210\171\158\194\006\006uint64\210\203\242$&\232\146\150q\012\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\005retns\210\171\158\194\006\006uint64\210\203\242$$\232\146\150q\014\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\003eip\210\171\158\194\006\006uint64\210\203\242$1\232\146\150q\016\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\016number-unlooping\210\171\158\194\006\006uint64\218\164\238\191\004\bfunction\218\244\134\182\012{\138\233\142\251\014u\210\203\242$,\232\146\150q\002\152\182\154\152\004\250\248\214\130\001\218\164\238\191\004\tfunctions\210\171\158\194\006\bfunction\210\203\242$2\232\146\150q\004\152\182\154\152\004\223\162\138\147\001\218\164\238\191\004\theap-func\210\171\158\194\006\014heap-functions\218\164\238\191\004\007program"
include Program_piqi
