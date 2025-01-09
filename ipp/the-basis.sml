
(* This file is generated by make-basis.sml. *)

functor TheBasis (datatype data = 
                     E of int
                   | EQ of string list * int
                   | T
                   | TQ of string list
                   | S of (string * data) list
                   | M of (string * data) list)
   :>
   sig
      val basis1 : (string * data) list
      val basis2 : (string * data) list
   end
   =
   struct

      val sig1_BOOL =
         [("bool", T),
          ("not", E 0),
          ("=", E 0),
          ("xor", E 0)]
      
      val sig1_INTEGER =
         [("int", T),
          ("minInt", E 0),
          ("maxInt", E 0),
          ("~", E 0),
          ("+", E 0),
          ("-", E 0),
          ("*", E 0),
          ("div", E 0),
          ("rem", E 0),
          ("min", E 0),
          ("max", E 0),
          ("abs", E 0),
          ("divmod", E 0),
          ("=", E 0),
          ("<>", E 0),
          ("<", E 0),
          (">", E 0),
          ("<=", E 0),
          (">=", E 0),
          ("compare", E 0),
          ("toString", E 0),
          ("toStringStd", E 0),
          ("fromInt", E 0),
          ("toInt", E 0),
          ("natrecUp", E 0),
          ("natrecDown", E 0)]
      
      val sig1_INT_INF =
         [("int", T),
          ("minInt", E 0),
          ("maxInt", E 0),
          ("~", E 0),
          ("+", E 0),
          ("-", E 0),
          ("*", E 0),
          ("div", E 0),
          ("rem", E 0),
          ("min", E 0),
          ("max", E 0),
          ("abs", E 0),
          ("divmod", E 0),
          ("=", E 0),
          ("<>", E 0),
          ("<", E 0),
          (">", E 0),
          ("<=", E 0),
          (">=", E 0),
          ("compare", E 0),
          ("toString", E 0),
          ("toStringStd", E 0),
          ("fromInt", E 0),
          ("toInt", E 0),
          ("pow", E 0),
          ("log2", E 0),
          ("orb", E 0),
          ("xorb", E 0),
          ("andb", E 0),
          ("notb", E 0),
          ("shl", E 0),
          ("shr", E 0),
          ("natrecUp", E 0),
          ("natrecDown", E 0)]
      
      val sig1_WORD =
         [("word", T),
          ("wordSize", E 0),
          ("toLargeWord", E 0),
          ("toLargeWordX", E 0),
          ("fromLargeWord", E 0),
          ("toInt", E 0),
          ("toIntX", E 0),
          ("fromInt", E 0),
          ("toLargeInt", E 0),
          ("toLargeIntX", E 0),
          ("fromLargeInt", E 0),
          ("andb", E 0),
          ("orb", E 0),
          ("xorb", E 0),
          ("notb", E 0),
          ("shl", E 0),
          ("shr", E 0),
          ("ashr", E 0),
          ("+", E 0),
          ("-", E 0),
          ("*", E 0),
          ("div", E 0),
          ("rem", E 0),
          ("=", E 0),
          ("<>", E 0),
          ("<", E 0),
          (">", E 0),
          ("<=", E 0),
          (">=", E 0),
          ("compare", E 0),
          ("toString", E 0)]
      
      val sig1_STRING =
         [("string", T),
          ("length", E 0),
          ("sub", E 0),
          ("subOpt", E 0),
          ("substring", E 0),
          ("^", E 0),
          ("concat", E 0),
          ("concatWith", E 0),
          ("str", E 0),
          ("implode", E 0),
          ("explode", E 0),
          ("map", E 0),
          ("=", E 0),
          ("<>", E 0),
          ("<", E 0),
          ("<=", E 0),
          (">", E 0),
          (">=", E 0),
          ("compare", E 0),
          ("fields", E 0)]
      
      val sig1_CHAR =
         [("char", T),
          ("ord", E 0),
          ("chr", E 0),
          ("=", E 0),
          ("<>", E 0),
          ("<", E 0),
          (">", E 0),
          ("<=", E 0),
          (">=", E 0),
          ("compare", E 0)]
      
      val sig1_LIST =
         [("list", T),
          ("null", E 0),
          ("length", E 0),
          ("hd", E 0),
          ("tl", E 0),
          ("nth", E 0),
          ("nthOpt", E 0),
          ("take", E 0),
          ("takeOpt", E 0),
          ("drop", E 0),
          ("dropOpt", E 0),
          ("split", E 0),
          ("splitOpt", E 0),
          ("last", E 0),
          ("@", E 0),
          ("rev", E 0),
          ("revAppend", E 0),
          ("foldl", E 0),
          ("foldr", E 0),
          ("map", E 0),
          ("mapi", E 0),
          ("mapPartial", E 0),
          ("revMap", E 0),
          ("revMapi", E 0),
          ("app", E 0),
          ("appi", E 0),
          ("find", E 0),
          ("findmap", E 0),
          ("filter", E 0),
          ("exists", E 0),
          ("all", E 0),
          ("tabulate", E 0)]
      
      val sig1_LIST_PAIR =
         [("UnequalLengths", E 0),
          ("zip", E 0),
          ("zipEq", E 0),
          ("unzip", E 0),
          ("app", E 0),
          ("appEq", E 0),
          ("map", E 0),
          ("mapEq", E 0),
          ("foldl", E 0),
          ("foldr", E 0),
          ("foldlEq", E 0),
          ("foldrEq", E 0),
          ("all", E 0),
          ("exists", E 0),
          ("allEq", E 0)]
      
      val sig1_OPTION =
         [("option", T),
          ("getOpt", E 0),
          ("isSome", E 0),
          ("valOf", E 0),
          ("join", E 0),
          ("map", E 0),
          ("mapPartial", E 0),
          ("app", E 0)]
      
      val sig1_ARRAY =
         [("array", T),
          ("array", E 0),
          ("fromList", E 0),
          ("tabulate", E 0),
          ("length", E 0),
          ("sub", E 0),
          ("update", E 0),
          ("blit", E 0),
          ("subarray", E 0),
          ("foldl", E 0),
          ("foldli", E 0),
          ("foldr", E 0),
          ("foldri", E 0),
          ("app", E 0),
          ("appi", E 0),
          ("find", E 0),
          ("findi", E 0),
          ("findmap", E 0),
          ("findmapi", E 0)]
      
      val sig1_VECTOR =
         [("vector", T),
          ("fromList", E 0),
          ("tabulate", E 0),
          ("length", E 0),
          ("sub", E 0),
          ("map", E 0),
          ("mapi", E 0),
          ("foldl", E 0),
          ("foldli", E 0),
          ("foldr", E 0),
          ("foldri", E 0),
          ("app", E 0),
          ("appi", E 0),
          ("find", E 0),
          ("findi", E 0),
          ("findmap", E 0),
          ("findmapi", E 0)]
      
      val sig1_IO =
         [("ioerr", T), ("Io", E 1), ("ioerrToString", E 0)]
      
      val sig1_TEXT_IO =
         [("instream", T),
          ("outstream", T),
          ("input1", E 0),
          ("inputN", E 0),
          ("inputLine", E 0),
          ("output1", E 0),
          ("output", E 0),
          ("flushOut", E 0),
          ("openIn", E 0),
          ("closeIn", E 0),
          ("openOut", E 0),
          ("openAppend", E 0),
          ("closeOut", E 0),
          ("stdIn", E 0),
          ("stdOut", E 0),
          ("stdErr", E 0),
          ("print", E 0)]
      
      val sig1_BIN_IO =
         [("instream", T),
          ("outstream", T),
          ("input1", E 0),
          ("output1", E 0),
          ("flushOut", E 0),
          ("openIn", E 0),
          ("closeIn", E 0),
          ("openOut", E 0),
          ("openAppend", E 0),
          ("closeOut", E 0)]
      
      val sig1_GENERAL =
         [("order", T),
          ("exn", T),
          ("unit", T),
          ("LESS", E 0),
          ("EQUAL", E 0),
          ("GREATER", E 0),
          ("Div", E 0),
          ("Fail", E 1),
          ("Invalid", E 1),
          ("Subscript", E 0),
          ("!", E 0),
          (":=", E 0),
          ("$", E 0),
          ("fst", E 0),
          ("snd", E 0),
          ("n1of3", E 0),
          ("n2of3", E 0),
          ("n3of3", E 0)]
      
      val sig1_CONT =
         [("cont", T), ("callcc", E 0), ("throw", E 0)]
      
      val basis1 =
         [("BOOL", S sig1_BOOL),
          ("INTEGER", S sig1_INTEGER),
          ("INT_INF", S sig1_INT_INF),
          ("WORD", S sig1_WORD),
          ("STRING", S sig1_STRING),
          ("CHAR", S sig1_CHAR),
          ("LIST", S sig1_LIST),
          ("LIST_PAIR", S sig1_LIST_PAIR),
          ("OPTION", S sig1_OPTION),
          ("ARRAY", S sig1_ARRAY),
          ("VECTOR", S sig1_VECTOR),
          ("IO", S sig1_IO),
          ("TEXT_IO", S sig1_TEXT_IO),
          ("BIN_IO", S sig1_BIN_IO),
          ("GENERAL", S sig1_GENERAL),
          ("CONT", S sig1_CONT),
          ("Bool", M sig1_BOOL),
          ("Int", M sig1_INTEGER),
          ("IntInf", M sig1_INT_INF),
          ("Word", M sig1_WORD),
          ("LargeWord", M sig1_WORD),
          ("Word8", M sig1_WORD),
          ("Word32", M sig1_WORD),
          ("Word64", M sig1_WORD),
          ("String", M sig1_STRING),
          ("Char", M sig1_CHAR),
          ("List", M sig1_LIST),
          ("ListPair", M sig1_LIST_PAIR),
          ("Option", M sig1_OPTION),
          ("Array", M sig1_ARRAY),
          ("Vector", M sig1_VECTOR),
          ("IO", M sig1_IO),
          ("TextIO", M sig1_TEXT_IO),
          ("BinIO", M sig1_BIN_IO),
          ("General", M sig1_GENERAL),
          ("Cont", M sig1_CONT)]
      
      val sig2_BOOL = [("bool", T), ("not", E 0)]
      
      val sig2_INTEGER =
         [("int", T),
          ("minInt", E 0),
          ("maxInt", E 0),
          ("~", E 0),
          ("+", E 0),
          ("-", E 0),
          ("*", E 0),
          ("div", E 0),
          ("mod", E 0),
          ("min", E 0),
          ("max", E 0),
          ("abs", E 0),
          ("=", E 0),
          ("<>", E 0),
          ("<", E 0),
          (">", E 0),
          ("<=", E 0),
          (">=", E 0),
          ("compare", E 0),
          ("toString", E 0),
          ("fromInt", E 0),
          ("toInt", E 0)]
      
      val sig2_INT_INF =
         [("int", T),
          ("minInt", E 0),
          ("maxInt", E 0),
          ("~", E 0),
          ("+", E 0),
          ("-", E 0),
          ("*", E 0),
          ("div", E 0),
          ("rem", E 0),
          ("min", E 0),
          ("max", E 0),
          ("abs", E 0),
          ("=", E 0),
          ("<>", E 0),
          ("<", E 0),
          (">", E 0),
          ("<=", E 0),
          (">=", E 0),
          ("compare", E 0),
          ("toString", E 0),
          ("fromInt", E 0),
          ("toInt", E 0),
          ("pow", E 0),
          ("log2", E 0),
          ("orb", E 0),
          ("xorb", E 0),
          ("andb", E 0),
          ("notb", E 0),
          ("<<", E 0),
          ("~>>", E 0)]
      
      val sig2_WORD =
         [("word", T),
          ("wordSize", E 0),
          ("toLargeWord", E 0),
          ("toLargeWordX", E 0),
          ("fromLargeWord", E 0),
          ("toInt", E 0),
          ("toIntX", E 0),
          ("fromInt", E 0),
          ("toLargeInt", E 0),
          ("toLargeIntX", E 0),
          ("fromLargeInt", E 0),
          ("andb", E 0),
          ("orb", E 0),
          ("xorb", E 0),
          ("notb", E 0),
          ("<<", E 0),
          (">>", E 0),
          ("~>>", E 0),
          ("+", E 0),
          ("-", E 0),
          ("*", E 0),
          ("div", E 0),
          ("mod", E 0),
          ("=", E 0),
          ("<>", E 0),
          ("<", E 0),
          (">", E 0),
          ("<=", E 0),
          (">=", E 0),
          ("compare", E 0),
          ("toString", E 0)]
      
      val sig2_STRING =
         [("string", T),
          ("size", E 0),
          ("sub", E 0),
          ("substring", E 0),
          ("extract", E 0),
          ("^", E 0),
          ("concat", E 0),
          ("concatWith", E 0),
          ("str", E 0),
          ("implode", E 0),
          ("explode", E 0),
          ("map", E 0),
          ("<", E 0),
          ("<=", E 0),
          (">", E 0),
          (">=", E 0),
          ("compare", E 0),
          ("fields", E 0)]
      
      val sig2_CHAR =
         [("char", T),
          ("ord", E 0),
          ("chr", E 0),
          ("<", E 0),
          (">", E 0),
          ("<=", E 0),
          (">=", E 0),
          ("compare", E 0)]
      
      val sig2_LIST =
         [("list", T),
          ("null", E 0),
          ("length", E 0),
          ("hd", E 0),
          ("tl", E 0),
          ("nth", E 0),
          ("take", E 0),
          ("drop", E 0),
          ("last", E 0),
          ("@", E 0),
          ("rev", E 0),
          ("revAppend", E 0),
          ("foldl", E 0),
          ("foldr", E 0),
          ("map", E 0),
          ("mapPartial", E 0),
          ("app", E 0),
          ("find", E 0),
          ("filter", E 0),
          ("exists", E 0),
          ("all", E 0),
          ("tabulate", E 0)]
      
      val sig2_LIST_PAIR =
         [("UnequalLengths", E 0),
          ("zip", E 0),
          ("zipEq", E 0),
          ("unzip", E 0),
          ("app", E 0),
          ("appEq", E 0),
          ("map", E 0),
          ("mapEq", E 0),
          ("foldl", E 0),
          ("foldr", E 0),
          ("foldlEq", E 0),
          ("foldrEq", E 0),
          ("all", E 0),
          ("exists", E 0),
          ("allEq", E 0)]
      
      val sig2_OPTION =
         [("option", T),
          ("getOpt", E 0),
          ("isSome", E 0),
          ("valOf", E 0),
          ("join", E 0),
          ("map", E 0),
          ("mapPartial", E 0),
          ("app", E 0)]
      
      val sig2_ARRAY =
         [("array", T),
          ("array", E 0),
          ("fromList", E 0),
          ("tabulate", E 0),
          ("length", E 0),
          ("sub", E 0),
          ("update", E 0),
          ("foldl", E 0),
          ("foldli", E 0),
          ("foldr", E 0),
          ("foldri", E 0),
          ("app", E 0),
          ("appi", E 0)]
      
      val sig2_VECTOR =
         [("vector", T),
          ("fromList", E 0),
          ("tabulate", E 0),
          ("length", E 0),
          ("sub", E 0),
          ("foldl", E 0),
          ("foldli", E 0),
          ("foldr", E 0),
          ("foldri", E 0),
          ("app", E 0),
          ("appi", E 0)]
      
      val sig2_MONO_ARRAY =
         [("elem", T),
          ("array", T),
          ("array", E 0),
          ("fromList", E 0),
          ("tabulate", E 0),
          ("length", E 0),
          ("sub", E 0),
          ("update", E 0),
          ("foldl", E 0),
          ("foldli", E 0),
          ("foldr", E 0),
          ("foldri", E 0),
          ("app", E 0),
          ("appi", E 0)]
      
      val sig2_MONO_ARRAY_SLICE =
         [("elem", T),
          ("array", T),
          ("slice", T),
          ("full", E 0),
          ("slice", E 0),
          ("subslice", E 0),
          ("base", E 0),
          ("length", E 0),
          ("sub", E 0),
          ("update", E 0),
          ("foldl", E 0),
          ("foldli", E 0),
          ("foldr", E 0),
          ("foldri", E 0),
          ("app", E 0),
          ("appi", E 0)]
      
      val sig2_IO = [("ioerr", T), ("Io", E 1)]
      
      val sig2_TEXT_IO =
         [("instream", T),
          ("outstream", T),
          ("input1", E 0),
          ("inputN", E 0),
          ("inputLine", E 0),
          ("output1", E 0),
          ("output", E 0),
          ("flushOut", E 0),
          ("openIn", E 0),
          ("closeIn", E 0),
          ("openOut", E 0),
          ("openAppend", E 0),
          ("closeOut", E 0),
          ("stdIn", E 0),
          ("stdOut", E 0),
          ("stdErr", E 0),
          ("print", E 0)]
      
      val sig2_BIN_IO =
         [("instream", T),
          ("outstream", T),
          ("input1", E 0),
          ("output1", E 0),
          ("flushOut", E 0),
          ("openIn", E 0),
          ("closeIn", E 0),
          ("openOut", E 0),
          ("openAppend", E 0),
          ("closeOut", E 0)]
      
      val sig2_GENERAL =
         [("order", T),
          ("exn", T),
          ("unit", T),
          ("LESS", E 0),
          ("EQUAL", E 0),
          ("GREATER", E 0),
          ("Div", E 0),
          ("Fail", E 1),
          ("Subscript", E 0),
          ("Invalid", E 1),
          ("!", E 0),
          (":=", E 0),
          ("o", E 0)]
      
      val basis2 =
         [("BOOL", S sig2_BOOL),
          ("INTEGER", S sig2_INTEGER),
          ("INT_INF", S sig2_INT_INF),
          ("WORD", S sig2_WORD),
          ("STRING", S sig2_STRING),
          ("CHAR", S sig2_CHAR),
          ("LIST", S sig2_LIST),
          ("LIST_PAIR", S sig2_LIST_PAIR),
          ("OPTION", S sig2_OPTION),
          ("ARRAY", S sig2_ARRAY),
          ("VECTOR", S sig2_VECTOR),
          ("MONO_ARRAY", S sig2_MONO_ARRAY),
          ("MONO_ARRAY_SLICE", S sig2_MONO_ARRAY_SLICE),
          ("IO", S sig2_IO),
          ("TEXT_IO", S sig2_TEXT_IO),
          ("BIN_IO", S sig2_BIN_IO),
          ("GENERAL", S sig2_GENERAL),
          ("Bool", M sig2_BOOL),
          ("Int", M sig2_INTEGER),
          ("IntInf", M sig2_INT_INF),
          ("Word", M sig2_WORD),
          ("LargeWord", M sig2_WORD),
          ("Word8", M sig2_WORD),
          ("Word32", M sig2_WORD),
          ("Word64", M sig2_WORD),
          ("String", M sig2_STRING),
          ("Char", M sig2_CHAR),
          ("List", M sig2_LIST),
          ("ListPair", M sig2_LIST_PAIR),
          ("Option", M sig2_OPTION),
          ("Array", M sig2_ARRAY),
          ("Vector", M sig2_VECTOR),
          ("Word8Array", M sig2_MONO_ARRAY),
          ("Word8ArraySlice", M sig2_MONO_ARRAY_SLICE),
          ("IO", M sig2_IO),
          ("TextIO", M sig2_TEXT_IO),
          ("BinIO", M sig2_BIN_IO),
          ("General", M sig2_GENERAL)]
      
   end
