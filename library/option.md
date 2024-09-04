open:Option
# `Option`

Options are defined:

    datatype
      intersect (i : level) .
      intermediate (a : U i) .
      U i
    of
      option : type =
      | None : option
      | Some : a -> option

Producing:

    option : type:option

    None : type:None

    Some : type:Some

The iterator for options:

    option_iter : type:option_iter

    option_iter a P z s (None _) --> z
    option_iter a P z s (Some _ x) --> s x

A simpler case-analysis operation:

    option_case : type:option_case
                = def:option_case
                imp:option_case

    option_case None n _ --> n
    option_case Some x _ s --> s x

Options are covariant:

    option_subtype : type:option_subtype


### Operations

    bind : type:bind
         = def:bind
         imp:bind

    bind None _ --> None
    bind (Some x) f --> f x


    join : type:join
         = def:join
         imp:join

    join None --> None
    join (Some l) --> l


    map : type:map
         = def:map
         imp:map

    map None _ --> None
    map (Some x) f --> Some (f x)


    valof : type:valof
         = def:valof
         imp:valof

    valof None x --> x
    valof (Some x) y --> x
