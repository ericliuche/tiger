structure Types =
struct

  type unique = unit ref

  datatype ty = 
            RECORD of (Symbol.symbol * ty) list * unique
          | NIL
          | INT
          | BREAK
          | STRING
          | ARRAY of ty * unique
    | NAME of Symbol.symbol * ty option ref
    | UNIT

  fun typeToString t =
    case t of
      INT => "integer"
    | STRING => "string"
    | NIL => "nil"
    | UNIT => "unit"
    | RECORD(symTyList, _) =>
        "{" ^ (String.concatWith ", "
        (map (fn (sym, t) => ((Symbol.name sym) ^ ":" ^ (typeToString t))) symTyList))  ^
        "}"
    | ARRAY(ty, _) => "array of " ^ (typeToString ty)
    | NAME(sym, ty) => Symbol.name(sym)

end

