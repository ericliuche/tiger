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

  (* TODO: Implement Join *)

  fun isSubtype(NIL, RECORD(_)) = true
    | isSubtype(ARRAY(_, u1), ARRAY(_, u2)) = (u1 = u2)
    | isSubtype(RECORD(r1), RECORD(r2)) = (r1 = r2)
    | isSubtype(BREAK, _) = true
    | isSubtype(NAME(sym, tyRef), ty) =
      (case !tyRef of
           NONE => false
         | SOME(tyRef) => isSubtype(tyRef, ty))
    | isSubtype(ty, NAME(sym, tyRef)) = 
      (case !tyRef of
           NONE => false
         | SOME(tyRef) => isSubtype(ty, tyRef))
    | isSubtype(t1, t2) = t1 = t2

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
    | BREAK => "break"

end

