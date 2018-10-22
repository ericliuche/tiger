structure Env =
struct

  structure S = Symbol
  structure T = Types

  datatype envEntry = VarEntry of {ty: T.ty, readOnly:bool}
                    | FunEntry of {formals:T.ty list, result: T.ty}

  fun fe(f, r) = FunEntry{formals=f, result=r}

  val baseTenv : T.ty Symbol.table =
    S.initTable([
        (S.symbol("string"), T.STRING),
        (S.symbol("int"),    T.INT),
        (S.symbol("nil"),    T.NIL)
    ])

  val baseVenv : envEntry Symbol.table =
    S.initTable([
        (S.symbol("chr"),       fe([T.INT], T.STRING)),
        (S.symbol("concat"),    fe([T.STRING, T.STRING], T.STRING)),
        (S.symbol("exit"),      fe([T.INT], T.UNIT)),
        (S.symbol("flush"),     fe([], T.UNIT)),
        (S.symbol("getchar"),   fe([], T.STRING)),
        (S.symbol("print"),     fe([T.STRING],T.UNIT)),
        (S.symbol("not"),       fe([T.INT], T.UNIT)),
        (S.symbol("ord"),       fe([T.STRING], T.INT)),
        (S.symbol("size"),      fe([T.STRING], T.INT)),
        (S.symbol("substring"), fe([T.STRING, T.INT, T.INT], T.STRING))
    ])
end

