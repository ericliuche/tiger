structure Env =
struct
  datatype envEntry = VarEntry of {ty: Types.ty}
                    | FunEntry of {formals:Types.ty list, result: Types.ty}
  val baseTenv : Types.ty Symbol.table =
    Symbol.initTable([
        (Symbol.symbol("string"), Types.STRING),
        (Symbol.symbol("int"), Types.INT),
        (Symbol.symbol("nil"), Types.NIL)
    ])

  val baseVenv : envEntry Symbol.table = Symbol.empty
end

