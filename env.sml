structure Env =
struct
  datatype envEntry = VarEntry of {ty: Types.ty}
                    | FunEntry of {formals:Types.ty list, result: Types.ty}
  val baseTenv : Types.ty Symbol.table = Symbol.empty
  val baseVenv : envEntry Symbol.table = Symbol.empty
end

