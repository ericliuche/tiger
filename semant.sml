structure Semant: sig val transProg : Absyn.exp -> Types.ty end =
struct

  structure A = Absyn
  structure S = Symbol
  structure T = Types


  fun checkInt({exp, ty}, pos) =
    case ty of
      T.INT => ()
    | actual => ErrorMsg.error pos ("Expected int, got " ^ (T.typeToString actual))

  fun checkCompOpTypes({exp=_, ty=tyLeft}, {exp=_, ty=tyRight}, pos) =
    case (tyLeft, tyRight) of
      ((T.INT, T.INT) | (T.STRING, T.STRING)) => ()
    | (actualLeft, actualRight) => ErrorMsg.error pos
        ("Expected (int, int) or (string, string), got (" ^ (T.typeToString actualLeft) ^
        ", " ^ (T.typeToString(actualRight)) ^ ")")

  fun transExp(venv, tenv) =
    let
      fun trexp(A.IntExp(intVal)) =
            {exp=(), ty=T.INT}
        
      | trexp(A.StringExp(stringVal, pos)) =
          {exp=(), ty=T.STRING}
        
      | trexp(A.OpExp{left, oper, right, pos}) =
          (case oper of
            (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp) =>
              (checkInt(trexp left, pos);
               checkInt(trexp right, pos);
               {exp=(), ty=T.INT})
          | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) =>
              (checkCompOpTypes((trexp left), (trexp right), pos);
              {exp=(), ty=T.INT}))

          (* TODO: equal and not equal operators *)
      
      | trexp(A.SeqExp(expPosList)) =
          let val typeList = map (fn (exp, _) => trexp exp) expPosList
          in
            if typeList = nil then {exp=(), ty=T.UNIT} else (List.last typeList)
          end
      
      | trexp(_) = {exp=(), ty=T.UNIT}

      in trexp
    end


  fun transProg ast =
    let val {exp=_, ty=topLevelType} = (transExp (nil, nil) ast)
    in topLevelType
    end

end