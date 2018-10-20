structure Semant: sig val transProg : Absyn.exp -> Types.ty end =
struct

  structure A = Absyn
  structure E = Env
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

  fun checkVarDecTypes(SOME({exp=_, ty=delcaredType}), {exp=_, ty=inferredType}, pos) = 
    if delcaredType != inferredType then 
      ErrorMsg.error pos ("Expected " ^ T.typeToString(delcaredType) ^ ", got " ^ T.typeToString(inferredType))
    else
      ()
    | checkVarDecTypes(NONE, {exp=_, ty=inferredType}, pos) =
      if inferredType = T.NIL then 
        ErrorMsg.error pos ("Unable to infer type")
      else
        ()

  fun lookupSymbol(table, symbol, pos) = 
    let val symbolVal = S.look(table, symbol)
    in
      ((if not (isSome symbolVal) then 
        ErrorMsg.error pos ("Undefined symbol " ^ S.name(symbol))
      else
        ());
      symbolVal)
    end

  fun transDec(venv, tenv, dec) = 
    case dec of 
       Absyn.VarDec{name, escape, typ, init, pos} =>
        let 
          val declaredTyp = case typ of 
            SOME(typSym, typPos) => 
              map 
                (fn (ty) => {exp=(), ty=ty}) 
                (lookupSymbol(venv, typSym, typPos))
          | NONE => NONE
        in
          (checkVarDecTypes(declaredTyp, transExp(venv, tenv) init, pos);
          {venv=S.enter(venv, name, typ), tenv=tenv})
        end

  and transExp(venv, tenv) =
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

      | trexp(A.LetExp{decs, body, pos}) = 
          let val {venv=venv, tenv=tenv} = 
            foldl 
              (fn (dec, {venv=curVenv, tenv=curTenv}) => transDec(curVenv, curTenv, dec))
              ({venv=venv, tenv=tenv})
              (decs)
          in 
            transExp(venv, tenv) body
          end

      | trexp(_) = {exp=(), ty=T.UNIT}

      in trexp
    end


  fun transProg ast =
    let 
      val venv = E.baseVenv
      val tenv = E.baseTenv
      val {exp=_, ty=topLevelType} = (transExp (venv, tenv) ast)
    in topLevelType
    end

end