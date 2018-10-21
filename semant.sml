structure Semant: sig val transProg : Absyn.exp -> Types.ty end =
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types

  (* The result type of transforming and type-checking an expression *)
  type expty = {exp: unit, ty: T.ty}


  (* Produces an error if the given expty is not an integer *)
  fun checkInt({exp, ty}, pos) =
    case ty of
      T.INT => ()
    | actual => ErrorMsg.error pos ("Expected int, got " ^ (T.typeToString actual))

  (* Produces an error if the given exptys cannot be used in a comparison operator *)
  fun checkCompOpTypes({exp=_, ty=tyLeft}, {exp=_, ty=tyRight}, pos) =
    case (tyLeft, tyRight) of
      ((T.INT, T.INT) | (T.STRING, T.STRING)) => ()
    | (actualLeft, actualRight) => ErrorMsg.error pos
        ("Expected (int, int) or (string, string), got (" ^ (T.typeToString actualLeft) ^
        ", " ^ (T.typeToString(actualRight)) ^ ")")

  (*
    Produces an error if the variable type and the type of its initialization expression
    are not legal
  *)
  fun checkVarDecTypes(SOME({exp=_, ty=delcaredType}), {exp=_, ty=inferredType}, pos) = 
        if delcaredType <> inferredType then 
          ErrorMsg.error pos ("Expected " ^ T.typeToString(delcaredType) ^ ", got " ^ T.typeToString(inferredType))
        else
          ()

    | checkVarDecTypes(NONE, {exp=_, ty=inferredType}, pos) =
        if inferredType = T.NIL then ErrorMsg.error pos ("Unable to infer type") else ()

  (*
    Produces an error if the declared and actual types disagree and returns the declared type
    if it is present or the actual type otherwise
  *)
  fun checkDeclaredType(SOME(declared), actual, pos) =
        if declared <> actual then
          (ErrorMsg.error pos ("Mismatch between declared and actual types - Expected " ^
            T.typeToString(declared) ^ ", got " ^ T.typeToString(actual));
          T.UNIT)
        else
          declared

    | checkDeclaredType(NONE, actual, pos) =
        actual

  (*
    Produces an error if the function call is passed the wrong number or wrong type
    of parameters
  *)
  fun checkArgumentTypes(paramTypeList, argTypeList, pos) =
    let
      val numArgs = length(argTypeList)
      val numParams = length(paramTypeList)

      fun checkArgTypes(params, args) =
        ListPair.all (fn (paramType, argType) => (paramType = argType)) (params, args)
    in
      if numParams <> numArgs then
        ErrorMsg.error pos ("Expected " ^ Int.toString(numParams) ^ " arguments, got "
          ^ Int.toString(numArgs))
      else
        if not (checkArgTypes(paramTypeList, argTypeList)) then
          ErrorMsg.error pos "Unexpected argument types"
      else
        ()
    end

  (*
    Produces an error if the given symbol is not in the given table and returns an
    option of the table value
  *)
  fun lookupSymbol(table, symbol, pos) = 
    let val symbolVal = S.look(table, symbol)
    in
      ((if not (isSome symbolVal) then 
        ErrorMsg.error pos ("Undefined symbol " ^ S.name(symbol))
      else
        ());
      symbolVal)
    end

  (*
    Transforms and type-checks an Absyn.Ty in the given type environment
  *)
  fun transTy(tenv, absynTy) =
    case absynTy of
      A.NameTy(sym, pos) =>
        Option.getOpt(lookupSymbol(tenv, sym, pos), T.UNIT)

    | A.ArrayTy(sym, pos) =>
        T.ARRAY(Option.getOpt(lookupSymbol(tenv, sym, pos), T.UNIT), ref ())

    | A.RecordTy(fieldList) =>
        T.RECORD(
          map
            (fn ({name, escape, typ, pos}) =>
              (name, Option.getOpt(lookupSymbol(tenv, typ, pos), T.UNIT)))
            (fieldList),
          ref ())


  (*
    Transforms and type-checks a function declaration in the given environments
  *)
  fun transFuncDec(venv, tenv, {name, params, result, body, pos}) =
    let
      fun getParamTypes({name, escape, typ, pos}) = (name, Option.getOpt(lookupSymbol(tenv, typ, pos), T.UNIT))
      val params' = map getParamTypes params
      val formals = map (fn (name, ty) => ty) params'

      fun addParamToBodyVenv((name, ty), curVenv) = S.enter(curVenv, name, E.VarEntry{ty=ty})
      val bodyVenv = foldl addParamToBodyVenv venv params'

      val {exp=_, ty=bodyTy} = transExp (bodyVenv, tenv) body

      val returnType = checkDeclaredType(
        Option.mapPartial (fn (symbol, pos) => lookupSymbol(tenv, symbol, pos)) (result),
        bodyTy,
        pos)
    in
      {venv=S.enter(venv, name, E.FunEntry{formals=formals, result=returnType}), tenv=tenv}
    end

  (*
    Transforms and type-checks a declaration in the given environments
  *)
  and transDec(venv, tenv, dec) = 
    case dec of 
       A.VarDec{name, escape, typ, init, pos} =>
        let
          val {exp=_, ty=inferredTy} = transExp(venv, tenv) init

          val declaredTyOpt =
            Option.mapPartial
              (fn (typSym, typPos) => lookupSymbol(tenv, typSym, typPos))
              (typ)

          val variableType = checkDeclaredType(declaredTyOpt, inferredTy, pos)

        in
          (case (declaredTyOpt, inferredTy) of
            (NONE, T.NIL) => ErrorMsg.error pos "Unknown type of nil variable"
          |  _ => ();

          {venv=S.enter(venv, name, E.VarEntry{ty=variableType}), tenv=tenv})
        end

    | A.TypeDec(decList) =>
        {venv=venv, tenv= foldl
          (fn ({name, ty, pos}, curTenv) => S.enter(curTenv, name, transTy(curTenv, ty)))
          (tenv)
          (decList)}

    | A.FunctionDec(decList) =>
        foldl
          (fn (functionDec, {venv, tenv}) => transFuncDec(venv, tenv, functionDec))
          ({venv=venv, tenv=tenv})
          (decList)


  (*
    Produces a transformation function which type-checks an expression with the given
    environments
  *)
  and transExp(venv, tenv) =
    let
      fun trexp(A.IntExp(intVal)) =
            {exp=(), ty=T.INT}
        
      | trexp(A.StringExp(stringVal, pos)) =
          {exp=(), ty=T.STRING}

      | trexp(A.NilExp) =
          {exp=(), ty=T.NIL}
        
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

      | trexp(A.VarExp(var)) =
          (case var of
            A.SimpleVar(sym, pos) =>
              let
                val venvEntry = lookupSymbol(venv, sym, pos)
              in
                (case venvEntry of
                  SOME(E.VarEntry{ty=ty}) => {exp=(), ty=ty}
                | _ => {exp=(), ty=T.UNIT})
              end

          | _ => {exp=(), ty=T.UNIT})

      | trexp(A.CallExp{func, args, pos}) =
          let
            val funcEntry = Option.getOpt(lookupSymbol(venv, func, pos), E.VarEntry{ty=T.UNIT})
            val {formals=paramTypes, result=resultType} =
              case funcEntry of
                E.FunEntry{formals, result} => {formals=formals, result=result}
              | E.VarEntry{ty} => {formals=[], result=T.UNIT} 

            val argExptys = map trexp args
            val argTypes = map (fn ({exp, ty}) => ty) argExptys
          in
            (checkArgumentTypes(paramTypes, argTypes, pos);
            {exp=(), ty=resultType})
          end

      | trexp(_) = {exp=(), ty=T.UNIT}

      in trexp
    end


  (* Translates and type-checks an abstract syntax tree *)
  fun transProg ast =
    let 
      val venv = E.baseVenv
      val tenv = E.baseTenv
      val {exp=_, ty=topLevelType} = (transExp (venv, tenv) ast)
    in topLevelType
    end

end