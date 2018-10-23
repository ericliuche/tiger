structure Semant: sig val transProg : Absyn.exp -> Types.ty end =
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types

  (* The result type of transforming and type-checking an expression *)
  type expty = {exp: unit, ty: T.ty}

  (* Produces an error if the given expty is not an integer *)
  fun checkInt(message, {exp, ty}, pos) =
    if T.isSubtype(ty, T.INT) then
      ()
    else
      ErrorMsg.error pos (message ^ "Expected int, got " ^ (T.typeToString ty))

  (* Produces an error if the given expty is not unit type *)
  fun checkUnit(message, {exp, ty}, pos) =
    if T.isSubtype(ty, T.UNIT) then
      ()
    else
      ErrorMsg.error pos (message ^ "Expected unit, got " ^ (T.typeToString ty))

  (* Produces an error if the given exptys cannot be used in a comparison operator *)
  fun checkCompOpTypes({exp=_, ty=tyLeft}, {exp=_, ty=tyRight}, pos) =
    case (tyLeft, tyRight) of
      ((T.INT, T.INT) | (T.STRING, T.STRING)) => ()
    | (actualLeft, actualRight) => ErrorMsg.error pos
        ("Expected (int, int) or (string, string), got (" ^ (T.typeToString actualLeft) ^
        ", " ^ (T.typeToString(actualRight)) ^ ")")

  (* Produces an error if the given exptys cannot be used in an equality comparison *)
  fun checkEqualOpTypes({exp=_, ty=tyLeft}, {exp=_, ty=tyRight}, pos) =
    case (T.isSubtype(tyLeft, tyRight), T.isSubtype(tyRight, tyLeft)) of
      (false, false) =>
        ErrorMsg.error pos ("Cannot compare equality for types " ^
          T.typeToString(tyLeft) ^ " and " ^ T.typeToString(tyRight))
    | _ => ()

  (* Produces an error if the given expression cannot be assigned to the given variable *)
  fun checkAssignmentTypes({exp=_, ty=varTy}, {exp=_, ty=expTy}, pos) =
    if not (T.isSubtype(expTy, varTy)) then
      ErrorMsg.error pos ("Invalid assignment to type " ^ T.typeToString(varTy))
    else
      ()

  (*
    Produces an error if the variable type and the type of its initialization expression
    are not legal
  *)
  fun checkVarDecTypes(SOME({exp=_, ty=declaredType}), {exp=_, ty=inferredType}, pos) = 
        if not(T.isSubtype(inferredType, declaredType)) then 
          ErrorMsg.error pos ("Expected " ^ T.typeToString(declaredType) ^ ", got " ^ T.typeToString(inferredType))
        else
          ()

    | checkVarDecTypes(NONE, {exp=_, ty=inferredType}, pos) =
        if inferredType = T.NIL then ErrorMsg.error pos ("Unable to infer type") else ()

  (*
    Produces an error if the declared and actual types disagree and returns the declared type
    if it is present or the actual type otherwise
  *)
  fun checkDeclaredType(SOME(declared), actual, pos) =
        if not(T.isSubtype(actual, declared)) then
          (ErrorMsg.error pos ("Mismatch between declared and actual types - Expected " ^
            T.typeToString(declared) ^ ", got " ^ T.typeToString(actual));
          T.UNIT)
        else
          declared

    | checkDeclaredType(NONE, actual, pos) =
        actual

  (*
    Produces an error if the two branches do not have compatible types
  *)
  fun checkIfThenElseTypes(consTy, antTy, pos) =
    if not(T.isSubtype(consTy, antTy)) andalso not(T.isSubtype(antTy, consTy)) then
      ErrorMsg.error pos "Mismatch between if-then-else branch types"
    else
      ()

  (*
    Produces an error if the given list of types is not compatible with the given list
    of actual types. 
  *)
  fun checkTypeList(expectedList, actualList) =
    ListPair.allEq (fn (expected, actual) => (T.isSubtype(actual, expected))) (expectedList, actualList)

  (*
    Produces an error if the function call is passed the wrong number or wrong type
    of parameters
  *)
  fun checkArgumentTypes(paramTypeList, argTypeList, pos) =
    let
      val numArgs = length(argTypeList)
      val numParams = length(paramTypeList)

    in
      if numParams <> numArgs then
        ErrorMsg.error pos ("Expected " ^ Int.toString(numParams) ^ " arguments, got "
          ^ Int.toString(numArgs))
      else
        if not (checkTypeList(paramTypeList, argTypeList)) then
          ErrorMsg.error pos "Unexpected argument types"
      else
        ()
    end

  (*
    Produces an error if the given record expression does not conform to the record type
    which it is declared to be
  *)
  fun checkRecordType(T.RECORD(typeFields, unique), recordFields, pos) =
        let
          val typeFieldLength = length(typeFields)
          val recordFieldLength = length(recordFields)

          fun getTy(sym, ty) = ty
          fun getName(sym, ty) = sym

          val expectedTypes = map getTy typeFields
          val actualTypes = map getTy recordFields

          val expectedNames = map getName typeFields
          val actualNames = map getName recordFields

          fun sameFieldNames(typeFieldNames, recordFieldNames) =
            ListPair.all
              (fn (typeFieldName: S.symbol, recordFieldName: S.symbol) => (typeFieldName = recordFieldName))
              (typeFieldNames, recordFieldNames)

        in
          if typeFieldLength <> recordFieldLength then
            ErrorMsg.error pos ("Expected " ^ Int.toString(typeFieldLength) ^ " fields, got " ^
              Int.toString(recordFieldLength))
          else if not (checkTypeList(expectedTypes, actualTypes)) then
              ErrorMsg.error pos ("Record field type mismatch")
          else if not (sameFieldNames(expectedNames, actualNames)) then
              ErrorMsg.error pos ("Record field name mismatch")
          else
            ()
        end

    | checkRecordType(actualType, recordFields, pos) =
        ErrorMsg.error pos ("Cannot assign a record to type " ^ T.typeToString(actualType))

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
    Traverses the name alias chain and returns the underlying type definition for
    the given type
  *)
  fun actualType(tenv, ty) =
    case ty of
      T.NAME(sym, tyRef) => actualType(tenv, Option.getOpt(!tyRef, T.UNIT))
    | _ => ty

  (* 
    Produces an error is var is not writable 
  *)
  fun checkWritable(venv, A.SimpleVar(symbol, pos)) = 
        (case lookupSymbol(venv, symbol, pos) of
          SOME(E.VarEntry{ty, readOnly=true}) => 
            ErrorMsg.error pos ("Unable to assign to read only variable " ^ S.name(symbol))
        | _ => ())
    | checkWritable(venv, _) = ()


  (* Produces an error if the given type environment has cyclical definitions *)
  fun checkEnvCycles({venv, tenv}, names, pos) =
    let

      fun cycle(tenv, T.NAME(sym, tyRef), seen) =
            (case !tyRef of
              SOME(ty) => (S.contains(seen, sym)) orelse (cycle(tenv, ty, S.enter(seen, sym, true)))
            | NONE => true)
        | cycle(tenv, _, seen) = false

      val foundCycle = foldl
        (fn (ty, foundCycle) => foundCycle orelse (cycle(tenv, ty, S.empty)))
        (false)
        (names)
    in
      if foundCycle then ErrorMsg.error pos "Found cyclical type definition" else ()
    end


  (*
    Transforms and type-checks an Absyn.Ty in the given type environment
  *)
  fun transTy(tenv, absynTy) =
    case absynTy of
      A.NameTy(sym, pos) =>
        Option.getOpt(lookupSymbol(tenv, sym, pos), T.UNIT)

    | A.ArrayTy(sym, pos) =>
        T.ARRAY(actualType(tenv, Option.getOpt(lookupSymbol(tenv, sym, pos), T.UNIT)), ref ())

    | A.RecordTy(fieldList) =>
        T.RECORD(
          map
            (fn ({name, escape, typ, pos}) =>
              (name, Option.getOpt(lookupSymbol(tenv, typ, pos), T.UNIT)))
            (fieldList),
          ref ())

  (*
    Transforms and type-checks a variable
  *)
  fun transVar(venv, tenv, var, inLoop) : expty =
    case var of
      A.SimpleVar(sym, pos) =>
        (case lookupSymbol(venv, sym, pos) of
          SOME(E.VarEntry{ty, readOnly}) => {exp=(), ty=actualType(tenv, ty)}
        | _ => {exp=(), ty=T.UNIT})

    | A.FieldVar(var, sym, pos) =>
        (case transVar(venv, tenv, var, inLoop) of
          {exp=_, ty=T.RECORD(fieldList, unique)} =>
            let
              fun getFieldType((fieldName, fieldType) :: tail) =
                    if fieldName = sym then
                      {exp=(), ty=actualType(tenv, fieldType)}
                    else
                      getFieldType(tail)

                | getFieldType(nil) = (
                  ErrorMsg.error pos ("Field " ^ S.name(sym) ^ " does not exist");
                  {exp=(), ty=T.UNIT})
            in
              getFieldType(fieldList)
            end

        | _ => (
          ErrorMsg.error pos (S.name(sym) ^ " is not a record type");
          {exp=(), ty=T.UNIT}))

    | A.SubscriptVar(var, exp, pos) =>
        (checkInt("Array index: ", transExp(venv, tenv, inLoop) exp, pos);
        case transVar(venv, tenv, var, inLoop) of
          {exp=_, ty=T.ARRAY(ty, unique)} => {exp=(), ty=actualType(tenv, ty)}
        | _ => (
          ErrorMsg.error pos "Cannot subscript a non-array type";
          {exp=(), ty=T.UNIT}))


  (*
    Transforms and type-checks a function declaration in the given environments
  *)
  and transFuncDec(venv, tenv, {name, params, result, body, pos}, inLoop) =
    let
      fun getParamTypes({name, escape, typ, pos}) = (name, Option.getOpt(lookupSymbol(tenv, typ, pos), T.UNIT))
      val params' = map getParamTypes params
      val formals = map (fn (name, ty) => ty) params'

      fun addParamToBodyVenv((name, ty), curVenv) = S.enter(curVenv, name, E.VarEntry{ty=ty, readOnly=false})
      val bodyVenv = foldl addParamToBodyVenv venv params'

      val {exp=_, ty=bodyTy} = transExp (bodyVenv, tenv, inLoop) body

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
  and transDec(venv, tenv, dec, inLoop) = 
    case dec of 
       A.VarDec{name, escape, typ, init, pos} =>
        let
          val {exp=_, ty=inferredTy} = transExp(venv, tenv, inLoop) init

          val declaredTyOpt =
            Option.mapPartial
              (fn (typSym, typPos) => lookupSymbol(tenv, typSym, typPos))
              (typ)

          val variableType = checkDeclaredType(declaredTyOpt, inferredTy, pos)

        in
          (case (declaredTyOpt, inferredTy) of
            (NONE, T.NIL) => ErrorMsg.error pos "Unknown type of nil variable"
          |  _ => ();
          {venv=S.enter(venv, name, E.VarEntry{ty=variableType, readOnly=false}), tenv=tenv})
        end

    | A.TypeDec(decList) =>
        let

          (* Build environment with empty name types *)
          val names = map (fn ({name, ty, pos}) => T.NAME(name, ref NONE)) decList
        
          fun addToNameTenv(name, curTenv) =
            case name of
              T.NAME(tyname, ty) => S.enter(curTenv, tyname, name)
            | _ => curTenv
          
          val nameTenv = foldl addToNameTenv tenv names

          (* Build real environment by resolving actual types for each name *)
          fun addToTenv({name, ty, pos}, curTenv) =
              let
                val tyResult = transTy(nameTenv, ty)
                val nameEnvResult = lookupSymbol(nameTenv, name, pos)
              in
                (case nameEnvResult of
                  SOME(T.NAME(sym, tyRef)) => tyRef := SOME(tyResult)
                | _ => ();
                S.enter(curTenv, name, tyResult))
              end

          val {name=_, ty=_, pos=startPos} = hd(decList)
          val env = {venv=venv, tenv= foldl addToTenv tenv decList}
        in
          (checkEnvCycles(env, names, startPos);
          env)
        end

    | A.FunctionDec(decList) =>
        let

          (* Create the type environment with function header information *)
          fun getFormal({name, escape, typ, pos}) = Option.getOpt(lookupSymbol(tenv, typ, pos), T.UNIT)

          fun getHeaderInfo({name, params, result=SOME(result, resultPos), body, pos}) =
                (name, map getFormal params, Option.getOpt(lookupSymbol(tenv, result, resultPos), T.UNIT))
            
            | getHeaderInfo({name, params, result=NONE, body, pos}) =
                (name, map getFormal params, T.UNIT)

          val headers = map getHeaderInfo decList

          fun createHeaderEnv((name, formals, result), curVenv) =
            S.enter(curVenv, name, E.FunEntry{formals=formals, result=result})

          val headerEnv = foldl createHeaderEnv venv headers

          (* Add the functions to the actual environments *)
          fun createEnv(functionDec, {venv, tenv}) = transFuncDec(headerEnv, tenv, functionDec, false)

        in
          foldl createEnv {venv=venv, tenv=tenv} decList
        end


  (*
    Produces a transformation function which type-checks an expression with the given
    environments
  *)
  and transExp(venv, tenv, inLoop) : A.exp -> expty =
    let
      fun trexp(A.IntExp(intVal)) : expty =
            {exp=(), ty=T.INT}
        
      | trexp(A.StringExp(stringVal, pos)) =
          {exp=(), ty=T.STRING}

      | trexp(A.NilExp) =
          {exp=(), ty=T.NIL}

      | trexp(A.ArrayExp{typ, size, init, pos}) =
          let
            val declaredType = lookupSymbol(tenv, typ, pos)
            val arraySubtype = case declaredType of
              SOME(T.ARRAY(ty, unique)) => SOME(ty)
            | nonarray => nonarray

            val {exp=_, ty=initType} = trexp init
          in
            (checkInt("Array size: ", trexp size, pos);
             checkDeclaredType(arraySubtype, initType, pos); 
            {exp=(), ty=Option.getOpt(declaredType, T.UNIT)})
          end
        
      | trexp(A.OpExp{left, oper, right, pos}) =
          (case oper of
            (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp) =>
              (checkInt("", trexp left, pos);
               checkInt("", trexp right, pos);
               {exp=(), ty=T.INT})
          | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) =>
              (checkCompOpTypes((trexp left), (trexp right), pos);
              {exp=(), ty=T.INT})

          | (A.EqOp | A.NeqOp) =>
              (checkEqualOpTypes((trexp left), (trexp right), pos);
               {exp=(), ty=T.INT}))

      | trexp(A.SeqExp(expPosList)) =
          let val typeList = map (fn (exp, _) => trexp exp) expPosList
          in
            if typeList = nil then {exp=(), ty=T.UNIT} else (List.last typeList)
          end

      | trexp(A.LetExp{decs, body, pos}) = 
          let val {venv=venv, tenv=tenv} = 
            foldl 
              (fn (dec, {venv=curVenv, tenv=curTenv}) => transDec(curVenv, curTenv, dec, inLoop))
              ({venv=venv, tenv=tenv})
              (decs)
          in 
            transExp(venv, tenv, inLoop) body
          end

      | trexp(A.VarExp(var)) =
          transVar(venv, tenv, var, inLoop)

      | trexp(A.CallExp{func, args, pos}) =
          let
            val funcEntry = lookupSymbol(venv, func, pos)
            val {formals=paramTypes, result=resultType} =
              case funcEntry of
                SOME(E.FunEntry{formals, result}) => {formals=formals, result=result}
              | _ => (ErrorMsg.error pos "Unable to apply a non-function value";
                     {formals=[], result=T.UNIT})

            val argExptys = map trexp args
            val argTypes = map (fn ({exp, ty}) => ty) argExptys
          in
            (checkArgumentTypes(paramTypes, argTypes, pos);
            {exp=(), ty=resultType})
          end

      | trexp(A.AssignExp{var, exp, pos}) =
          (checkWritable(venv, var);
           checkAssignmentTypes(transVar(venv, tenv, var, inLoop), trexp exp, pos);
          {exp=(), ty=T.UNIT})

      | trexp(A.IfExp{test, then', else'=NONE, pos}) =
          (checkInt("If test expression: ", trexp test, pos);
           checkUnit("If body expression: ", trexp then', pos);
          {exp=(), ty=T.UNIT})

      | trexp(A.IfExp{test, then', else'=SOME(antecedent), pos}) =
          let
            val {exp=_, ty=consTy} = trexp then'
            val {exp=_, ty=antTy} = trexp antecedent
          in
            (checkInt("If test expression: ", trexp test, pos);
             checkIfThenElseTypes(consTy, antTy, pos);
            {exp=(), ty=consTy})
          end

      | trexp(A.ForExp{var, escape, lo, hi, body, pos}) = 
          let 
            val venv' = S.enter(venv, var, E.VarEntry{ty=T.INT, readOnly=true})
          in 
            (checkInt("For lo expression: ", trexp lo, pos);
             checkInt("For hi expression: ", trexp hi, pos);
             checkUnit("For body expression: ", transExp(venv', tenv, true) body, pos);
            {exp=(), ty=T.UNIT})
          end

      | trexp(A.WhileExp{test, body, pos}) = 
          (checkInt("While test expression: ", trexp test, pos);
           checkUnit("While body expression: ", transExp(venv, tenv, true) body, pos);
          {exp=(), ty=T.UNIT})

      | trexp(A.RecordExp{fields=fieldList, typ, pos}) =
          let
            val recordType = actualType(
              tenv,
              Option.getOpt(lookupSymbol(tenv, typ, pos), T.UNIT))

            fun getFieldType(symbol, exp, pos) =
              let val {exp=(), ty=fieldTy} = trexp exp
              in
                (symbol, fieldTy)
              end

            val fieldTypeList = map getFieldType fieldList
          in
            (checkRecordType(recordType, fieldTypeList, pos);
              {exp=(), ty=recordType})
          end

      | trexp(A.BreakExp(pos)) = 
          (if not inLoop then
            ErrorMsg.error pos "Illegal break, must be within a for or while loop"
          else 
            ();
          {exp=(), ty=T.BREAK})

      fun trexpLoop(A.BreakExp(pos)) = {exp=(), ty=T.BREAK}
        | trexpLoop(exp) = trexp(exp)

      in if inLoop then trexpLoop else trexp
    end


  (* Translates and type-checks an abstract syntax tree *)
  fun transProg ast =
    let 
      val venv = E.baseVenv
      val tenv = E.baseTenv
      val {exp=_, ty=topLevelType} = (transExp (venv, tenv, false) ast)
    in topLevelType
    end

end