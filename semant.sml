structure Semant: sig val transProg : Absyn.exp -> unit end =
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types

  (* The result type of transforming and type-checking an expression *)
  type expty = {exp: Translate.exp, ty: T.ty}

  (* Tracks whether the current AST is valid *)
  val legalAst = ref true

  (* Prints the given error message and marks the current AST as illegal *)
  fun error pos = fn msg =>
    (legalAst := false; ErrorMsg.error pos msg)

  (* Produces an error if the given expty is not an integer *)
  fun checkInt(message, {exp, ty}, pos) =
    if T.isSubtype(ty, T.INT) then ()
    else error pos (message ^ "Expected int, got " ^ (T.typeToString ty))

  (* Produces an error if the given expty is not unit type *)
  fun checkUnit(message, {exp, ty}, pos) =
    if T.isSubtype(ty, T.UNIT) then ()
    else error pos (message ^ "Expected unit, got " ^ (T.typeToString ty))

  (* Produces an error if the given exptys cannot be used in a comparison operator *)
  fun checkCompOpTypes({exp=_, ty=tyLeft}, {exp=_, ty=tyRight}, pos) =
    case (tyLeft, tyRight) of
      ((T.INT, T.INT) | (T.STRING, T.STRING)) => ()
    | (actualLeft, actualRight) => error pos
        ("Expected (int, int) or (string, string), got (" ^ (T.typeToString actualLeft) ^
        ", " ^ (T.typeToString(actualRight)) ^ ")")

  (* Produces an error if the given exptys cannot be used in an equality comparison *)
  fun checkEqualOpTypes({exp=_, ty=tyLeft}, {exp=_, ty=tyRight}, pos) =
    case (T.isSubtype(tyLeft, tyRight), T.isSubtype(tyRight, tyLeft)) of
      (false, false) =>
        error pos ("Cannot compare equality for types " ^
          T.typeToString(tyLeft) ^ " and " ^ T.typeToString(tyRight))
    | _ => ()

  (* Produces an error if the given expression cannot be assigned to the given variable *)
  fun checkAssignmentTypes({exp=_, ty=varTy}, {exp=_, ty=expTy}, pos) =
    if not (T.isSubtype(expTy, varTy)) then
      error pos ("Invalid assignment to type " ^ T.typeToString(varTy))
    else ()

  (*
    Produces an error if the variable type and the type of its initialization expression
    are not legal
  *)
  fun checkVarDecTypes(SOME({exp=_, ty=declaredType}), {exp=_, ty=inferredType}, pos) = 
        if not(T.isSubtype(inferredType, declaredType)) then 
          error pos ("Expected " ^ T.typeToString(declaredType) ^
                     ", got " ^ T.typeToString(inferredType))
        else ()

    | checkVarDecTypes(NONE, {exp=_, ty=inferredType}, pos) =
        if inferredType = T.NIL then error pos ("Unable to infer type") else ()

  (*
    Produces an error if the declared and actual types disagree and returns the declared type
    if it is present or the actual type otherwise
  *)
  fun checkDeclaredType(SOME(declared), actual, pos) =
        if not(T.isSubtype(actual, declared)) then
          (error pos ("Mismatch between declared and actual types - Expected " ^
                      T.typeToString(declared) ^ ", got " ^ T.typeToString(actual));
          T.TOP)
        else
          declared

    | checkDeclaredType(NONE, actual, pos) =
        actual

  (*
    Produces an error if the function return type and the body type are incompatible or
    if a procedure has a non-unit type
  *)
  fun checkFunctionDeclaredType(NONE, actual, pos) =
        (checkUnit("Procedure definition: ", {exp=Translate.TODO(), ty=actual}, pos);
        T.UNIT)

    | checkFunctionDeclaredType(declaredOpt, actual, pos) =
        checkDeclaredType(declaredOpt, actual, pos)

  (*
    Produces an error if the two branches do not have compatible types
  *)
  fun checkIfThenElseTypes(consTy, antTy, pos) =
    if not(T.isSubtype(consTy, antTy)) andalso not(T.isSubtype(antTy, consTy)) then
      error pos "Mismatch between if-then-else branch types"
    else ()

  (*
    Produces an error if the given list of types is not compatible with the given list
    of actual types. 
  *)
  fun checkTypeList(expectedList, actualList) =
    ListPair.allEq
      (fn (expected, actual) => (T.isSubtype(actual, expected)))
      (expectedList, actualList)

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
        error pos ("Expected " ^ Int.toString(numParams) ^ " arguments, got " ^
                   Int.toString(numArgs))
      else if not (checkTypeList(paramTypeList, argTypeList)) then
          error pos "Unexpected argument types"
      else ()
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
              (fn (typeFieldName: S.symbol, recordFieldName: S.symbol) =>
                (typeFieldName = recordFieldName))
              (typeFieldNames, recordFieldNames)

        in
          if typeFieldLength <> recordFieldLength then
            error pos ("Expected " ^ Int.toString(typeFieldLength) ^ " fields, got " ^
              Int.toString(recordFieldLength))
          else if not (checkTypeList(expectedTypes, actualTypes)) then
              error pos ("Record field type mismatch")
          else if not (sameFieldNames(expectedNames, actualNames)) then
              error pos ("Record field name mismatch")
          else
            ()
        end

    | checkRecordType(actualType, recordFields, pos) =
        error pos ("Cannot assign a record to type " ^ T.typeToString(actualType))

  (*
    Produces an error if all symbols in the list are not unique
  *)
  fun checkUnique((sym, pos)::rest, seen) =
        if S.contains(seen, sym) then
          error pos ("Illegal duplicate identifier: " ^ (S.name sym))
        else checkUnique(rest, S.enter(seen, sym, true))

    | checkUnique(nil, seen) = ()

  (*
    Produces an error if the given symbol is not in the given table and returns an
    option of the table value
  *)
  fun lookupSymbol(table, symbol, pos) = 
    let val symbolVal = S.look(table, symbol)
    in
      ((if not (isSome symbolVal) then 
        error pos ("Undefined symbol " ^ S.name(symbol))
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
      T.NAME(sym, tyRef) => actualType(tenv, Option.getOpt(!tyRef, T.TOP))
    | _ => ty

  (* 
    Produces an error is var is not writable 
  *)
  fun checkWritable(venv, A.SimpleVar(symbol, pos)) = 
        (case lookupSymbol(venv, symbol, pos) of
          SOME(E.VarEntry{access, ty, readOnly=true}) => 
            error pos ("Unable to assign to read only variable " ^ S.name(symbol))
        | _ => ())
    | checkWritable(venv, _) = ()


  (* Produces an error if the given type environment has cyclical definitions *)
  fun checkEnvCycles({venv, tenv}, names, pos) =
    let

      fun cycle(tenv, T.NAME(sym, tyRef), seen) =
            (case !tyRef of
              SOME(ty) => (S.contains(seen, sym)) orelse
                          (cycle(tenv, ty, S.enter(seen, sym, true)))
            | NONE => true)
        | cycle(tenv, _, seen) = false

      val foundCycle = foldl
        (fn (ty, foundCycle) => foundCycle orelse (cycle(tenv, ty, S.empty)))
        (false)
        (names)
    in
      if foundCycle then error pos "Found cyclical type definition" else ()
    end


  (*
    Transforms and type-checks an Absyn.Ty in the given type environment
  *)
  fun transTy(tenv, absynTy) =
    case absynTy of
      A.NameTy(sym, pos) =>
        Option.getOpt(lookupSymbol(tenv, sym, pos), T.TOP)

    | A.ArrayTy(sym, pos) =>
        T.ARRAY(actualType(tenv, Option.getOpt(lookupSymbol(tenv, sym, pos), T.TOP)), ref ())

    | A.RecordTy(fieldList) =>
        T.RECORD(
          map
            (fn ({name, escape, typ, pos}) =>
              (name, Option.getOpt(lookupSymbol(tenv, typ, pos), T.TOP)))
            (fieldList),
          ref ())

  (*
    Transforms and type-checks a variable
  *)
  fun transVar(venv, tenv, var, inLoop, level, exitLabel) : expty =
    case var of
      A.SimpleVar(sym, pos) =>
        (case lookupSymbol(venv, sym, pos) of
          SOME(E.VarEntry{access, ty, readOnly}) => {exp=Translate.simpleVar(access, level), ty=actualType(tenv, ty)}
        | _ => {exp=Translate.TODO(), ty=T.UNIT})

    | A.FieldVar(var, sym, pos) =>
        let
          val varResult = transVar(venv, tenv, var, inLoop, level, exitLabel)

          fun getFieldType((fieldName, fieldType) :: tail, varExp, fieldIdx) =
                if fieldName = sym then
                  {exp=Translate.fieldVar(varExp, fieldIdx), ty=actualType(tenv, fieldType)}
                else
                  getFieldType(tail, varExp, fieldIdx + 1)

            | getFieldType(nil, varExp, fieldIdx) = (
                error pos ("Field " ^ S.name(sym) ^ " does not exist");
                {exp=Translate.TODO(), ty=T.TOP})
        in
          case varResult of
            {exp=varExp, ty=T.RECORD(fieldList, unique)} => getFieldType(fieldList, varExp, 0)

          | _ => (
            error pos (S.name(sym) ^ " is not a record type");
            {exp=Translate.TODO(), ty=T.TOP})
        end

    | A.SubscriptVar(var, exp, pos) =>
        let
          val {exp=idxExp, ty=idxTy} = transExp(venv, tenv, inLoop, level, exitLabel) exp
        in
          (checkInt("Array index: ", {exp=idxExp, ty=idxTy}, pos);
          case transVar(venv, tenv, var, inLoop, level, exitLabel) of
            {exp=varExp, ty=T.ARRAY(ty, unique)} => {exp=Translate.arrayVar(varExp, idxExp), ty=actualType(tenv, ty)}
        
          | _ => (error pos "Cannot subscript a non-array type";
            {exp=Translate.TODO(), ty=T.TOP}))
        end


  (*
    Transforms and type-checks a function declaration in the given environments
  *)
  and transFuncDec(venv, tenv, {name, params, result, body, pos}, inLoop, level, exitLabel) =
    let
      val label = Temp.newlabel()
      val formalEscapes = map (fn ({name, escape, typ, pos}) => !escape) params
      val formalAccesses = Translate.formals(level)

      fun getParamTypes(({name, escape, typ, pos}, access)) = (name, Option.getOpt(lookupSymbol(tenv, typ, pos), T.TOP), access)
      val params' = map getParamTypes (ListPair.zip (params, formalAccesses))
      val formals = map (fn (name, ty, access) => ty) params'

      fun addParamToBodyVenv((name, ty, access), curVenv) = S.enter(curVenv, name, E.VarEntry{access=access, ty=ty, readOnly=false})
      val bodyVenv = foldl addParamToBodyVenv venv params'

      val {exp=_, ty=bodyTy} = transExp (bodyVenv, tenv, inLoop, level, exitLabel) body

      val returnType = checkFunctionDeclaredType(
        Option.mapPartial (fn (symbol, pos) => lookupSymbol(tenv, symbol, pos)) (result),
        bodyTy,
        pos)
    in
      {venv=S.enter(venv, name, E.FunEntry{level=level, label=label, formals=formals, result=returnType}),
       tenv=tenv}
    end

  (*
    Transforms and type-checks a declaration in the given environments
  *)
  and transDec(venv, tenv, dec, inLoop, level, exitLabel) = 
    case dec of 
       A.VarDec{name, escape, typ, init, pos} =>
        let
          val {exp=_, ty=inferredTy} = transExp(venv, tenv, inLoop, level, exitLabel) init

          val declaredTyOpt =
            Option.mapPartial
              (fn (typSym, typPos) => lookupSymbol(tenv, typSym, typPos))
              (typ)

          val variableType = checkDeclaredType(declaredTyOpt, inferredTy, pos)
          val access = Translate.allocLocal(level)(!escape)

        in
          (case (declaredTyOpt, inferredTy) of
            (NONE, T.NIL) => error pos "Unknown type of nil variable"
          |  _ => ();
          {venv=S.enter(venv, name, E.VarEntry{access=access, ty=variableType, readOnly=false}),
           tenv=tenv})
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
          fun getFormal({name, escape, typ, pos}) = Option.getOpt(lookupSymbol(tenv, typ, pos), T.TOP)

          fun getEscape({name, escape, typ, pos}) = !escape

          fun getHeaderInfo({name, params, result=SOME(result, resultPos), body, pos}) =
                let val label = Temp.newlabel() in
                  (name, map getFormal params, Option.getOpt(lookupSymbol(tenv, result, resultPos), T.TOP),
                    label, (Translate.newLevel{parent=level, name=label, formals=(map getEscape params)}))
                end
            
            | getHeaderInfo({name, params, result=NONE, body, pos}) =
                let val label = Temp.newlabel() in
                  (name, map getFormal params, T.UNIT,
                    label, (Translate.newLevel{parent=level, name=label, formals=(map getEscape params)}))
                end

          val headers = map getHeaderInfo decList

          val newLevels = map (fn (_, _, _, _, newLevel) => newLevel) headers

          val namesAndPos = map (fn ({name, params, result, body, pos}) => (name, pos)) decList

          fun createHeaderEnv((name, formals, result, label, level), curVenv) =
            S.enter(curVenv, name, E.FunEntry{level=level, label=label, formals=formals, result=result})

          val headerEnv = foldl createHeaderEnv venv headers

          (* Add the functions to the actual environments *)
          fun createEnv((functionDec, newLevel), {venv, tenv}) = transFuncDec(headerEnv, tenv, functionDec, false, newLevel, exitLabel)

        in
          (checkUnique(namesAndPos, S.empty);
           foldl createEnv {venv=venv, tenv=tenv} (ListPair.zip (decList, newLevels)))
        end


  (*
    Produces a transformation function which type-checks an expression with the given
    environments
  *)
  and transExp(venv, tenv, inLoop, level, exitLabel) : A.exp -> expty =
    let
      fun trexp(A.IntExp(intVal)) : expty =
            {exp=Translate.intExp(intVal), ty=T.INT}
        
      | trexp(A.StringExp(stringVal, pos)) =
          {exp=Translate.TODO(), ty=T.STRING}

      | trexp(A.NilExp) =
          {exp=Translate.nilExp(), ty=T.NIL}

      | trexp(A.ArrayExp{typ, size, init, pos}) =
          let
            fun getActualType(ty) = actualType(tenv, ty)
            val declaredType = Option.map getActualType (lookupSymbol(tenv, typ, pos))
            val arraySubtype = case declaredType of
              SOME(T.ARRAY(ty, unique)) => SOME(ty)
            | nonarray => nonarray

            val {exp=_, ty=initType} = trexp init
          in
            (checkInt("Array size: ", trexp size, pos);
             checkDeclaredType(arraySubtype, initType, pos); 
            {exp=Translate.TODO(), ty=Option.getOpt(declaredType, T.TOP)})
          end
        
      | trexp(A.OpExp{left, oper, right, pos}) =
          let
            val leftResult as {exp=leftExp, ty=_} = trexp left
            val rightResult as {exp=rightExp, ty=_} = trexp right
          in
            case oper of
              (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp) =>
                (checkInt("", leftResult, pos);
                 checkInt("", rightResult, pos);
                 {exp=Translate.arithExp(leftExp, oper, rightExp), ty=T.INT})
            | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) =>
                (checkCompOpTypes(leftResult, rightResult, pos);
                {exp=Translate.compExp(leftExp, oper, rightExp), ty=T.INT})

            | (A.EqOp | A.NeqOp) =>
                (checkEqualOpTypes(leftResult, rightResult, pos);
                {exp=Translate.compExp(leftExp, oper, rightExp), ty=T.INT})
          end

      | trexp(A.SeqExp(expPosList)) =
          let
            val typeList = map (fn (exp, _) => trexp exp) expPosList
            fun getTy({exp, ty}) = ty
            fun getExp({exp, ty}) = exp
          in
            case (typeList) of
              nil => {exp=Translate.TODO(), ty=T.UNIT}
            | _ =>   {exp=Translate.expSeq(map getExp typeList), ty=getTy (List.last typeList)}
          end

      | trexp(A.LetExp{decs, body, pos}) = 
          let val {venv=venv, tenv=tenv} = 
            foldl 
              (fn (dec, {venv=curVenv, tenv=curTenv}) => transDec(curVenv, curTenv, dec, inLoop, level, exitLabel))
              ({venv=venv, tenv=tenv})
              (decs)
          in 
            transExp(venv, tenv, inLoop, level, exitLabel) body
          end

      | trexp(A.VarExp(var)) =
          transVar(venv, tenv, var, inLoop, level, exitLabel)

      | trexp(A.CallExp{func, args, pos}) =
          let
            val funcEntry = lookupSymbol(venv, func, pos)
            val {formals=paramTypes, result=resultType, label=funcLabel, level=funcLevel} =
              case funcEntry of
                SOME(E.FunEntry{level, label, formals, result}) =>
                      {formals=formals, result=result, label=label, level=level}
              | _ => (error pos "Unable to apply a non-function value";
                     {formals=[], result=T.TOP, label=Temp.newlabel(), level=level})

            val argExptys = map trexp args
            val argTypes = map (fn ({exp, ty}) => ty) argExptys
            val argExps = map (fn ({exp, ty}) => exp) argExptys
          in
            (checkArgumentTypes(paramTypes, argTypes, pos);
            {exp=Translate.callExp(func, argExps, funcLevel, level), ty=resultType})
          end

      | trexp(A.AssignExp{var, exp, pos}) =
          let
            val varResult as {exp=varExp, ty=varTy} = transVar(venv, tenv, var, inLoop, level, exitLabel)
            val expResult as {exp=expExp, ty=expTy} = trexp exp
          in
            (checkWritable(venv, var);
             checkAssignmentTypes(varResult, expResult, pos);
            {exp=Translate.assignExp(varExp, expExp), ty=T.UNIT})
          end

      | trexp(A.IfExp{test, then', else'=NONE, pos}) =
          let
            val testResult as {exp=testExp, ty=testTy} = trexp test
            val thenResult as {exp=thenExp, ty=thenTy} = trexp then'
          in
            (checkInt("If test expression: ", testResult, pos);
             checkUnit("If body expression: ", thenResult, pos);
             {exp=Translate.ifExp(testExp, thenExp, NONE), ty=T.UNIT})
          end

      | trexp(A.IfExp{test, then', else'=SOME(antecedent), pos}) =
          let
            val testResult as {exp=testExp, ty=testTy} = trexp test
            val {exp=consExp, ty=consTy} = trexp then'
            val {exp=antExp, ty=antTy} = trexp antecedent
          in
            (checkInt("If test expression: ", testResult, pos);
             checkIfThenElseTypes(consTy, antTy, pos);
             {exp=Translate.ifExp(testExp, consExp, SOME(antExp)), ty=T.join(consTy, antTy)})
          end

      | trexp(A.ForExp{var, escape, lo, hi, body, pos}) = 
          let 
            val access = Translate.allocLocal(level)(!escape)
            val exitLabel = Temp.newlabel()
            val venv' = S.enter(venv, var, E.VarEntry{access=access, ty=T.INT, readOnly=true})
            val loResult as {exp=loExp, ty=loTy} = trexp lo
            val hiResult as {exp=hiExp, ty=hiTy} = trexp hi
            val bodyResult as {exp=bodyExp, ty=bodyTy} = transExp(venv', tenv, true, level, exitLabel) body
          in 
            (checkInt("For lo expression: ", loResult, pos);
             checkInt("For hi expression: ", hiResult, pos);
             checkUnit("For body expression: ", bodyResult, pos);
            {exp=Translate.forExp(access, loExp, hiExp, bodyExp, exitLabel), ty=T.UNIT})
          end

      | trexp(A.WhileExp{test, body, pos}) = 
          let
            val exitLabel = Temp.newlabel()
            val testResult as {exp=testExp, ty=testTy} = trexp test
            val bodyResult as {exp=bodyExp, ty=bodyTy} = transExp(venv, tenv, true, level, exitLabel) body
          in
            (checkInt("While test expression: ", testResult, pos);
             checkUnit("While body expression: ", bodyResult, pos);
            {exp=Translate.whileExp(testExp, bodyExp, exitLabel), ty=T.UNIT})
          end

      | trexp(A.RecordExp{fields=fieldList, typ, pos}) =
          let
            val recordType = actualType(
              tenv,
              Option.getOpt(lookupSymbol(tenv, typ, pos), T.TOP))

            fun getFieldType(symbol, exp, pos) =
              let val {exp=_, ty=fieldTy} = trexp exp
              in
                (symbol, fieldTy)
              end

            val fieldTypeList = map getFieldType fieldList
          in
            (checkRecordType(recordType, fieldTypeList, pos);
              {exp=Translate.TODO(), ty=recordType})
          end

      | trexp(A.BreakExp(pos)) = 
          (if not inLoop then (error pos "Illegal break, must be within a for or while loop")
           else ();
          {exp=Translate.breakExp(exitLabel), ty=T.BREAK})

      fun trexpLoop(A.BreakExp(pos)) = {exp=Translate.breakExp(exitLabel), ty=T.BREAK}
        | trexpLoop(exp) = trexp(exp)

      in if inLoop then trexpLoop else trexp
    end


  (* Translates and type-checks an abstract syntax tree *)
  fun transProg ast =
    (legalAst := true;
    let
      val mainLabel = Temp.newlabel()
      val mainLevel = Translate.newLevel{parent=Translate.outermost, name=mainLabel, formals=[]} 
      val {exp=topLevelExp, ty=topLevelType} = (transExp (E.baseVenv, E.baseTenv, false, mainLevel, mainLabel) ast)
      val _ = Translate.procEntryExit({level=mainLevel, body=topLevelExp})
    in ()
    end)

end