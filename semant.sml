structure Semant: sig val transProg : Absyn.exp -> Translate.frag list end =
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure Ty = Types
  structure Tr = Translate

  (* The result type of transforming and type-checking an expression *)
  type expty = {exp: Tr.exp, ty: Ty.ty}

  (* Tracks whether the current AST is valid *)
  val legalAst = ref true

  (* Prints the given error message and marks the current AST as illegal *)
  fun error pos = fn msg =>
    (legalAst := false; ErrorMsg.error pos msg)

  (* Produces an error if the given expty is not an integer *)
  fun checkInt(message, {exp, ty}, pos) =
    if Ty.isSubtype(ty, Ty.INT) then ()
    else error pos (message ^ "Expected int, got " ^ (Ty.typeToString ty))

  (* Produces an error if the given expty is not unit type *)
  fun checkUnit(message, {exp, ty}, pos) =
    if Ty.isSubtype(ty, Ty.UNIT) then ()
    else error pos (message ^ "Expected unit, got " ^ (Ty.typeToString ty))

  (* Produces an error if the given exptys cannot be used in a comparison operator *)
  fun checkCompOpTypes({exp=_, ty=tyLeft}, {exp=_, ty=tyRight}, pos) =
    case (tyLeft, tyRight) of
      ((Ty.INT, Ty.INT) | (Ty.STRING, Ty.STRING)) => ()
    | (actualLeft, actualRight) => error pos
        ("Expected (int, int) or (string, string), got (" ^ (Ty.typeToString actualLeft) ^
        ", " ^ (Ty.typeToString(actualRight)) ^ ")")

  (* Produces an error if the given exptys cannot be used in an equality comparison *)
  fun checkEqualOpTypes({exp=_, ty=tyLeft}, {exp=_, ty=tyRight}, pos) =
    case (Ty.isSubtype(tyLeft, tyRight), Ty.isSubtype(tyRight, tyLeft)) of
      (false, false) =>
        error pos ("Cannot compare equality for types " ^
          Ty.typeToString(tyLeft) ^ " and " ^ Ty.typeToString(tyRight))
    | _ => ()

  (* Produces an error if the given expression cannot be assigned to the given variable *)
  fun checkAssignmentTypes({exp=_, ty=varTy}, {exp=_, ty=expTy}, pos) =
    if not (Ty.isSubtype(expTy, varTy)) then
      error pos ("Invalid assignment to type " ^ Ty.typeToString(varTy))
    else ()

  (*
    Produces an error if the variable type and the type of its initialization expression
    are not legal
  *)
  fun checkVarDecTypes(SOME({exp=_, ty=declaredType}), {exp=_, ty=inferredType}, pos) = 
        if not(Ty.isSubtype(inferredType, declaredType)) then 
          error pos ("Expected " ^ Ty.typeToString(declaredType) ^
                     ", got " ^ Ty.typeToString(inferredType))
        else ()

    | checkVarDecTypes(NONE, {exp=_, ty=inferredType}, pos) =
        if inferredType = Ty.NIL then error pos ("Unable to infer type") else ()

  (*
    Produces an error if the declared and actual types disagree and returns the declared type
    if it is present or the actual type otherwise
  *)
  fun checkDeclaredType(SOME(declared), actual, pos) =
        if not(Ty.isSubtype(actual, declared)) then
          (error pos ("Mismatch between declared and actual types - Expected " ^
                      Ty.typeToString(declared) ^ ", got " ^ Ty.typeToString(actual));
          Ty.TOP)
        else
          declared

    | checkDeclaredType(NONE, actual, pos) =
        actual

  (*
    Produces an error if the function return type and the body type are incompatible or
    if a procedure has a non-unit type
  *)
  fun checkFunctionDeclaredType(NONE, bodyExpty, pos) =
        (checkUnit("Procedure definition: ", bodyExpty, pos);
        Ty.UNIT)

    | checkFunctionDeclaredType(declaredOpt, bodyExpty, pos) =
        let
          val {exp=_, ty=bodyTy} = bodyExpty
        in
          checkDeclaredType(declaredOpt, bodyTy, pos)
        end

  (*
    Produces an error if the two branches do not have compatible types
  *)
  fun checkIfThenElseTypes(consTy, antTy, pos) =
    if not(Ty.isSubtype(consTy, antTy)) andalso not(Ty.isSubtype(antTy, consTy)) then
      error pos "Mismatch between if-then-else branch types"
    else ()

  (*
    Produces an error if the given list of types is not compatible with the given list
    of actual Ty. 
  *)
  fun checkTypeList(expectedList, actualList) =
    ListPair.allEq
      (fn (expected, actual) => (Ty.isSubtype(actual, expected)))
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
  fun checkRecordType(Ty.RECORD(typeFields, unique), recordFields, pos) =
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
        error pos ("Cannot assign a record to type " ^ Ty.typeToString(actualType))

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
      Ty.NAME(sym, tyRef) => actualType(tenv, Option.getOpt(!tyRef, Ty.TOP))
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
  fun checkEnvCycles({venv, tenv, expList}, names, pos) =
    let

      fun cycle(tenv, Ty.NAME(sym, tyRef), seen) =
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
        Option.getOpt(lookupSymbol(tenv, sym, pos), Ty.TOP)

    | A.ArrayTy(sym, pos) =>
        Ty.ARRAY(actualType(tenv, Option.getOpt(lookupSymbol(tenv, sym, pos), Ty.TOP)), ref ())

    | A.RecordTy(fieldList) =>
        Ty.RECORD(
          map
            (fn ({name, escape, typ, pos}) =>
              (name, Option.getOpt(lookupSymbol(tenv, typ, pos), Ty.TOP)))
            (fieldList),
          ref ())

  (*
    Transforms and type-checks a variable
  *)
  fun transVar(venv, tenv, var, inLoop, level, exitLabel) : expty =
    case var of
      A.SimpleVar(sym, pos) =>
        (case lookupSymbol(venv, sym, pos) of
          SOME(E.VarEntry{access, ty, readOnly}) => {exp=Tr.simpleVar(access, level), ty=actualType(tenv, ty)}
        | _ => {exp=Tr.error(), ty=Ty.UNIT})

    | A.FieldVar(var, sym, pos) =>
        let
          val varResult = transVar(venv, tenv, var, inLoop, level, exitLabel)

          fun getFieldType((fieldName, fieldType) :: tail, varExp, fieldIdx) =
                if fieldName = sym then
                  {exp=Tr.fieldVar(varExp, fieldIdx), ty=actualType(tenv, fieldType)}
                else
                  getFieldType(tail, varExp, fieldIdx + 1)

            | getFieldType(nil, varExp, fieldIdx) = (
                error pos ("Field " ^ S.name(sym) ^ " does not exist");
                {exp=Tr.error(), ty=Ty.TOP})
        in
          case varResult of
            {exp=varExp, ty=Ty.RECORD(fieldList, unique)} => getFieldType(fieldList, varExp, 0)

          | _ => (
            error pos (S.name(sym) ^ " is not a record type");
            {exp=Tr.error(), ty=Ty.TOP})
        end

    | A.SubscriptVar(var, exp, pos) =>
        let
          val {exp=idxExp, ty=idxTy} = transExp(venv, tenv, inLoop, level, exitLabel) exp
        in
          (checkInt("Array index: ", {exp=idxExp, ty=idxTy}, pos);
          case transVar(venv, tenv, var, inLoop, level, exitLabel) of
            {exp=varExp, ty=Ty.ARRAY(ty, unique)} => {exp=Tr.arrayVar(varExp, idxExp), ty=actualType(tenv, ty)}
        
          | _ => (error pos "Cannot subscript a non-array type";
            {exp=Tr.error(), ty=Ty.TOP}))
        end


  (*
    Transforms and type-checks a function declaration in the given environments
  *)
  and transFuncDec(venv, tenv, {name, params, result, body, pos}, inLoop, level, exitLabel) =
    let
      val label = Temp.namedlabel(Symbol.name name)
      val formalEscapes = map (fn ({name, escape, typ, pos}) => !escape) params
      val formalAccesses = Tr.formals(level)

      fun getParamTypes(({name, escape, typ, pos}, access)) = (name, Option.getOpt(lookupSymbol(tenv, typ, pos), Ty.TOP), access)
      val params' = map getParamTypes (ListPair.zip (params, formalAccesses))
      val formals = map (fn (name, ty, access) => ty) params'

      fun addParamToBodyVenv((name, ty, access), curVenv) = S.enter(curVenv, name, E.VarEntry{access=access, ty=ty, readOnly=false})
      val bodyVenv = foldl addParamToBodyVenv venv params'

      val bodyExpty as {exp=bodyExp, ty=bodyTy} = transExp (bodyVenv, tenv, inLoop, level, exitLabel) body

      val returnType = checkFunctionDeclaredType(
        Option.mapPartial (fn (symbol, pos) => lookupSymbol(tenv, symbol, pos)) (result),
        bodyExpty,
        pos)
    in
      (Tr.procEntryExit({level=level, body=bodyExp});

      {venv=S.enter(venv, name, E.FunEntry{level=level, label=label, formals=formals, result=returnType}),
       tenv=tenv})
    end

  (*
    Transforms and type-checks a declaration in the given environments
  *)
  and transDec(venv, tenv, dec, inLoop, level, exitLabel, expList) = 
    case dec of 
       A.VarDec{name, escape, typ, init, pos} =>
        let
          val {exp=initExp, ty=inferredTy} = transExp(venv, tenv, inLoop, level, exitLabel) init

          val declaredTyOpt =
            Option.mapPartial
              (fn (typSym, typPos) => lookupSymbol(tenv, typSym, typPos))
              (typ)

          val variableType = checkDeclaredType(declaredTyOpt, inferredTy, pos)
          val access = Tr.allocLocal(level)(!escape)

        in
          (case (declaredTyOpt, inferredTy) of
            (NONE, Ty.NIL) => error pos "Unknown type of nil variable"
          |  _ => ();
          {venv=S.enter(venv, name, E.VarEntry{access=access, ty=variableType, readOnly=false}),
           tenv=tenv,
           expList=(Tr.initExp(access, initExp) :: expList)})
        end

    | A.TypeDec(decList) =>
        let

          (* Build environment with empty name types *)
          val names = map (fn ({name, ty, pos}) => Ty.NAME(name, ref NONE)) decList
        
          fun addToNameTenv(name, curTenv) =
            case name of
              Ty.NAME(tyname, ty) => S.enter(curTenv, tyname, name)
            | _ => curTenv
          
          val nameTenv = foldl addToNameTenv tenv names

          (* Build real environment by resolving actual types for each name *)
          fun addToTenv({name, ty, pos}, curTenv) =
              let
                val tyResult = transTy(nameTenv, ty)
                val nameEnvResult = lookupSymbol(nameTenv, name, pos)
              in
                (case nameEnvResult of
                  SOME(Ty.NAME(sym, tyRef)) => tyRef := SOME(tyResult)
                | _ => ();
                S.enter(curTenv, name, tyResult))
              end

          val {name=_, ty=_, pos=startPos} = hd(decList)
          val env = {venv=venv, tenv= foldl addToTenv tenv decList, expList=expList}
        in
          (checkEnvCycles(env, names, startPos);
          env)
        end

    | A.FunctionDec(decList) =>
        let

          (* Create the type environment with function header information *)
          fun getFormal({name, escape, typ, pos}) = Option.getOpt(lookupSymbol(tenv, typ, pos), Ty.TOP)

          fun getEscape({name, escape, typ, pos}) = !escape

          fun getHeaderInfo({name, params, result=SOME(result, resultPos), body, pos}) =
                let val label = Temp.namedlabel(Symbol.name name) in
                  (name, map getFormal params, Option.getOpt(lookupSymbol(tenv, result, resultPos), Ty.TOP),
                    label, (Tr.newLevel{parent=level, name=label, formals=(map getEscape params)}))
                end
            
            | getHeaderInfo({name, params, result=NONE, body, pos}) =
                let val label = Temp.namedlabel(Symbol.name name) in
                  (name, map getFormal params, Ty.UNIT,
                    label, (Tr.newLevel{parent=level, name=label, formals=(map getEscape params)}))
                end

          val headers = map getHeaderInfo decList

          val newLevels = map (fn (_, _, _, _, newLevel) => newLevel) headers

          val namesAndPos = map (fn ({name, params, result, body, pos}) => (name, pos)) decList

          fun createHeaderEnv((name, formals, result, label, level), curVenv) =
            S.enter(curVenv, name, E.FunEntry{level=level, label=label, formals=formals, result=result})

          val headerEnv = foldl createHeaderEnv venv headers

          (* Add the functions to the actual environments *)
          fun createEnv((functionDec, newLevel), {venv, tenv}) = transFuncDec(headerEnv, tenv, functionDec, false, newLevel, exitLabel)

          val {venv=newVenv, tenv=newTenv} = foldl createEnv {venv=venv, tenv=tenv} (ListPair.zip (decList, newLevels))

        in
          (checkUnique(namesAndPos, S.empty);
           {venv=newVenv, tenv=newTenv, expList=expList})
        end


  (*
    Produces a transformation function which type-checks an expression with the given
    environments
  *)
  and transExp(venv, tenv, inLoop, level, exitLabel) : A.exp -> expty =
    let
      fun trexp(A.IntExp(intVal)) : expty =
            {exp=Tr.intExp(intVal), ty=Ty.INT}
        
      | trexp(A.StringExp(stringVal, pos)) =
          {exp=Tr.stringExp(stringVal), ty=Ty.STRING}

      | trexp(A.NilExp) =
          {exp=Tr.nilExp(), ty=Ty.NIL}

      | trexp(A.ArrayExp{typ, size, init, pos}) =
          let
            fun getActualType(ty) = actualType(tenv, ty)
            val declaredType = Option.map getActualType (lookupSymbol(tenv, typ, pos))
            val arraySubtype = case declaredType of
              SOME(Ty.ARRAY(ty, unique)) => SOME(ty)
            | nonarray => nonarray

            val initResult as {exp=initExp, ty=initType} = trexp init
            val sizeResult as {exp=sizeExp, ty=sizeType} = trexp size
          in
            (checkInt("Array size: ", sizeResult, pos);
             checkDeclaredType(arraySubtype, initType, pos); 
            {exp=Tr.arrayExp(sizeExp, initExp), ty=Option.getOpt(declaredType, Ty.TOP)})
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
                {exp=Tr.arithExp(leftExp, oper, rightExp), ty=Ty.INT})
            | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) =>
                (checkCompOpTypes(leftResult, rightResult, pos);
                {exp=Tr.compExp(leftResult, oper, rightResult), ty=Ty.INT})
            | (A.EqOp | A.NeqOp) =>
                (checkEqualOpTypes(leftResult, rightResult, pos);
                {exp=Tr.compExp(leftResult, oper, rightResult), ty=Ty.INT})
          end

      | trexp(A.SeqExp(expPosList)) =
          let
            val typeList = map (fn (exp, _) => trexp exp) expPosList
            fun getTy({exp, ty}) = ty
            fun getExp({exp, ty}) = exp
          in
            case (typeList) of
              nil => {exp=Tr.error(), ty=Ty.UNIT}
            | _ =>   {exp=Tr.expSeq(map getExp typeList), ty=getTy (List.last typeList)}
          end

      | trexp(A.LetExp{decs, body, pos}) = 
          let
            val {venv=venv, tenv=tenv, expList=expList} = 
              foldl 
                (fn (dec, {venv=curVenv, tenv=curTenv, expList=curExpList}) =>
                    transDec(curVenv, curTenv, dec, inLoop, level, exitLabel, curExpList))
                ({venv=venv, tenv=tenv, expList=[]})
                (decs)

            val bodyResult as {exp=bodyExp, ty=bodyTy} =
              transExp(venv, tenv, inLoop, level, exitLabel) body

          in 
            {exp=Tr.letExp(rev expList, bodyExp), ty=bodyTy}
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
                     {formals=[], result=Ty.TOP, label=Temp.newlabel(), level=level})

            val argExptys = map trexp args
            val argTypes = map (fn ({exp, ty}) => ty) argExptys
            val argExps = map (fn ({exp, ty}) => exp) argExptys
          in
            (checkArgumentTypes(paramTypes, argTypes, pos);
            {exp=Tr.callExp(func, argExps, funcLevel, level), ty=resultType})
          end

      | trexp(A.AssignExp{var, exp, pos}) =
          let
            val varResult as {exp=varExp, ty=varTy} = transVar(venv, tenv, var, inLoop, level, exitLabel)
            val expResult as {exp=expExp, ty=expTy} = trexp exp
          in
            (checkWritable(venv, var);
             checkAssignmentTypes(varResult, expResult, pos);
            {exp=Tr.assignExp(varExp, expExp), ty=Ty.UNIT})
          end

      | trexp(A.IfExp{test, then', else'=NONE, pos}) =
          let
            val testResult as {exp=testExp, ty=testTy} = trexp test
            val thenResult as {exp=thenExp, ty=thenTy} = trexp then'
          in
            (checkInt("If test expression: ", testResult, pos);
             checkUnit("If body expression: ", thenResult, pos);
             {exp=Tr.ifExp(testExp, thenExp, NONE), ty=Ty.UNIT})
          end

      | trexp(A.IfExp{test, then', else'=SOME(antecedent), pos}) =
          let
            val testResult as {exp=testExp, ty=testTy} = trexp test
            val {exp=consExp, ty=consTy} = trexp then'
            val {exp=antExp, ty=antTy} = trexp antecedent
          in
            (checkInt("If test expression: ", testResult, pos);
             checkIfThenElseTypes(consTy, antTy, pos);
             {exp=Tr.ifExp(testExp, consExp, SOME(antExp)), ty=Ty.join(consTy, antTy)})
          end

      | trexp(A.ForExp{var, escape, lo, hi, body, pos}) = 
          let 
            val access = Tr.allocLocal(level)(!escape)
            val exitLabel = Temp.newlabel()
            val venv' = S.enter(venv, var, E.VarEntry{access=access, ty=Ty.INT, readOnly=true})
            val loResult as {exp=loExp, ty=loTy} = trexp lo
            val hiResult as {exp=hiExp, ty=hiTy} = trexp hi
            val bodyResult as {exp=bodyExp, ty=bodyTy} = transExp(venv', tenv, true, level, exitLabel) body
          in 
            (checkInt("For lo expression: ", loResult, pos);
             checkInt("For hi expression: ", hiResult, pos);
             checkUnit("For body expression: ", bodyResult, pos);
            {exp=Tr.forExp(access, loExp, hiExp, bodyExp, exitLabel), ty=Ty.UNIT})
          end

      | trexp(A.WhileExp{test, body, pos}) = 
          let
            val exitLabel = Temp.newlabel()
            val testResult as {exp=testExp, ty=testTy} = trexp test
            val bodyResult as {exp=bodyExp, ty=bodyTy} = transExp(venv, tenv, true, level, exitLabel) body
          in
            (checkInt("While test expression: ", testResult, pos);
             checkUnit("While body expression: ", bodyResult, pos);
            {exp=Tr.whileExp(testExp, bodyExp, exitLabel), ty=Ty.UNIT})
          end

      | trexp(A.RecordExp{fields=fieldList, typ, pos}) =
          let
            val recordType = actualType(
              tenv,
              Option.getOpt(lookupSymbol(tenv, typ, pos), Ty.TOP))

            fun getFieldType(symbol, exp, pos) =
              let val {exp=fieldExp, ty=fieldTy} = trexp exp
              in
                (symbol, fieldTy, fieldExp)
              end
            val fieldTypeExpList = map getFieldType fieldList

            val fieldTypeList = map (fn (sym, ty, _) => (sym, ty)) fieldTypeExpList
            val fieldExps = map (fn (_, _, exp) => exp) fieldTypeExpList
          in
            (checkRecordType(recordType, fieldTypeList, pos);
              {exp=Tr.recordExp(fieldExps), ty=recordType})
          end

      | trexp(A.BreakExp(pos)) = 
          (if not inLoop then (error pos "Illegal break, must be within a for or while loop")
           else ();
          {exp=Tr.breakExp(exitLabel), ty=Ty.BREAK})

      fun trexpLoop(A.BreakExp(pos)) = {exp=Tr.breakExp(exitLabel), ty=Ty.BREAK}
        | trexpLoop(exp) = trexp(exp)

      in if inLoop then trexpLoop else trexp
    end

  (* Debugging utility to print the frag list to stdout *)
  fun showIR(nil) = nil
    | showIR(frag :: rest) = (Tr.printFrag frag; frag :: showIR(rest))


  (* Translates and type-checks an abstract syntax tree *)
  fun transProg ast =
    (legalAst := true;
     Tr.clearFrags();
    let
      val mainLabel = Temp.namedlabel("main")
      val mainLevel = Tr.newLevel{parent=Tr.outermost, name=mainLabel, formals=[]} 
      val {exp=topLevelExp, ty=topLevelType} = (transExp (E.baseVenv, E.baseTenv, false, mainLevel, mainLabel) ast)
    in
      (Tr.procEntryExit({level=mainLevel, body=topLevelExp});
       Tr.getResult())
    end)

end