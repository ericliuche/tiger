signature TRANSLATE = 
sig
  type level
  type access
  type exp
  type frag

  (* Frame Layout *)
  val outermost: level
  val newLevel: {parent: level, name: Temp.label, formals: bool list} -> level
  val formals: level -> access list
  val allocLocal: level -> bool -> access


  (* IR Translation *)
  val simpleVar: access * level -> exp
  val arrayVar: exp * exp -> exp
  val fieldVar: exp * int -> exp

  val intExp: int -> exp
  val nilExp: unit -> exp
  val stringExp: string -> exp

  val assignExp: exp * exp -> exp
  val initExp: access * exp -> exp

  val arithExp: exp * Absyn.oper * exp -> exp
  val compExp: {exp: exp, ty: Types.ty} * Absyn.oper * {exp: exp, ty: Types.ty} -> exp

  val ifExp: exp * exp * exp option -> exp
  val whileExp: exp * exp * Temp.label -> exp
  val forExp: access * exp * exp * exp * Temp.label -> exp
  val breakExp: Temp.label -> exp
  val letExp: exp list * exp -> exp
  val callExp: Temp.label * exp list * level * level -> exp

  val expSeq: exp list -> exp

  val recordExp: exp list -> exp
  val arrayExp: exp * exp -> exp

  val procEntryExit : {level: level, body: exp} -> unit

  structure F: FRAME 
  val getResult : unit -> F.frag list

  (* Dummy value to allow for testing with an incomplete implementation *)
  val TODO: unit -> exp

  val printFrag: frag -> frag

end

structure Translate: TRANSLATE = 
struct

  (* Frame Layout *)

  structure F = MipsFrame

  datatype level = Level of {parent: level, frame: F.frame, unique: unit ref}
                 | Outermost

  type access = level * F.access

  type frag = F.frag

  val outermost = Outermost

  val frags : F.frag list ref = ref []
  fun getResult() = rev (!frags)

  fun newLevel({parent, name, formals}) =
    Level{parent=parent, frame=F.newFrame{name=name, formals=true :: formals}, unique=ref ()}

  fun formals(level as Outermost) = []

    | formals(level as Level{parent, frame, unique}) =
        case F.formals(frame) of
          staticLinkOffset :: formals => map (fn formal => (level, formal)) (formals)
        | nil => nil

  exception OutermostLevelException

  fun allocLocal(level as Outermost) = raise OutermostLevelException
    | allocLocal(level as Level{parent, frame, unique}) =
        fn esc => (level, F.allocLocal(frame)(esc))

  (* IR Translation *)

  structure A = Absyn
  structure Te = Tree
  structure Tp = Temp
  structure Ty = Types

  datatype exp = Ex of Te.exp
               | Nx of Te.stm
               | Cx of Tp.label * Tp.label -> Te.stm

  (* Raised in cases that are impossible to reach in valid Tiger programs *)
  exception IllegalProgramException

  exception EmptySeqException

  (* Produces a SEQ linked list from the list of statements *)
  fun seq(s :: nil) = s
    | seq(s :: rest) = Te.SEQ(s, seq(rest))
    | seq(nil) = raise EmptySeqException

  (* Coerces the given exp into an exp used for its value *)
  fun unEx(Ex e) = e
    | unEx(Nx s) = Te.ESEQ(s, Te.CONST 0)
    | unEx(Cx genstm) =
        let
          val r = Tp.newtemp()
          val t = Tp.newlabel()
          val f = Tp.newlabel()
        in
          Te.ESEQ(seq[Te.MOVE(Te.TEMP r, Te.CONST 1),
                     genstm(t, f),
                     Te.LABEL f,
                     Te.MOVE(Te.TEMP r, Te.CONST 0),
                     Te.LABEL t],
                Te.TEMP r)
        end

  (* Coerces the given exp into a stm *)
  fun unNx(Nx s) = s
    | unNx(Ex e) = Te.EXP(e)
    | unNx(Cx genstm) =
        let
          val t = Tp.newlabel()
          val f = Tp.newlabel()
        in
          seq[genstm(t, f), Te.LABEL t, Te.LABEL f]
        end


  (* Coerces the given exp into a conditional branching value *)
  fun unCx(Cx genstm) = genstm
    | unCx(Nx s) = unCx(Ex(Te.CONST(0))) (* Unreachable in legal Tiger program *)
    | unCx(Ex (Te.CONST 0)) = (fn (t, f) => Te.JUMP(Te.NAME f, [f]))
    | unCx(Ex (Te.CONST 1)) = (fn (t, f) => Te.JUMP(Te.NAME t, [t]))
    | unCx(e as Ex(_)) = (fn (t, f) => Te.CJUMP(Te.NE, Te.CONST 0, unEx e, t, f))


  (* Debugging utility to print an exp and return it *)
  fun printTree(exp as Cx(genstm)) =
        (Printtree.printtree(TextIO.stdOut, genstm(Tp.namedlabel("true"), Tp.namedlabel("false"))); exp)
    | printTree(exp) =
        (Printtree.printtree(TextIO.stdOut, unNx exp); exp)

  fun printFrag(frag) = F.printFrag(frag)


  fun simpleVar(varAcc as (varLevel, varFrameAccess), curLevel) =
    let
      fun unpackLevel(Level({parent, frame, unique})) = (parent, frame, unique)
        | unpackLevel(level as Outermost) = raise OutermostLevelException

      val (varLevelParent, varLevelFrame, varLevelID) = unpackLevel varLevel

      (* Accumulates mem accesses for static links until we reach the correct level*)
      fun simpleVarAccum(curLevel: level, accumulator: Te.exp) =
        let
          val (curLevelParent, curLevelFrame, curLevelID) = unpackLevel curLevel
          val staticLink = hd(F.formals curLevelFrame)
        in
          if curLevelID = varLevelID then
            F.exp(varFrameAccess)(accumulator)
          else
            simpleVarAccum(curLevelParent, F.exp(staticLink)(accumulator))
        end

      val result = simpleVarAccum(curLevel, Te.TEMP(F.FP))
    in
      Ex(simpleVarAccum(curLevel, Te.TEMP(F.FP)))
    end

  fun arrayVar(varExp, idxExp) =
    Ex(Te.MEM(Te.BINOP(
      Te.PLUS,
      Te.MEM(unEx varExp),
      Te.BINOP(
        Te.MUL,
        unEx idxExp,
        Te.CONST (F.wordSize)))))

  fun fieldVar(varExp, fieldIdx) =
    Ex(Te.MEM(Te.BINOP(
      Te.PLUS,
      Te.MEM(unEx varExp),
      Te.CONST(fieldIdx * F.wordSize))))

  fun intExp(intVal) = Ex(Te.CONST intVal)

  fun nilExp() = Ex(Te.CONST 0)

  fun stringExp lit = 
    let val label = Tp.newlabel()
    in
      frags := F.STRING(label, lit) :: !frags;
      Ex(Te.NAME label)
    end

  fun assignExp(var, exp) = Nx(Te.MOVE(unEx var, unEx exp))

  fun initExp((level, frameAccess), exp) =
    Nx(Te.MOVE(F.exp(frameAccess)(Te.TEMP(F.FP)), unEx exp))

  fun arithExp(leftExp, oper, rightExp) =
    let
      val binop = case oper of
        A.PlusOp   => Te.PLUS
      | A.MinusOp  => Te.MINUS
      | A.TimesOp  => Te.MUL
      | A.DivideOp => Te.DIV
      | _ => raise IllegalProgramException
    in
      Ex(Te.BINOP(binop, unEx leftExp, unEx rightExp))
    end

  fun compExp({exp=leftExp, ty=Ty.STRING}, oper, {exp=rightExp, ty=Ty.STRING}) =
      let
        val funName = case oper of
            A.EqOp  => "stringEQ"
          | A.NeqOp => "stringNE"
          | A.LtOp  => "stringLT"
          | A.LeOp  => "stringLE"
          | A.GtOp  => "stringGT"
          | A.GeOp  => "stringGE"
          | _     => raise IllegalProgramException
      in
          Ex(F.externalCall(funName, ([unEx leftExp, unEx rightExp])))
      end
    | compExp({exp=leftExp, ty=leftTy}, oper, {exp=rightExp, ty=rightTy}) =
      let
        val relop = case oper of
            A.EqOp  => Te.EQ
          | A.NeqOp => Te.NE
          | A.LtOp  => Te.LT
          | A.LeOp  => Te.LE
          | A.GtOp  => Te.GT
          | A.GeOp  => Te.GE
          | _     => raise IllegalProgramException
      in
        Cx(fn (t, f) => Te.CJUMP(relop, unEx leftExp, unEx rightExp, t, f))
      end


  fun ifExp(test, Nx(then'), NONE) =
        let
          val consequent = Tp.newlabel()
          val join = Tp.newlabel()
        in
          Nx(seq[(unCx test)(consequent, join),
                 Te.LABEL(consequent),
                 then',
                 Te.LABEL(join)])
        end

    | ifExp(test, Nx(then'), SOME(Nx(else'))) =
        let
          val consequent = Tp.newlabel()
          val antecedent = Tp.newlabel()
          val join = Tp.newlabel()
        in
          Nx(seq[(unCx test)(consequent, antecedent),
                 Te.LABEL(consequent),
                 then',
                 Te.JUMP(Te.NAME(join), [join]),
                 Te.LABEL(antecedent),
                 else',
                 Te.LABEL(join)])
        end

    | ifExp(test, Cx(then'), SOME(Cx(else'))) =
        let
          val consequent = Tp.newlabel()
          val antecedent = Tp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              Te.LABEL(consequent),
                              then'(t, f),
                              Te.LABEL(antecedent),
                              else'(t, f)])
        end

    | ifExp(test, then', SOME(Cx(else'))) =
        let
          val consequent = Tp.newlabel()
          val antecedent = Tp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              Te.LABEL(consequent),
                              Te.CJUMP(Te.NE, unEx then', Te.CONST(0), t, f),
                              Te.LABEL(antecedent),
                              else'(t, f)])
        end

    | ifExp(test, Cx(then'), SOME(else')) =
        let
          val consequent = Tp.newlabel()
          val antecedent = Tp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              Te.LABEL(consequent),
                              then'(t, f),
                              Te.LABEL(antecedent),
                              Te.CJUMP(Te.NE, unEx else', Te.CONST(0), t, f)])
        end

    | ifExp(test, then', NONE) =
        let
           val join = Tp.newlabel()
           val consequent = Tp.newlabel()
         in
           Nx(seq[(unCx test)(consequent, join),
                  Te.LABEL(consequent),
                  unNx then',
                  Te.LABEL(join)])
         end

    | ifExp(test, then', SOME(else')) =
        let
           val join = Tp.newlabel()
           val consequent = Tp.newlabel()
           val antecedent = Tp.newlabel()
           val result = Tp.newtemp()
         in
           Ex(Te.ESEQ(seq[(unCx test)(consequent, antecedent),
                         Te.LABEL(consequent),
                         Te.MOVE(Te.TEMP(result), unEx then'),
                         Te.JUMP(Te.NAME(join), [join]),
                         Te.LABEL(antecedent),
                         Te.MOVE(Te.TEMP(result), unEx else'),
                         Te.LABEL(join)],
                     Te.TEMP(result)))
         end

  fun forExp((_, varFrameAccess), loExp, hiExp, bodyExp, exitLabel) =
    let
        val testVar = F.exp(varFrameAccess)(Te.TEMP F.FP)
        val hiVar = Tp.newtemp()
        val body = Tp.newlabel()
        val inc = Tp.newlabel()
    in
        Nx(seq[Te.MOVE(testVar, unEx loExp),
               Te.MOVE(Te.TEMP hiVar, unEx hiExp), 
               Te.CJUMP(Te.LE, testVar, Te.TEMP hiVar, body, exitLabel),
               Te.LABEL body, 
               unNx bodyExp,
               Te.CJUMP(Te.LT, testVar, Te.TEMP hiVar, inc, exitLabel),
               Te.LABEL inc,
               Te.MOVE(testVar, Te.BINOP(Te.PLUS, testVar, Te.CONST 1)),
               Te.JUMP(Te.NAME body, [body]),
               Te.LABEL exitLabel])
    end

  fun whileExp(testExp, bodyExp, exitLabel) =
      let 
          val test = Tp.newlabel()
          val body = Tp.newlabel()
      in
          Nx(seq[Te.LABEL test, (unCx testExp)(body, exitLabel), 
                 Te.LABEL body, 
                 unNx bodyExp, 
                 Te.JUMP(Te.NAME test, [test]),
                 Te.LABEL exitLabel])
      end

  fun breakExp exitLabel = Nx(Te.JUMP(Te.NAME exitLabel, [exitLabel]))

  fun callExp(funcName, argExpList, Outermost, callerLevel) =
        Ex(Te.CALL(Te.NAME funcName, map unEx argExpList))

    | callExp(funcName, argExpList, Level{parent=funcParent, frame=_, unique=_}, callerLevel) =
        let
          fun getStaticLink(callerLevel as Level{parent=callerParent, frame=_, unique=_}) =
            if funcParent = callerLevel then
              Te.TEMP(F.FP)
            else
              Te.MEM(getStaticLink(callerParent))

          | getStaticLink(Outermost) = raise OutermostLevelException

        in
          Ex(Te.CALL(Te.NAME funcName, getStaticLink(callerLevel) :: (map unEx argExpList)))
        end

  fun letExp([], bodyExp) = Ex(unEx bodyExp)
    | letExp(decExps, bodyExp) = Ex(Te.ESEQ(seq (map unNx decExps), unEx bodyExp))

  fun expSeq(exp :: nil) = exp
    | expSeq(nil) = raise EmptySeqException
    | expSeq(stm :: rest) =
        (*printTree(Ex(Te.ESEQ(unNx stm, unEx(expSeq rest))))*)
        let
          (* Accumulate all stms into one seq, and then return an eseq with the last expression *)
          fun seqAcc(e, nil) = e
            | seqAcc(stmSeq, exp :: nil) = Ex(Te.ESEQ(unNx stmSeq, unEx exp))
            | seqAcc(stmSeq, nextStm :: rest) = seqAcc(Nx(Te.SEQ(unNx stmSeq, unNx nextStm)), rest)
        in
          seqAcc(stm, rest)
        end

  fun recordExp(fieldList) =
    let
      val recordPtr = Tp.newtemp()

      fun setField(fieldExp, idx) =
        Te.MOVE(Te.MEM(Te.BINOP(Te.PLUS, Te.TEMP(recordPtr), Te.CONST(idx * (F.wordSize)))),
               unEx fieldExp)
    in
      Ex(Te.ESEQ(
        seq(
          Te.MOVE(Te.TEMP(recordPtr),
                 F.externalCall("malloc", [Te.CONST(length(fieldList) * F.wordSize)]))
          :: (map setField (ListPair.zip (fieldList, (List.tabulate(length(fieldList), (fn i => i))))))),
        Te.TEMP(recordPtr)))
    end

  fun arrayExp(size, initVal) = Ex(F.externalCall("initArray", [unEx size, unEx initVal]))

  fun procEntryExit({level=Outermost, body}) = raise OutermostLevelException
    | procEntryExit({level=Level{parent, frame, unique}, body}) =
      frags := F.PROC{
          body=F.procEntryExit1(frame, Te.MOVE(Te.TEMP F.RV, unEx body)), 
          frame=frame
        } :: !frags

  fun TODO() = Ex(Te.CONST 0)

end
