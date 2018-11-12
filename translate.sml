signature TRANSLATE = 
sig
  type level
  type access
  type exp

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

  val arithExp: exp * Absyn.oper * exp -> exp
  val compExp: exp * Absyn.oper * exp -> exp

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

  structure Frame: FRAME 
  val getResult : unit -> Frame.frag list

  (* Dummy value to allow for testing with an incomplete implementation *)
  val TODO: unit -> exp

end

structure Translate: TRANSLATE = 
struct

  (* Frame Layout *)

  structure Frame: FRAME = MipsFrame

  datatype level = Level of {parent: level, frame: Frame.frame, unique: unit ref}
                 | Outermost

  type access = level * Frame.access

  val outermost = Outermost

  val frags : Frame.frag list ref = ref []
  fun getResult() = rev (!frags)

  fun newLevel({parent, name, formals}) =
    Level{parent=parent, frame=Frame.newFrame{name=name, formals=true :: formals}, unique=ref ()}


  fun formals(level as Outermost) = []

    | formals(level as Level{parent, frame, unique}) =
        case Frame.formals(frame) of
          staticLinkOffset :: formals => map (fn formal => (level, formal)) (formals)
        | nil => nil

  exception OutermostLevelException

  fun allocLocal(level as Outermost) = raise OutermostLevelException
    | allocLocal(level as Level{parent, frame, unique}) =
        fn esc => (level, Frame.allocLocal(frame)(esc))

  (* IR Translation *)

  structure A = Absyn
  structure T = Tree

  datatype exp = Ex of T.exp
               | Nx of T.stm
               | Cx of Temp.label * Temp.label -> T.stm

  (* Raised in cases that are impossible to reach in valid Tiger programs *)
  exception IllegalProgramException

  exception EmptySeqException

  (* Produces a SEQ linked list from the list of statements *)
  fun seq(s :: nil) = s
    | seq(s :: rest) = T.SEQ(s, seq(rest))
    | seq(nil) = raise EmptySeqException

  (* Coerces the given exp into an exp used for its value *)
  fun unEx(Ex e) = e
    | unEx(Nx s) = T.ESEQ(s, T.CONST 0)
    | unEx(Cx genstm) =
        let
          val r = Temp.newtemp()
          val t = Temp.newlabel()
          val f = Temp.newlabel()
        in
          T.ESEQ(seq[T.MOVE(T.TEMP r, T.CONST 1),
                     genstm(t, f),
                     T.LABEL f,
                     T.MOVE(T.TEMP r, T.CONST 0),
                     T.LABEL t],
                T.TEMP r)
        end

  (* Coerces the given exp into a stm *)
  fun unNx(Nx s) = s
    | unNx(Ex e) = T.EXP(e)
    | unNx(Cx genstm) =
        let
          val t = Temp.newlabel()
          val f = Temp.newlabel()
        in
          seq[genstm(t, f), T.LABEL t, T.LABEL f]
        end


  (* Coerces the given exp into a conditional branching value *)
  fun unCx(Cx genstm) = genstm
    | unCx(Nx s) = unCx(Ex(T.CONST(0))) (* Unreachable in legal Tiger program *)
    | unCx(Ex (T.CONST 0)) = (fn (t, f) => T.JUMP(T.NAME f, [f]))
    | unCx(Ex (T.CONST 1)) = (fn (t, f) => T.JUMP(T.NAME t, [t]))
    | unCx(e as Ex(_)) = (fn (t, f) => T.CJUMP(T.NE, T.CONST 0, unEx e, t, f))


  (* Debugging utility to print an exp and return it *)
  fun printTree(exp as Cx(genstm)) =
        (Printtree.printtree(TextIO.stdOut, genstm(Temp.namedlabel("true"), Temp.namedlabel("false"))); exp)
    | printTree(exp) =
        (Printtree.printtree(TextIO.stdOut, unNx exp); exp)


  fun simpleVar(varAcc as (varLevel, varFrameAccess), curLevel) =
    let
      fun unpackLevel(Level({parent, frame, unique})) = (parent, frame, unique)
        | unpackLevel(level as Outermost) = raise OutermostLevelException

      val (varLevelParent, varLevelFrame, varLevelID) = unpackLevel varLevel

      (* Accumulates mem accesses for static links until we reach the correct level*)
      fun simpleVarAccum(curLevel: level, accumulator: T.exp) =
        let
          val (curLevelParent, curLevelFrame, curLevelID) = unpackLevel curLevel
          val staticLink = hd(Frame.formals curLevelFrame)
        in
          if curLevelID = varLevelID then
            Frame.exp(varFrameAccess)(accumulator)
          else
            simpleVarAccum(curLevelParent, Frame.exp(staticLink)(accumulator))
        end

      val result = simpleVarAccum(curLevel, T.TEMP(Frame.FP))
    in
      Ex(simpleVarAccum(curLevel, T.TEMP(Frame.FP)))
    end

  fun arrayVar(varExp, idxExp) =
    Ex(T.MEM(T.BINOP(
      T.PLUS,
      T.MEM(unEx varExp),
      T.BINOP(
        T.MUL,
        unEx idxExp,
        T.CONST (Frame.wordSize)))))

  fun fieldVar(varExp, fieldIdx) =
    Ex(T.MEM(T.BINOP(
      T.PLUS,
      T.MEM(unEx varExp),
      T.CONST(fieldIdx * Frame.wordSize))))

  fun intExp(intVal) = Ex(T.CONST intVal)

  fun nilExp() = Ex(T.CONST 0)

  fun stringExp lit = 
    let val label = Temp.newlabel()
    in
      frags := Frame.STRING(label, lit) :: !frags;
      Ex(T.NAME label)
    end

  fun assignExp(var, exp) = Nx(T.MOVE(unEx var, unEx exp))

  fun arithExp(leftExp, oper, rightExp) =
    let
      val binop = case oper of
        A.PlusOp   => T.PLUS
      | A.MinusOp  => T.MINUS
      | A.TimesOp  => T.MUL
      | A.DivideOp => T.DIV
      | _ => raise IllegalProgramException
    in
      Ex(T.BINOP(binop, unEx leftExp, unEx rightExp))
    end

  fun compExp(leftExp, oper, rightExp) =
    let
      val relop = case oper of
        A.EqOp  => T.EQ
      | A.NeqOp => T.NE
      | A.LtOp  => T.LT
      | A.LeOp  => T.LE
      | A.GtOp  => T.GT
      | A.GeOp  => T.GE
      | _     => raise IllegalProgramException
    in
      Cx(fn (t, f) => T.CJUMP(relop, unEx leftExp, unEx rightExp, t, f))
    end


  fun ifExp(test, Nx(then'), NONE) =
        let
          val consequent = Temp.newlabel()
          val join = Temp.newlabel()
        in
          Nx(seq[(unCx test)(consequent, join),
                 T.LABEL(consequent),
                 then',
                 T.LABEL(join)])
        end

    | ifExp(test, Nx(then'), SOME(Nx(else'))) =
        let
          val consequent = Temp.newlabel()
          val antecedent = Temp.newlabel()
          val join = Temp.newlabel()
        in
          Nx(seq[(unCx test)(consequent, antecedent),
                 T.LABEL(consequent),
                 then',
                 T.JUMP(T.NAME(join), [join]),
                 T.LABEL(antecedent),
                 else',
                 T.LABEL(join)])
        end

    | ifExp(test, Cx(then'), SOME(Cx(else'))) =
        let
          val consequent = Temp.newlabel()
          val antecedent = Temp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              T.LABEL(consequent),
                              then'(t, f),
                              T.LABEL(antecedent),
                              else'(t, f)])
        end

    | ifExp(test, then', SOME(Cx(else'))) =
        let
          val consequent = Temp.newlabel()
          val antecedent = Temp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              T.LABEL(consequent),
                              T.CJUMP(T.NE, unEx then', T.CONST(0), t, f),
                              T.LABEL(antecedent),
                              else'(t, f)])
        end

    | ifExp(test, Cx(then'), SOME(else')) =
        let
          val consequent = Temp.newlabel()
          val antecedent = Temp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              T.LABEL(consequent),
                              then'(t, f),
                              T.LABEL(antecedent),
                              T.CJUMP(T.NE, unEx else', T.CONST(0), t, f)])
        end

    | ifExp(test, then', NONE) =
        let
           val join = Temp.newlabel()
           val consequent = Temp.newlabel()
         in
           Nx(seq[(unCx test)(consequent, join),
                  T.LABEL(consequent),
                  unNx then',
                  T.LABEL(join)])
         end

    | ifExp(test, then', SOME(else')) =
        let
           val join = Temp.newlabel()
           val consequent = Temp.newlabel()
           val antecedent = Temp.newlabel()
           val result = Temp.newtemp()
         in
           Ex(T.ESEQ(seq[(unCx test)(consequent, antecedent),
                         T.LABEL(consequent),
                         T.MOVE(T.TEMP(result), unEx then'),
                         T.JUMP(T.NAME(join), [join]),
                         T.LABEL(antecedent),
                         T.MOVE(T.TEMP(result), unEx else'),
                         T.LABEL(join)],
                     T.TEMP(result)))
         end

  fun forExp((_, varFrameAccess), loExp, hiExp, bodyExp, exitLabel) =
    let
        val testVar = Frame.exp(varFrameAccess)(T.TEMP Frame.FP)
        val hiVar = Temp.newtemp()
        val body = Temp.newlabel()
        val inc = Temp.newlabel()
    in
        Nx(seq[T.MOVE(testVar, unEx loExp),
               T.MOVE(T.TEMP hiVar, unEx hiExp), 
               T.CJUMP(T.LE, testVar, T.TEMP hiVar, body, exitLabel),
               T.LABEL body, 
               unNx bodyExp,
               T.CJUMP(T.LT, testVar, T.TEMP hiVar, inc, exitLabel),
               T.LABEL inc,
               T.MOVE(testVar, T.BINOP(T.PLUS, testVar, T.CONST 1)),
               T.JUMP(T.NAME body, [body]),
               T.LABEL exitLabel])
    end

  fun whileExp(testExp, bodyExp, exitLabel) =
      let 
          val test = Temp.newlabel()
          val body = Temp.newlabel()
      in
          Nx(seq[T.LABEL test, (unCx testExp)(body, exitLabel), 
                 T.LABEL body, 
                 unNx bodyExp, 
                 T.JUMP(T.NAME test, [test]),
                 T.LABEL exitLabel])
      end

  fun breakExp exitLabel = Nx(T.JUMP(T.NAME exitLabel, [exitLabel]))

  fun callExp(funcName, argExpList, Outermost, callerLevel) =
        Ex(T.CALL(T.NAME funcName, map unEx argExpList))

    | callExp(funcName, argExpList, Level{parent=funcParent, frame=_, unique=_}, callerLevel) =
        let
          fun getStaticLink(callerLevel as Level{parent=callerParent, frame=_, unique=_}) =
            if funcParent = callerLevel then
              T.TEMP(Frame.FP)
            else
              T.MEM(getStaticLink(callerParent))

          | getStaticLink(Outermost) = raise OutermostLevelException

        in
          Ex(T.CALL(T.NAME funcName, getStaticLink(callerLevel) :: (map unEx argExpList)))
        end

  fun letExp([], bodyExps) = Ex(unEx bodyExps)
    | letExp(decExps, bodyExps) = Ex(T.ESEQ(seq (map unNx decExps), unEx bodyExps))

  fun expSeq(exp :: nil) = exp
    | expSeq(nil) = raise EmptySeqException
    | expSeq(stm :: rest) =
        (*printTree(Ex(T.ESEQ(unNx stm, unEx(expSeq rest))))*)
        let
          (* Accumulate all stms into one seq, and then return an eseq with the last expression *)
          fun seqAcc(e, nil) = e
            | seqAcc(stmSeq, exp :: nil) = Ex(T.ESEQ(unNx stmSeq, unEx exp))
            | seqAcc(stmSeq, nextStm :: rest) = seqAcc(Nx(T.SEQ(unNx stmSeq, unNx nextStm)), rest)
        in
          seqAcc(stm, rest)
        end

  fun recordExp(fieldList) =
    let
      val recordPtr = Temp.newtemp()

      fun setField(fieldExp, idx) =
        T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP(recordPtr), T.CONST(idx * (Frame.wordSize)))),
               unEx fieldExp)
    in
      Ex(T.ESEQ(
        seq(
          T.MOVE(T.TEMP(recordPtr),
                 Frame.externalCall("malloc", [T.CONST(length(fieldList) * Frame.wordSize)]))
          :: (map setField (ListPair.zip (fieldList, (List.tabulate(length(fieldList), (fn i => i))))))),
        T.TEMP(recordPtr)))
    end

  fun arrayExp(size, initVal) = Ex(Frame.externalCall("initArray", [unEx size, unEx initVal]))

  fun procEntryExit({level=Outermost, body}) = raise OutermostLevelException
    | procEntryExit({level=Level{parent, frame, unique}, body}) =
      frags := Frame.PROC{
          body=Frame.procEntryExit1(frame, T.MOVE(T.TEMP Frame.RV, unEx body)), 
          frame=frame
        } :: !frags

  fun TODO() = Ex(T.CONST 0)

end
