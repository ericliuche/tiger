signature TRANSLATE = 
sig
  type level
  type access
  type exp
  type frag

  structure Frame: FRAME

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

  val initExp: access * exp -> exp
  val assignExp: exp * exp -> exp

  val arithExp: exp * Absyn.oper * exp -> exp
  val compExp: {exp: exp, ty: Types.ty} * Absyn.oper * {exp: exp, ty: Types.ty} -> exp

  val ifExp: exp * exp * exp option -> exp
  val whileExp: exp * exp * Temp.label -> exp
  val forExp: access * exp * exp * exp * Temp.label -> exp
  val breakExp: Temp.label -> exp
  val letExp: exp list * exp -> exp
  val expSeq: exp list -> exp

  val callExp: Temp.label * exp list * level * level -> exp

  val recordExp: exp list -> exp
  val arrayExp: exp * exp -> exp

  val procEntryExit: {level: level, body: exp} -> unit

  val getResult: unit -> Frame.frag list
  val clearFrags: unit -> unit

  (* Error value returned during translation of illegal Tiger programs *)
  val error: unit -> exp

  (* Debugging utility to print a representation of the given frag to standard out *)
  val printFrag: frag -> frag

end

structure Translate: TRANSLATE = 
struct

  (* Frame Layout *)

  structure Frame = MipsFrame

  datatype level = Level of {parent: level, frame: Frame.frame, unique: unit ref}
                 | Outermost

  type access = level * Frame.access

  type frag = Frame.frag

  val outermost = Outermost

  val frags : Frame.frag list ref = ref []
  
  fun getResult() = rev (!frags)

  fun clearFrags() = frags := []

  fun newLevel({parent, name, formals}) =
    Level{parent=parent, frame=Frame.newFrame{name=name, formals=true :: formals}, unique=ref ()}

  fun formals(level as Outermost) = []

    | formals(level as Level{parent, frame, unique}) =
        case Frame.formals(frame) of
          staticLinkOffset :: formals => map (fn formal => (level, formal)) (formals)
        | nil => nil

  (* Raised in cases of illegal actions on the outermost lexical level *)
  exception OutermostLevelException

  fun allocLocal(level as Outermost) = raise OutermostLevelException
    | allocLocal(level as Level{parent, frame, unique}) =
        fn esc => (level, Frame.allocLocal(frame)(esc))



  (* IR Translation *)

  structure A = Absyn

  datatype exp = Ex of Tree.exp
               | Nx of Tree.stm
               | Cx of Temp.label * Temp.label -> Tree.stm

  (* Raised in cases that are impossible to reach in valid Tiger programs *)
  exception IllegalProgramException

  (* Produces a SEQ linked list from the list of statements *)
  fun seq(s :: nil) = s
    | seq(s :: rest) = Tree.SEQ(s, seq(rest))
    | seq(nil) = raise IllegalProgramException

  (* Coerces the given exp into an exp used for its value *)
  fun unEx(Ex e) = e
    | unEx(Nx s) = Tree.ESEQ(s, Tree.CONST 0)
    | unEx(Cx genstm) =
        let
          val r = Temp.newtemp()
          val t = Temp.newlabel()
          val f = Temp.newlabel()
        in
          Tree.ESEQ(seq[Tree.MOVE(Tree.TEMP r, Tree.CONST 1),
                     genstm(t, f),
                     Tree.LABEL f,
                     Tree.MOVE(Tree.TEMP r, Tree.CONST 0),
                     Tree.LABEL t],
                Tree.TEMP r)
        end

  (* Coerces the given exp into a stm *)
  fun unNx(Nx s) = s
    | unNx(Ex e) = Tree.EXP(e)
    | unNx(Cx genstm) =
        let
          val t = Temp.newlabel()
          val f = Temp.newlabel()
        in
          seq[genstm(t, f), Tree.LABEL t, Tree.LABEL f]
        end


  (* Coerces the given exp into a conditional branching value *)
  fun unCx(Cx genstm) = genstm
    | unCx(Nx s) = unCx(Ex(Tree.CONST(0))) (* Unreachable in legal Tiger program *)
    | unCx(Ex (Tree.CONST 0)) = (fn (t, f) => Tree.JUMP(Tree.NAME f, [f]))
    | unCx(Ex (Tree.CONST 1)) = (fn (t, f) => Tree.JUMP(Tree.NAME t, [t]))
    | unCx(e as Ex(_)) = (fn (t, f) => Tree.CJUMP(Tree.NE, Tree.CONST 0, unEx e, t, f))


  (* Debugging utility to print an exp and return it *)
  fun printTree(exp as Cx(genstm)) =
        (Printtree.printtree(TextIO.stdOut, genstm(Temp.namedlabel("true"), Temp.namedlabel("false"))); exp)
    | printTree(exp) =
        (Printtree.printtree(TextIO.stdOut, unNx exp); exp)

  (* Debugging utility to print a frag *)
  fun printFrag(frag) = Frame.printFrag(frag)


  (* Var translations *)

  fun simpleVar(varAcc as (varLevel, varFrameAccess), curLevel) =
    let
      fun unpackLevel(Level({parent, frame, unique})) = (parent, frame, unique)
        | unpackLevel(level as Outermost) = raise OutermostLevelException

      val (varLevelParent, varLevelFrame, varLevelID) = unpackLevel varLevel

      (* Accumulates mem accesses for static links until we reach the correct level*)
      fun simpleVarAccum(curLevel: level, accumulator: Tree.exp) =
        let
          val (curLevelParent, curLevelFrame, curLevelID) = unpackLevel curLevel
          val staticLink = hd(Frame.formals curLevelFrame)
        in
          if curLevelID = varLevelID then
            Frame.exp(varFrameAccess)(accumulator)
          else
            simpleVarAccum(curLevelParent, Frame.exp(staticLink)(accumulator))
        end
    in
      Ex(simpleVarAccum(curLevel, Tree.TEMP(Frame.FP)))
    end

  fun arrayVar(varExp, idxExp) =
    Ex(Tree.MEM(Tree.BINOP(
      Tree.PLUS,
      Tree.MEM(unEx varExp),
      Tree.BINOP(
        Tree.MUL,
        unEx idxExp,
        Tree.CONST (Frame.wordSize)))))

  fun fieldVar(varExp, fieldIdx) =
    Ex(Tree.MEM(Tree.BINOP(
      Tree.PLUS,
      Tree.MEM(unEx varExp),
      Tree.CONST(fieldIdx * Frame.wordSize))))


  (* Primitive expression translations *)

  fun intExp(intVal) = Ex(Tree.CONST intVal)

  fun nilExp() = Ex(Tree.CONST 0)

  fun stringExp lit = 
    let val label = Temp.newlabel()
    in
      frags := Frame.STRING(label, lit) :: !frags;
      Ex(Tree.NAME label)
    end


  (* Assignment/initialization translations *)

  fun initExp((level, frameAccess), exp) =
    Nx(Tree.MOVE(Frame.exp(frameAccess)(Tree.TEMP(Frame.FP)), unEx exp))
  
  fun assignExp(var, exp) = Nx(Tree.MOVE(unEx var, unEx exp))


  (* Operator expression translations *)

  fun arithExp(leftExp, oper, rightExp) =
    let
      val binop = case oper of
        A.PlusOp   => Tree.PLUS
      | A.MinusOp  => Tree.MINUS
      | A.TimesOp  => Tree.MUL
      | A.DivideOp => Tree.DIV
      | _ => raise IllegalProgramException
    in
      Ex(Tree.BINOP(binop, unEx leftExp, unEx rightExp))
    end

  fun compExp({exp=leftExp, ty=Types.STRING}, oper, {exp=rightExp, ty=Types.STRING}) =
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
          Ex(Frame.externalCall(funName, ([unEx leftExp, unEx rightExp])))
      end
    | compExp({exp=leftExp, ty=leftTy}, oper, {exp=rightExp, ty=rightTy}) =
      let
        val relop = case oper of
            A.EqOp  => Tree.EQ
          | A.NeqOp => Tree.NE
          | A.LtOp  => Tree.LT
          | A.LeOp  => Tree.LE
          | A.GtOp  => Tree.GT
          | A.GeOp  => Tree.GE
          | _     => raise IllegalProgramException
      in
        Cx(fn (t, f) => Tree.CJUMP(relop, unEx leftExp, unEx rightExp, t, f))
      end


  (* Control flow translations *)

  fun ifExp(test, Nx(then'), NONE) =
        let
          val consequent = Temp.newlabel()
          val join = Temp.newlabel()
        in
          Nx(seq[(unCx test)(consequent, join),
                 Tree.LABEL(consequent),
                 then',
                 Tree.LABEL(join)])
        end

    | ifExp(test, Nx(then'), SOME(Nx(else'))) =
        let
          val consequent = Temp.newlabel()
          val antecedent = Temp.newlabel()
          val join = Temp.newlabel()
        in
          Nx(seq[(unCx test)(consequent, antecedent),
                 Tree.LABEL(consequent),
                 then',
                 Tree.JUMP(Tree.NAME(join), [join]),
                 Tree.LABEL(antecedent),
                 else',
                 Tree.LABEL(join)])
        end

    | ifExp(test, Cx(then'), SOME(Cx(else'))) =
        let
          val consequent = Temp.newlabel()
          val antecedent = Temp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              Tree.LABEL(consequent),
                              then'(t, f),
                              Tree.LABEL(antecedent),
                              else'(t, f)])
        end

    | ifExp(test, then', SOME(Cx(else'))) =
        let
          val consequent = Temp.newlabel()
          val antecedent = Temp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              Tree.LABEL(consequent),
                              (unCx then')(t, f),
                              Tree.LABEL(antecedent),
                              else'(t, f)])
        end

    | ifExp(test, Cx(then'), SOME(else')) =
        let
          val consequent = Temp.newlabel()
          val antecedent = Temp.newlabel()
        in
          Cx(fn (t, f) => seq[(unCx test)(consequent, antecedent),
                              Tree.LABEL(consequent),
                              then'(t, f),
                              Tree.LABEL(antecedent),
                              (unCx else')(t, f)])
        end

    | ifExp(test, then', NONE) =
        let
           val join = Temp.newlabel()
           val consequent = Temp.newlabel()
         in
           Nx(seq[(unCx test)(consequent, join),
                  Tree.LABEL(consequent),
                  unNx then',
                  Tree.LABEL(join)])
         end

    | ifExp(test, then', SOME(else')) =
        let
           val join = Temp.newlabel()
           val consequent = Temp.newlabel()
           val antecedent = Temp.newlabel()
           val result = Temp.newtemp()
         in
           Ex(Tree.ESEQ(seq[(unCx test)(consequent, antecedent),
                         Tree.LABEL(consequent),
                         Tree.MOVE(Tree.TEMP(result), unEx then'),
                         Tree.JUMP(Tree.NAME(join), [join]),
                         Tree.LABEL(antecedent),
                         Tree.MOVE(Tree.TEMP(result), unEx else'),
                         Tree.LABEL(join)],
                     Tree.TEMP(result)))
         end

  fun forExp((_, varFrameAccess), loExp, hiExp, bodyExp, exitLabel) =
    let
        val testVar = Frame.exp(varFrameAccess)(Tree.TEMP Frame.FP)
        val hiVar = Temp.newtemp()
        val body = Temp.newlabel()
        val inc = Temp.newlabel()
    in
        Nx(seq[Tree.MOVE(testVar, unEx loExp),
               Tree.MOVE(Tree.TEMP hiVar, unEx hiExp), 
               Tree.CJUMP(Tree.LE, testVar, Tree.TEMP hiVar, body, exitLabel),
               Tree.LABEL body, 
               unNx bodyExp,
               Tree.CJUMP(Tree.LT, testVar, Tree.TEMP hiVar, inc, exitLabel),
               Tree.LABEL inc,
               Tree.MOVE(testVar, Tree.BINOP(Tree.PLUS, testVar, Tree.CONST 1)),
               Tree.JUMP(Tree.NAME body, [body]),
               Tree.LABEL exitLabel])
    end

  fun whileExp(testExp, bodyExp, exitLabel) =
      let 
          val test = Temp.newlabel()
          val body = Temp.newlabel()
      in
          Nx(seq[Tree.LABEL test, (unCx testExp)(body, exitLabel), 
                 Tree.LABEL body, 
                 unNx bodyExp, 
                 Tree.JUMP(Tree.NAME test, [test]),
                 Tree.LABEL exitLabel])
      end

  fun breakExp exitLabel = Nx(Tree.JUMP(Tree.NAME exitLabel, [exitLabel]))

  fun letExp([], bodyExp) = Ex(unEx bodyExp)
    | letExp(decExps, bodyExp) = Ex(Tree.ESEQ(seq (map unNx decExps), unEx bodyExp))

  fun expSeq(exp :: nil) = exp
    | expSeq(nil) = raise IllegalProgramException
    | expSeq(stm :: rest) =
        (*printTree(Ex(Tree.ESEQ(unNx stm, unEx(expSeq rest))))*)
        let
          (* Accumulate all stms into one seq, and then return an eseq with the last expression *)
          fun seqAcc(e, nil) = e
            | seqAcc(stmSeq, exp :: nil) = Ex(Tree.ESEQ(unNx stmSeq, unEx exp))
            | seqAcc(stmSeq, nextStm :: rest) = seqAcc(Nx(Tree.SEQ(unNx stmSeq, unNx nextStm)), rest)
        in
          seqAcc(stm, rest)
        end


  (* Function application translation *)

  fun callExp(funcName, argExpList, Outermost, callerLevel) =
        Ex(Tree.CALL(Tree.NAME funcName, map unEx argExpList))

    | callExp(funcName, argExpList, Level{parent=funcParent, frame=_, unique=_}, callerLevel) =
        let
          fun getStaticLink(callerLevel as Level{parent=callerParent, frame=_, unique=_}) =
            if funcParent = callerLevel then
              Tree.TEMP(Frame.FP)
            else
              Tree.MEM(getStaticLink(callerParent))

          | getStaticLink(Outermost) = raise OutermostLevelException

        in
          Ex(Tree.CALL(Tree.NAME funcName, getStaticLink(callerLevel) :: (map unEx argExpList)))
        end


  (* Record and array creation *)

  fun recordExp(fieldList) =
    let
      val recordPtr = Temp.newtemp()

      fun setField(fieldExp, idx) =
        Tree.MOVE(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP(recordPtr), Tree.CONST(idx * (Frame.wordSize)))),
               unEx fieldExp)
    in
      Ex(Tree.ESEQ(
        seq(
          Tree.MOVE(Tree.TEMP(recordPtr),
                 Frame.externalCall("malloc", [Tree.CONST(length(fieldList) * Frame.wordSize)]))
          :: (map setField (ListPair.zip (fieldList, (List.tabulate(length(fieldList), (fn i => i))))))),
        Tree.TEMP(recordPtr)))
    end

  fun arrayExp(size, initVal) = Ex(Frame.externalCall("initArray", [unEx size, unEx initVal]))


  (* Handles procedure call protocol boilerplate *)
  fun procEntryExit({level=Outermost, body}) = raise OutermostLevelException
    | procEntryExit({level=Level{parent, frame, unique}, body}) =
      frags := Frame.PROC{
          body=Frame.procEntryExit1(frame, Tree.MOVE(Tree.TEMP Frame.RV, unEx body)), 
          frame=frame
        } :: !frags


  (* Called during translation of illegal Tiger programs *)
  fun error() = raise IllegalProgramException

end
