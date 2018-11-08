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
  val arrayVar: exp * exp * level -> exp

  val intExp: int -> exp

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

  structure T = Tree

  datatype exp = Ex of T.exp
               | Nx of T.stm
               | Cx of Temp.label * Temp.label -> T.stm


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

  fun arrayVar(varExp, idxExp, lev) =
    Ex(T.MEM(T.BINOP(
      T.PLUS,
      unEx varExp,
      T.BINOP(
        T.MUL,
        unEx idxExp,
        T.CONST (Frame.wordSize)))))



  fun intExp(intVal) = Ex(T.CONST intVal)

  fun TODO() = Ex(T.CONST 0)

end
