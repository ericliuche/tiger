signature TRANSLATE = 
sig
  type level
  type access

  val outermost: level
  val newLevel: {parent: level, name: Temp.label, formals: bool list} -> level
  val formals: level -> access list
  val allocLocal: level -> bool -> access
end

structure Translate: TRANSLATE = 
struct

  structure Frame: FRAME = MipsFrame

  datatype level = Level of {parent: level, frame: Frame.frame}
                 | Outermost

  type access = level * Frame.access

  val outermost = Outermost


  fun newLevel({parent, name, formals}) =
    Level{parent=parent, frame=Frame.newFrame{name=name, formals=true :: formals}}


  fun formals(level as Outermost) = []

    | formals(level as Level{parent, frame}) =
        case Frame.formals(frame) of
          staticLinkOffset :: formals => map (fn formal => (level, formal)) (formals)
        | nil => nil

  exception OutermostFrameException

  fun allocLocal(level as Outermost) = raise OutermostFrameException
    | allocLocal(level as Level{parent, frame}) =
        fn esc => (level, Frame.allocLocal(frame)(esc))


end