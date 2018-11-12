signature FRAME = 
sig
  type frame
  type access

  val FP: Temp.temp
  val RV: Temp.temp

  val newFrame: {name: Temp.label, formals: bool list} -> frame

  val name: frame -> Temp.label
  val formals: frame -> access list

  val allocLocal: frame -> bool -> access

  val wordSize: int

  val exp: access -> Tree.exp -> Tree.exp

  datatype frag = PROC of {body: Tree.stm, frame: frame}
              | STRING of Temp.label * string

  val externalCall: string * Tree.exp list -> Tree.exp

  val procEntryExit1 : frame * Tree.stm -> Tree.stm

  (* Debugging utility for printing a frag *)
  val printFrag: frag -> frag

end

(* A FRAME implementation targeting the MIPS architecture *)
structure MipsFrame : FRAME = 
struct

  datatype access = InFrame of int
                  | InReg of Temp.temp

  type frame = {name: Temp.label, formals: access list, numLocals: int ref}

  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  val FP = Temp.newtemp()
  val RV = Temp.newtemp()
  val wordSize = 4

  fun name({name: Temp.label, formals: access list, numLocals: int ref}) = name

  fun formals({name: Temp.label, formals: access list, numLocals: int ref}) = formals

  fun allocLocal({name: Temp.label, formals: access list, numLocals: int ref}) =
    let
      fun alloc(true)  = (numLocals := !numLocals + 1; InFrame(0 - !numLocals * wordSize))
        | alloc(false) = InReg(Temp.newtemp())
    in
      alloc
    end

  fun newFrame({name: Temp.label, formals: bool list}) =
    let
      val maxRegFormals = 4
      val regCount = ref 0
      val frameCount = ref 0

      fun allocFormal(esc) =
        if ((not esc) andalso (!regCount < maxRegFormals)) then
          (regCount := !regCount + 1;
           InReg(Temp.newtemp()))
        else
          (frameCount := !frameCount + 1;
           InFrame((!frameCount - 1) * wordSize))

    in
      {name=name, formals=map allocFormal formals, numLocals=ref 0}
    end


  structure T = Tree
  
  fun exp(InReg(temp)) = (fn (exp) => T.TEMP temp)
    | exp(InFrame(0)) = (fn (exp) => T.MEM(exp))
    | exp(InFrame(offset)) = (fn (exp) => T.MEM(T.BINOP(T.PLUS, exp, T.CONST offset)))

  fun externalCall(name, args) =
    T.CALL(T.NAME(Temp.namedlabel(name)), args)

  fun procEntryExit1(frame, body) = body

  fun printFrag(frag as PROC{body=stm, frame={name=name, formals=_, numLocals=_}}) =
        (print "\n\n"; Printtree.printtree(TextIO.stdOut, stm); frag)
    | printFrag(frag as STRING(label, stringVal)) =
        (print "\n\n"; print (Symbol.name (label)); print(" = "); print(stringVal); print "\n"; frag)
end