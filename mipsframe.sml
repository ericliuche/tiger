signature FRAME = 
sig
  type frame
  type access

  val FP: Temp.temp

  val newFrame: {name: Temp.label, formals: bool list} -> frame

  val name: frame -> Temp.label
  val formals: frame -> access list

  val allocLocal: frame -> bool -> access

  val wordSize: int

  val exp: access -> Tree.exp -> Tree.exp

end

(* A FRAME implementation targeting the MIPS architecture *)
structure MipsFrame : FRAME = 
struct

  datatype access = InFrame of int
                  | InReg of Temp.temp

  type frame = {name: Temp.label, formals: access list, numLocals: int ref}

  val FP = Temp.newtemp()
  val wordSize = 4

  fun name({name: Temp.label, formals: access list, numLocals: int ref}) = name

  fun formals({name: Temp.label, formals: access list, numLocals: int ref}) = formals

  fun allocLocal({name: Temp.label, formals: access list, numLocals: int ref}) =
    let
      fun alloc(true)  = (numLocals := !numLocals + 1; InFrame(0 - (!numLocals - 1) * wordSize))
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
    | exp(InFrame(offset)) = (fn (exp) => T.MEM(T.BINOP(T.PLUS, exp, T.CONST offset)))
end