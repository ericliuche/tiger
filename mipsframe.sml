signature FRAME = 
sig
  type frame
  type access
  type register

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

  val tempMap: register Temp.Table.table

  val specialregs: (Temp.temp * register) list
  val argregs: (Temp.temp * register) list
  val calleesaves: (Temp.temp * register) list
  val callersaves: (Temp.temp * register) list

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

  type register = string

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

  (* Assign temps to all of the special MIPS registers and initialize the temp map *)
  val (specialregs, argregs, calleesaves, callersaves, tempMap) =
    let
      val tempMap = ref (Temp.Table.init([
        (FP, "$fp"),
        (RV, "$v0")
      ]))

      val specialregs = ["$fp", "$v0", "$v1", "$sp", "$ra", "$0"]
      val argregs = ["$a0", "$a1", "$a2", "$a3"]
      val calleesaves = ["$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7"]
      val callersaves = ["$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9"]

      fun initRegList(nil) = nil
        | initRegList(reg :: rest) =
            let
              val temp = Temp.newtemp()
            in

              (* We handle FP and RV separately, so don't add them to the table twice *)
              (if not (reg = "$fp") andalso not (reg = "$v0") then
                tempMap := Temp.Table.enter(!tempMap, temp, reg)
               else ();
              
              (temp, reg) :: initRegList(rest))
            end
    in
      (initRegList specialregs,
       initRegList argregs,
       initRegList calleesaves,
       initRegList callersaves,
       !tempMap)
    end

  fun printFrag(frag as PROC{body=stm, frame={name=name, formals=_, numLocals=_}}) =
        (print "\n\n"; Printtree.printtree(TextIO.stdOut, stm); frag)
    | printFrag(frag as STRING(label, stringVal)) =
        (print "\n\n"; print (Symbol.name (label)); print(" = "); print(stringVal); print "\n"; frag)
end