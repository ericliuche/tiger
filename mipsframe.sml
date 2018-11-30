signature FRAME = 
sig
  type frame
  type access
  type register

  val FP: Temp.temp
  val RV: Temp.temp
  val RA: Temp.temp
  val SP: Temp.temp

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
  val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
  val procEntryExit3 : frame * Assem.instr list -> {prolog: string, body: Assem.instr list, epilog: string}

  val tempMap: register Temp.Table.table

  val specialregs: (Temp.temp * register) list
  val argregs: (Temp.temp * register) list
  val calleesaves: (Temp.temp * register) list
  val callersaves: (Temp.temp * register) list

  val numReg: int

  (* Retrieve the temps or registers respectively from a list of (register * temp) *)
  val tempList: (Temp.temp * register) list -> Temp.temp list
  val registerList: (Temp.temp * register) list -> register list

  (* Debugging utility for printing a frag *)
  val printFrag: frag -> frag

  val tempName: Temp.temp -> string

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
  val RA = Temp.newtemp()
  val SP = Temp.newtemp()
  val ZERO = Temp.newtemp()

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

  structure T = Tree
  
  fun exp(InReg(temp)) = (fn (exp) => T.TEMP temp)
    | exp(InFrame(0)) = (fn (exp) => T.MEM(exp))
    | exp(InFrame(offset)) = (fn (exp) => T.MEM(T.BINOP(T.PLUS, exp, T.CONST offset)))

  fun externalCall(name, args) =
    T.CALL(T.NAME(Temp.namedlabel(name)), args)



  (* Assign temps to all of the special MIPS registers and initialize the temp map *)
  val (specialregs, argregs, calleesaves, callersaves, tempMap) =
    let
      val tempMap = ref (Temp.Table.init([
        (FP, "$fp"),
        (RV, "$v0"),
        (RA, "$ra"),
        (SP, "$sp"),
        (ZERO, "$0")
      ]))

      val argregs = ["$a0", "$a1", "$a2", "$a3"]
      val calleesaves = ["$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7"]
      val callersaves = ["$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9"]

      fun initRegList(nil) = nil
        | initRegList(reg :: rest) =
            let
              val temp = Temp.newtemp()
            in
              tempMap := Temp.Table.enter(!tempMap, temp, reg);
              (temp, reg) :: initRegList(rest)
            end
    in
      ([(FP, "$fp"), (RV, "$rv"), (RA, "$ra"), (SP, "$sp"), (ZERO, "$0")],
       initRegList argregs,
       initRegList calleesaves,
       initRegList callersaves,
       !tempMap)
    end

  val numReg = (length callersaves) + (length calleesaves) + (length specialregs) + (length argregs)

  fun tempList(tempRegs) = map (fn (temp, reg) => temp) tempRegs

  fun registerList(tempRegs) = map (fn (temp, reg) => reg) tempRegs


  fun newFrame({name: Temp.label, formals: bool list}) =
    let
      val frameCount = ref 0

      fun allocFormal(esc) =
        if not esc then
          InReg(Temp.newtemp())
        else
          (frameCount := !frameCount + 1;
           InFrame((!frameCount - 1) * wordSize))

    in
      {name=name, formals=map allocFormal formals, numLocals=ref 0}
    end


  fun procEntryExit1(frame, body) = body

  fun procEntryExit2(frame, body) =
    body @ [Assem.OPER{assem="",
                       src=(tempList (calleesaves @ specialregs)),
                       dst=[],
                       jump=SOME([])}]

  fun procEntryExit3({name, formals, numLocals}, body) =
    {prolog="PROCEDURE " ^ (Symbol.name name) ^ " \n",
     body=body,
     epilog="END " ^ (Symbol.name name) ^ " \n"}

  fun tempName(temp) = Option.getOpt(Temp.Table.look(tempMap, temp), Temp.makestring(temp))

  fun printFrag(frag as PROC{body=stm, frame={name=name, formals=_, numLocals=_}}) =
        (print "\n\n"; Printtree.printtree(TextIO.stdOut, stm); frag)
    | printFrag(frag as STRING(label, stringVal)) =
        (print "\n\n"; print (Symbol.name (label)); print(" = "); print(stringVal); print "\n"; frag)
end