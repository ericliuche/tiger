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

  val stringFrag: frag -> string

  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
  val procEntryExit3 : frame * Assem.instr list -> {prolog: string, body: Assem.instr list, epilog: string}

  val tempMap: register Temp.Table.table

  val registers: register list

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

  type frame = {name: Temp.label, formals: access list, numLocals: int ref,
                viewShiftMoves: Tree.stm list, maxParams: int ref}

  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  type register = string

  val FP = Temp.newtemp()
  val RV = Temp.newtemp()
  val RA = Temp.newtemp()
  val SP = Temp.newtemp()
  val ZERO = Temp.newtemp()

  val wordSize = 4

  fun name({name: Temp.label, ...}: frame) = name

  fun formals({formals: access list, ...}: frame) = formals

  fun allocLocal({numLocals: int ref, ...}: frame) =
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

  fun stringFrag(STRING(label, literal)) = (Symbol.name label) ^ ": .asciiz \"" ^ literal ^ "\"\n\n"
    | stringFrag(_) = ErrorMsg.impossible "Cannot treat a non-string fragment as a string"

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
      ([(FP, "$fp"), (RV, "$v0"), (RA, "$ra"), (SP, "$sp"), (ZERO, "$0")],
       initRegList argregs,
       initRegList calleesaves,
       initRegList callersaves,
       !tempMap)
    end

  val numReg = (length callersaves) + (length calleesaves) + (length specialregs) + (length argregs)

  fun tempList(tempRegs) = map (fn (temp, reg) => temp) tempRegs

  fun registerList(tempRegs) = map (fn (temp, reg) => reg) tempRegs

  val registers = registerList(calleesaves @ callersaves @ argregs @ specialregs)


  fun newFrame({name: Temp.label, formals: bool list}) =
    let
      val frameCount = ref 0
      val viewShiftMoves = ref []

      fun allocFormal((esc, argIdx)) =
        let
          val source =
            if argIdx < (length argregs) then
              Tree.TEMP((List.nth(tempList argregs, argIdx)))
            else
              Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP(FP), Tree.CONST((argIdx - 4) * wordSize)))
        in
          if not esc then
            let
              val temp = Temp.newtemp()  
            in
              viewShiftMoves := Tree.MOVE(Tree.TEMP(temp), source) :: !viewShiftMoves;
              InReg(temp)
            end
          else
            let
              val offset = !frameCount * wordSize
            in
              frameCount := !frameCount + 1;
              viewShiftMoves := Tree.MOVE(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP(FP), Tree.CONST(offset))), source) :: !viewShiftMoves;
              InFrame(offset)
            end
        end
        
        val indexes = List.tabulate(length formals, (fn idx => idx))
        val formalsWithIndexes = ListPair.zip(formals, indexes)

    in
      {name=name, formals=map allocFormal formalsWithIndexes, numLocals=ref 0,
       viewShiftMoves=(rev (!viewShiftMoves)), maxParams=ref 0}
    end


  fun procEntryExit1(frame as {name, formals, numLocals, viewShiftMoves, maxParams}, body) =
    let
      fun toSeqTree(stm1 :: stm2 :: nil) = Tree.SEQ(stm1, stm2)
        | toSeqTree(stm :: nil) = stm
        | toSeqTree(nil) = ErrorMsg.impossible "Cannot have empty view shift"
        | toSeqTree(stm :: rest) = Tree.SEQ(stm, toSeqTree(rest))

      val argMoves = toSeqTree viewShiftMoves

      fun getCalleeSavesMoves(temp) =
        let
          val newTemp = Temp.newtemp()
        in
          (Tree.MOVE(Tree.TEMP(newTemp), Tree.TEMP(temp)),
           Tree.MOVE(Tree.TEMP(temp), Tree.TEMP(newTemp)))
        end

      val calleeSavesMoves = map getCalleeSavesMoves (tempList calleesaves)
      val calleeSavesPrefix = map (fn (m1, m2) => m1) calleeSavesMoves
      val calleeSavesSuffix = map (fn (m1, m2) => m2) calleeSavesMoves

      val raAccess = allocLocal(frame)(true)
      val raSave = Tree.MOVE(exp(raAccess)(Tree.TEMP(SP)), Tree.TEMP(RA))
      val raLoad = Tree.MOVE(Tree.TEMP(RA), exp(raAccess)(Tree.TEMP(SP)))
    in
      Tree.SEQ(raSave,
        Tree.SEQ(argMoves,
          Tree.SEQ(toSeqTree calleeSavesPrefix,
            Tree.SEQ(body,
              toSeqTree (calleeSavesSuffix @ [raLoad])))))
    end


  fun procEntryExit2({maxParams, ...}: frame, body) =
    let
      fun getMaxParams(instr, prevMax) =
        case instr of
          Assem.OPER{jump=SOME(_), src=sources, ...} =>
            if (length(sources) + 3) > prevMax then length(sources) + 3 else prevMax
        | _ => prevMax

    in
      maxParams := foldr getMaxParams 2 body;
      print("Max params: " ^ (Int.toString (!maxParams)) ^ "\n");

      body @ [Assem.OPER{assem="",
                       src=(tempList (calleesaves @ specialregs)),
                       dst=[],
                       jump=SOME([])}]
    end

  fun procEntryExit3({name, formals, numLocals, viewShiftMoves, maxParams}, body) =
    let
      val maxFrameSize = (!maxParams) * wordSize

      val prolog = (Symbol.name name) ^ ":\n" ^
                   "move $fp, $sp\n" ^
                   "sub $sp, $sp, " ^ (Int.toString maxFrameSize) ^ "\n"

      val mainEpilog = if (Symbol.name name) = "main" then
        "move $t0, $v0\n" ^
        "li $v0, 1\n" ^
        "move $a0, $t0\n" ^
        "syscall\n"   
      else
        ""

      val epilog = "move $sp, $fp\n" ^
                   "addi $fp, $fp, " ^ (Int.toString maxFrameSize) ^ "\n" ^
                   mainEpilog ^
                   "jr $ra\n\n"
    in
      {prolog=prolog, body=body, epilog=epilog}
    end

  fun tempName(temp) = Option.getOpt(Temp.Table.look(tempMap, temp), Temp.makestring(temp))

  fun printFrag(frag as PROC{body=stm, frame={name=name, ...}}) =
        (print "\n\n"; Printtree.printtree(TextIO.stdOut, stm); frag)
    | printFrag(frag as STRING(label, stringVal)) =
        (print "\n\n"; print (Symbol.name (label)); print(" = "); print(stringVal); print "\n"; frag)
end