signature CODEGEN = 
sig
  structure Frame: FRAME
  val codegen: Frame.frame -> Tree.stm -> Assem.instr list
end


structure MipsCodegen: CODEGEN =
struct

  structure Frame = MipsFrame
  structure A = Assem
  structure T = Tree

  fun codegen(frame)(stm) =
    let
      val instrs = ref nil

      fun emit(instr) = instrs := (instr :: !instrs)

      fun result(gen) =
        let
          val t = Temp.newtemp()
        in
          (gen t; t)
        end


      fun munchStm(T.SEQ(a, b)) = (munchStm a; munchStm b)

        | munchStm(T.LABEL(label)) =
            emit(A.LABEL{assem=(Symbol.name label) ^ ":\n", lab=label})

        | munchStm(T.JUMP(T.NAME(label), labels)) =
            emit(A.OPER{assem="j " ^ (Symbol.name label) ^ "\n",
                        src=[],
                        dst=[],
                        jump=SOME(labels)})

        | munchStm(T.CJUMP(relop, exp1, exp2, trueLabel, falseLabel)) =
            let
              val relopAssem = case relop of
                T.EQ => "beq"
              | T.NE => "bne"
              | T.LT => "blt"
              | T.GT => "bgt"
              | T.LE => "ble"
              | T.GE => "bge"
              | T.ULT => "bltu"
              | T.ULE => "bleu"
              | T.UGT => "bgtu"
              | T.UGE => "bgeu"

            in
              emit(A.OPER{assem=(relopAssem ^ " `s0, `s1, " ^ (Symbol.name trueLabel) ^ "\n" ^
                                 "j " ^ (Symbol.name falseLabel) ^ "\n"),
                          src=[munchExp exp1, munchExp exp2],
                          dst=[],
                          jump=SOME([trueLabel, falseLabel])})
            end


        | munchStm(T.MOVE(T.MEM(exp1), exp2)) =
            emit(A.OPER{assem="sw `s0, `s1\n",
                        src=[munchExp exp1, munchExp exp2],
                        dst=[],
                        jump=NONE})

        | munchStm(T.MOVE(T.TEMP(temp), exp)) =
            emit(A.MOVE{assem="move `d0, `s0\n",
                        src=munchExp exp,
                        dst=temp})


      and munchExp(T.BINOP(T.PLUS, T.CONST(intVal), exp)) =
            result(fn r =>
              emit(A.OPER{assem="addi `d0, `s0, " ^ (Int.toString intVal) ^ "\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.BINOP(T.PLUS, exp, T.CONST(intVal))) =
            result(fn r =>
              emit(A.OPER{assem="addi `d0, `s0, " ^ (Int.toString intVal) ^ "\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.BINOP(T.PLUS, exp1, exp2)) =
            result(fn r =>
              emit(A.OPER{assem="add `d0, `s0, `s1\n",
                          src=[munchExp exp1, munchExp exp2],
                          dst=[r],
                          jump=NONE}))


        | munchExp(T.BINOP(T.MINUS, exp1, exp2)) =
            result(fn r =>
              emit(A.OPER{assem="sub `d0, `s0, `s1\n",
                          src=[munchExp exp1, munchExp exp2],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.BINOP(T.MUL, exp1, exp2)) =
            result(fn r =>
              emit(A.OPER{assem="mul `d0, `s0, `s1\n",
                          src=[munchExp exp1, munchExp exp2],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.BINOP(T.DIV, exp1, exp2)) =
            result(fn r =>
              emit(A.OPER{assem="div `d0, `s0, `s1\n",
                          src=[munchExp exp1, munchExp exp2],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.TEMP(temp)) =
            result(fn r =>
              emit(A.MOVE{assem="move `d0 `s0\n",
                          src=temp,
                          dst=r}))

        | munchExp(T.CONST(intVal)) =
            result(fn r =>
              emit(A.OPER{assem="li `d0, " ^ (Int.toString intVal) ^ "\n",
                          src=[],
                          dst=[r],
                          jump=NONE}))

    in
      (munchStm stm;
       rev(!instrs))
    end
end
