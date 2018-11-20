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

      exception IllegalTree

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

        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, exp1, T.CONST(intVal))), exp2)) =
            emit(A.OPER{assem="sw `s0, " ^ (Int.toString intVal) ^ "(`s1)\n",
                        src=[munchExp exp1, munchExp exp2],
                        dst=[],
                        jump=NONE})

        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST(intVal), exp1)), exp2)) =
            emit(A.OPER{assem="sw `s0, " ^ (Int.toString intVal) ^ "(`s1)\n",
                        src=[munchExp exp1, munchExp exp2],
                        dst=[],
                        jump=NONE})


        | munchStm(T.MOVE(T.MEM(exp1), exp2)) =
            emit(A.OPER{assem="sw `s0, `s1\n",
                        src=[munchExp exp1, munchExp exp2],
                        dst=[],
                        jump=NONE})

        | munchStm(T.MOVE(T.TEMP(temp), T.CALL(T.NAME(funcName), argExps))) =
            emit(A.OPER{assem="jal " ^ (Symbol.name funcName) ^ "\n",
                        src=munchArgs(0, argExps),
                        dst=[],
                        jump=SOME([funcName])})

        | munchStm(T.MOVE(T.TEMP(temp), T.CONST(intVal))) =
            emit(A.OPER{assem="li `d0, " ^ (Int.toString intVal) ^ "\n",
                        src=[],
                        dst=[temp],
                        jump=NONE})

        | munchStm(T.MOVE(T.TEMP(temp), exp)) =
            emit(A.MOVE{assem="move `d0, `s0\n",
                        src=munchExp exp,
                        dst=temp})

        | munchStm(_) = raise IllegalTree


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


        | munchExp(T.BINOP(T.MINUS, T.CONST(0), exp)) =
            result(fn r =>
              emit(A.OPER{assem="neg `d0, `s0\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.BINOP(T.MINUS, exp, T.CONST(intVal))) =
            result(fn r =>
              emit(A.OPER{assem="sub `d0, `s0, " ^ (Int.toString intVal) ^ "\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))


        | munchExp(T.BINOP(T.MUL, T.CONST(intVal), exp)) =
            result(fn r =>
              emit(A.OPER{assem="mul `d0, `s0, " ^ (Int.toString intVal) ^ "\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.BINOP(T.MUL, exp, T.CONST(intVal))) =
            result(fn r =>
              emit(A.OPER{assem="mul `d0, `s0, " ^ (Int.toString intVal) ^ "\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))


        | munchExp(T.BINOP(T.DIV, exp, T.CONST(intVal))) =
            result(fn r =>
              emit(A.OPER{assem="div `d0, `s0, " ^ (Int.toString intVal) ^ "\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))


        | munchExp(T.BINOP(binop, exp1, exp2)) =
            let
              val binopAssem = case binop of
                T.PLUS => "add"
              | T.MINUS => "sub"
              | T.MUL => "mul"
              | T.DIV => "div"
              | T.AND => "and"
              | T.OR => "or"
              | T.LSHIFT => "sll"
              | T.RSHIFT => "srl"
              | T.ARSHIFT => "sra"
              | T.XOR => "xor"
            in
              result(fn r =>
                emit(A.OPER{assem=(binopAssem ^ " `d0, `s0, `s1\n"),
                            src=[munchExp exp1, munchExp exp2],
                            dst=[r],
                            jump=NONE}))
            end


        | munchExp(T.TEMP(temp)) =
            result(fn r =>
              emit(A.MOVE{assem="move `d0, `s0\n",
                          src=temp,
                          dst=r}))


        | munchExp(T.MEM(T.BINOP(T.PLUS, exp, T.CONST(intVal)))) =
            result(fn r =>
              emit(A.OPER{assem="lw `d0, " ^ (Int.toString intVal) ^ "(`s0)\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST(intVal), exp))) =
            result(fn r =>
              emit(A.OPER{assem="lw `d0, " ^ (Int.toString intVal) ^ "(`s0)\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.MEM(T.CONST(intVal))) =
            result(fn r =>
              emit(A.OPER{assem="lw `d0, " ^ (Int.toString intVal) ^ "\n",
                          src=[],
                          dst=[r],
                          jump=NONE}))        

        | munchExp(T.MEM(exp)) =
            result(fn r =>
              emit(A.OPER{assem="lw `d0, `s0\n",
                          src=[munchExp exp],
                          dst=[r],
                          jump=NONE}))


        | munchExp(T.CONST(intVal)) =
            result(fn r =>
              emit(A.OPER{assem="li `d0, " ^ (Int.toString intVal) ^ "\n",
                          src=[],
                          dst=[r],
                          jump=NONE}))

        | munchExp(T.CALL(T.NAME(funcName), argExps)) =
            result(fn r =>
              emit(A.OPER{assem="jal " ^ (Symbol.name funcName) ^ "\n",
                          src=munchArgs(0, argExps),
                          dst=[],
                          jump=SOME([funcName])}))

        | munchExp(T.NAME(strLabel)) =
            result(fn r =>
              emit(A.OPER{assem="la `d0, " ^ (Symbol.name strLabel) ^ "\n",
                          src=[],
                          dst=[r],
                          jump=NONE}))

        | munchExp(tree) = (Printtree.printtree(TextIO.stdOut, T.EXP(tree)); raise IllegalTree)


      (*
        Move the first 4 arguments into a registers, then allocate the rest of
        the arguments on the stack frame
      *)
      and munchArgs(idx, nil) = nil
        | munchArgs(idx, argExp :: rest) =
            if idx < (length(Frame.argregs) - 1) then
              let
                val (argTemp, argReg) = List.nth(Frame.argregs, idx)
              in
                (munchStm(T.MOVE(T.TEMP(argTemp), argExp));
                 argTemp :: munchArgs(idx + 1, rest))
              end

            (* 
              Once we start pushing args to the stack, do so in reverse order
              so that they can be read in order by incrementing the address from
              the frame pointer.
            *)
            else if idx = (length(Frame.argregs) - 1) then
              (munchExp argExp) :: munchArgs(idx + 1, rev(rest))

            else
              (munchStm(T.MOVE(
                Frame.exp(Frame.allocLocal(frame)(true))
                                          (T.TEMP(Frame.FP)),
                T.TEMP(munchExp(argExp))));
              munchArgs(idx + 1, rest))


    in
      (munchStm stm;
       rev(!instrs))
    end
end
