structure FindEscape: sig val findEscape: Absyn.exp -> unit end =

struct

  structure S = Symbol
  structure A = Absyn

  type depth = int
  type escEnv = (depth * bool ref) S.table

  fun traverseVar(env: escEnv, d: depth, s: A.var): unit =
    case s of
      A.SimpleVar(sym, pos) => (
        case S.look(env, sym) of
          SOME((depth, esc)) =>
            if (depth < d) then (esc := true) else ()
        | NONE => ())

    | A.FieldVar(var, sym, pos) => traverseVar(env, d, var)
    | A.SubscriptVar(var, exp, pos) => (
        traverseVar(env, d, var);
        traverseExp(env, d, exp))

  and traverseExp(env: escEnv, d: depth, s: A.exp): unit =
    let
      fun trexp(s: A.exp) = traverseExp(env, d, s)
    in
      case s of
        (A.NilExp | A.IntExp(_) | A.StringExp(_, _) | A.BreakExp(_)) => ()
    
      | A.VarExp(var) => traverseVar(env, d, var)

      | A.CallExp{func, args, pos} => (map trexp args; ())
      
      | A.OpExp{left, oper, right, pos} => (trexp left; trexp right)

      | A.RecordExp{fields, typ, pos} =>
          (map (fn (sym, exp, pos) => trexp exp) fields; ())

      | A.SeqExp(expList) => (map (fn (exp, pos) => trexp exp) expList; ())

      | A.AssignExp{var, exp, pos} => (traverseVar(env, d, var); trexp exp)

      | A.IfExp{test, then', else'=SOME(antecedent), pos} => (
          trexp test;
          trexp then';
          trexp antecedent)

      | A.IfExp{test, then', else'=NONE, pos} => (trexp test; trexp then')

      | A.WhileExp{test, body, pos} => (trexp test; trexp body)

      | A.ForExp{var, escape, lo, hi, body, pos} => (
          trexp lo;
          trexp hi;
          traverseExp(S.enter(env, var, (d, escape)), d, body))

      | A.LetExp{decs, body, pos} =>
          traverseExp(traverseDec(env, d, decs), d, body)

      | A.ArrayExp{typ, size, init, pos} => (trexp size; trexp init)
    end

  and traverseDec(env: escEnv, d: depth, s: A.dec list): escEnv =
    let
      fun trdec(A.FunctionDec(fundecs), env): escEnv =
            let
              fun addParamToEnv({name, escape, typ, pos}, curEnv) =
                S.enter(curEnv, name, (d + 1, escape))

              fun addFundecToEnv({name, params, result, body, pos}, curEnv) =
                foldl addParamToEnv curEnv params

              fun traverseFunc({name, params, result, body, pos}) =
                traverseExp((foldl addParamToEnv env params), d + 1, body)

            in
              (map traverseFunc fundecs;
              env)
            end

        | trdec(A.VarDec{name, escape, typ, init, pos}, env): escEnv = (
            traverseExp(env, d, init);
            S.enter(env, name, (d, escape)))

        | trdec(A.TypeDec(_), env): escEnv = env

    in
      foldl trdec env s
    end

  fun findEscape(prog: A.exp) : unit = traverseExp(S.empty, 0, prog)
end