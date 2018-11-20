structure Main = struct

  structure Tr = Translate
  structure F = MipsFrame
  (* structure R = RegAlloc *)

  fun getsome (SOME x) = x

  fun emitproc out (F.PROC{body, frame}) =
    let
      (* val _ = print ("emit " ^ Frame.name frame ^ "\n") *)
	    val stms = Canon.linearize body
      val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
      val _ = (app (fn tree => Printtree.printtree(TextIO.stdOut, tree)) stms'; print("\n\n"))
	    val instrs = List.concat(map (MipsCodegen.codegen frame) stms') 

      fun tempName(temp) = Option.getOpt(Temp.Table.look(F.tempMap, temp), Temp.makestring(temp))

      val format0 = Assem.format(tempName)
    in
      (app (fn i => TextIO.output(out,format0 i)) instrs; print("\n\n"))
    end
    
    | emitproc out (F.STRING(lab, s)) = TextIO.output(out, s)

  fun withOpenFile fname f = 
    let
      val (out, closeOut) =
        (TextIO.openOut fname, TextIO.closeOut)
        (*(TextIO.stdOut, (fn _ => ()))*)
      
    in
      (f out before closeOut out) 
	    handle e => (TextIO.closeOut out; raise e)
    end 

   fun compile filename = 
       let val absyn = Parse.parse filename
           val frags = (FindEscape.findEscape absyn; Semant.transProg absyn)
        in 
            withOpenFile (filename ^ ".s") (fn out => (app (emitproc out) frags))
       end

end



