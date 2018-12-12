structure Main = struct

  structure Tr = Translate
  structure F = MipsFrame

  fun getsome (SOME x) = x

  fun emitproc out (F.PROC{body, frame}) =
    let
	    val stms = Canon.linearize body
      val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	    val instrs = List.concat(map (MipsCodegen.codegen frame) stms')
      val instrs' = F.procEntryExit2(frame, instrs)

      val (instrs'', allocation) = RegAlloc.alloc(instrs', frame)

      val {prolog, body=instrs''', epilog} = F.procEntryExit3(frame, instrs'')

      fun registerForTemp(temp) =
        case Temp.Table.look(allocation, temp) of
          SOME(register) => register
        | NONE => F.tempName(temp)

      val format0 = Assem.format(registerForTemp)
    in
      TextIO.output(out, prolog);
      app (fn i => TextIO.output(out,format0 i)) instrs''';
      TextIO.output(out, epilog)
    end
    
    | emitproc out (str as F.STRING(lab, s)) = TextIO.output(out, F.stringFrag(str))

  fun withOpenFile fname f = 
    let
      val (out, closeOut) =
        (TextIO.openOut fname, TextIO.closeOut)
      
    in
      (f out before closeOut out) 
	    handle e => (TextIO.closeOut out; raise e)
    end 

   fun compile filename = 
       let val absyn = Parse.parse filename
           val frags = (FindEscape.findEscape absyn; Semant.transProg absyn)

           (* Separate the .data fragments from the .text fragments *)
           val dataFrags = foldr
            (fn (frag, frags) =>
              case frag of
                F.STRING(_, _) => frag :: frags
              | _ => frags)
            (nil)
            (frags)

            val textFrags = foldr
              (fn (frag, frags) =>
                case frag of
                  F.PROC(_) => frag :: frags
                | _ => frags)
              (nil)
              (frags)
        in 
            withOpenFile
              (filename ^ ".s")
              (fn out =>
                (TextIO.output(out, ".data\n");
                 app (emitproc out) dataFrags;
                 TextIO.output(out, "\n\n.text\n");
                 app (emitproc out) textFrags))
       end

end



