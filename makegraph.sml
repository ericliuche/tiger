signature Makegraph = 
sig
  val instrs2graph : Assem.instr list ->
                Flow.flowgraph * Flow.Graph.node list
end

structure MakeGraph : Makegraph = 
struct
  structure FG = Flow.Graph

  fun instrs2graph asm =
    let 
      val flowGraph = Graph.newGraph()
      val nodes = map (fn _ => FG.newNode(flowGraph)) asm
      val nodeInstrs = ListPair.zip(nodes, asm)

      fun buildNodes((node, instr), (def, use, ismove, labelMap)) =
          case instr of
            Assem.OPER{assem, dst, src, jump} =>
              (FG.Table.enter(def, node, dst),
               FG.Table.enter(use, node, src),
               FG.Table.enter(ismove, node, false),
               labelMap)

          | Assem.MOVE{assem, dst, src} =>
              (FG.Table.enter(def, node, [dst]),
               FG.Table.enter(use, node, [src]),
               FG.Table.enter(ismove, node, true),
               labelMap)

          | Assem.LABEL{assem, lab} =>
              (FG.Table.enter(def, node, []),
               FG.Table.enter(use, node, []),
               FG.Table.enter(ismove, node, false),
               Symbol.enter(labelMap, lab, node))

      val init = (FG.Table.empty, FG.Table.empty, FG.Table.empty, Symbol.empty)
      val (def, use, ismove, labelMap) = foldl buildNodes init nodeInstrs

      fun buildEdges((node, Assem.OPER{assem, dst, src, jump=SOME(labels)}), nextNode) = 
        let 
          fun addEdge(label) = 
            case Symbol.look(labelMap, label) of 
              SOME(labelNode) => FG.mk_edge({from=node, to=labelNode})
            | NONE =>
                (* If we are jumping to an unknown label, it better be a different procedure. *)
                if String.isPrefix "jal" assem then
                  case nextNode of
                      SOME(n) => FG.mk_edge({from=node, to=n})
                    | NONE => ()
                else
                  (ErrorMsg.impossible "missing label")
        in
          (app addEdge labels;
           SOME(node))
        end
      | buildEdges((node, _), nextNode) = 
          (case nextNode of
            SOME(n) => FG.mk_edge({from=node, to=n})
          | NONE => ();
          SOME(node))

      val _ = foldr buildEdges NONE nodeInstrs
    in
       (Flow.FGRAPH{control=flowGraph, 
                    def=def, 
                    use=use,
                    ismove=ismove}, 
        nodes)
    end
end