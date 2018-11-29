signature REG_ALLOC = 
sig
    structure Frame: FRAME
    type allocation = Frame.register Temp.Table.table
    val alloc: Assem.instr list * Frame.frame -> Assem.instr list * allocation

end

signature COLOR = 
sig
    structure Frame: FRAME

    type allocation = Frame.register Temp.Table.table

    val color: {interference: Liveness.igraph,
                initial: allocation,
                spillCost: Graph.node -> int,
                registers: Frame.register list} -> allocation * Temp.temp list

end


structure RegAlloc: REG_ALLOC =
struct
  structure Frame = MipsFrame

  type allocation = Frame.register Temp.Table.table

  fun alloc(instrs, frame): Assem.instr list * allocation =
    let
      val (flowGraph, flowGraphNodes) = MakeGraph.instrs2graph instrs
      val (igraph, liveOut) = Liveness.interferenceGraph flowGraph
      val igraphNodes = Graph.nodes((fn Liveness.IGRAPH{graph=graph, ...} => graph) igraph)

      (* Get the degree of the given node *)
      fun degree(node) = length(Graph.adj(node))

      (* Is the given node move related to any other node? *)
      fun moveRelated(node) =
        let
          fun movesContains(node, (n1, n2) :: rest) =
                Graph.eq(node, n1) orelse Graph.eq(node, n2) orelse movesContains(node, rest)
            | movesContains(node, nil) = false
        in
          movesContains(node, (fn Liveness.IGRAPH{moves=moves, ...} => moves) igraph)
        end

      (* Initialize the spill, freeze, and simplify worklists *)
      fun makeWorklist(node :: rest, spillWL, freezeWL, simplifyWL) =
            if degree(node) >= Frame.numReg then
              makeWorklist(rest, node :: spillWL, freezeWL, simplifyWL)
            else if moveRelated(node) then
              makeWorklist(rest, spillWL, node :: freezeWL, simplifyWL)
            else
              makeWorklist(rest, spillWL, freezeWL, node :: simplifyWL)

        | makeWorklist(nil, spillWL, freezeWL, simplifyWL) =
            (spillWL, freezeWL, simplifyWL)


      (* Calculate the initial values for the worklists *)
      val (spillWLInit, freezeWLInit, simplifyWLInit) = makeWorklist(igraphNodes, [], [], []) 
      
      val spillWL = ref spillWLInit
      val freezeWL = ref freezeWLInit
      val simplifyWL = ref simplifyWLInit

      fun processWLs() =
        if length(!simplifyWL) > 0 then
          (* Simplify a node *)
          processWLs()
        else if length(!freezeWL) > 0 then
          (* Freeze a node *)
          processWLs()
        else if length(!spillWL) > 0 then
          (* Select a spill candidate *)
          processWLs()

        (* TODO: add check for moves worklist *)

        else
          (* Nothing was done this iteration, so don't recurse *)
          ()

    in
      print("Constructed worklists");
      processWLs();
      (instrs, Temp.Table.empty)
    end

end