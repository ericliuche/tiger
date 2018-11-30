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

      (* Does the given list of nodes contain the given node? *)
      fun containsNode(head :: rest, node) = Graph.eq(head, node) orelse containsNode(rest, node)
        | containsNode(nil, node) = false

      (* Remove all instances of the given item from the given list using the given comparator *)
      fun removeFromList(head :: rest, item, eqOp) =
            if eqOp(head, item) then
              removeFromList(rest, item, eqOp)
            else
              head :: removeFromList(rest, item, eqOp)
        | removeFromList(nil, item, eqOp) = nil


      (* Remove all instances of the given node from the given list of nodes *)
      fun removeNodeFromList(nodeList, node) = removeFromList(nodeList, node, Graph.eq)

      (* Construct a control flow graph and an interference graph *)
      val (flowGraph, flowGraphNodes) = MakeGraph.instrs2graph instrs
      val (igraph, liveOut) = Liveness.interferenceGraph flowGraph
      val igraphNodes = Graph.nodes((fn Liveness.IGRAPH{graph=graph, ...} => graph) igraph)
      val igraphMoves = foldr (fn (node, moveList) => node :: moveList) nil igraphNodes
      val igraphGtemp = (fn Liveness.IGRAPH{gtemp=gtemp, ...} => gtemp) igraph

      (* Print the interference graph *)
      val _ = Liveness.show(TextIO.stdOut, igraph)


      (* Track which temps have been assigned colors already and which nodes they correspond to *)
      val precoloredMap = Frame.tempMap
      val precolored = foldr
        (fn (node, precoloredList) =>
          case Temp.Table.look(precoloredMap, (igraphGtemp node)) of
            SOME(register) => node :: precoloredList
          | NONE => precoloredList)

        (nil)
        (igraphNodes)

      (* Lookup table for current degree of a node *)
      val degrees = ref (foldr
        (fn (node, table) => Graph.Table.enter(table, node, length(Graph.adj(node))))
        (Graph.Table.empty)
        (igraphNodes))

      (* Adjacency list representation for the interference graph *)
      val adjList = ref (foldr
        (fn (node, table) => Graph.Table.enter(table, node, (Graph.adj(node))))
        (Graph.Table.empty)
        (igraphNodes))

      (* Get the degree of the given node *)
      fun degree(node) =
        case Graph.Table.look(!degrees, node) of
          SOME(degree) => degree
        | NONE => ErrorMsg.impossible "Missing degree for node"

      (* Is the given node move related to any other node? *)
      fun moveRelated(node) =
        let
          fun movesContains(node, (n1, n2) :: rest) =
                Graph.eq(node, n1) orelse Graph.eq(node, n2) orelse movesContains(node, rest)
            | movesContains(node, nil) = false
        in
          movesContains(node, (fn Liveness.IGRAPH{moves=moves, ...} => moves) igraph)
        end

      (* Return the name of the node and the associated temp as a string *)
      fun nodeAndTempName(node) =
        (Graph.nodename node) ^ " (" ^ (Frame.tempName (igraphGtemp node)) ^ ")"

      (* Initialize the spill, freeze, and simplify worklists *)
      fun makeWorklist(node :: rest, spillWL, freezeWL, simplifyWL) =
            if degree(node) >= Frame.numReg then
              makeWorklist(rest, node :: spillWL, freezeWL, simplifyWL)
            (*else if moveRelated(node) then
              makeWorklist(rest, spillWL, node :: freezeWL, simplifyWL)*)
            else
              makeWorklist(rest, spillWL, freezeWL, node :: simplifyWL)

        | makeWorklist(nil, spillWL, freezeWL, simplifyWL) =
            (spillWL, freezeWL, simplifyWL)


      (* Calculate the initial values for the worklists *)
      val (spillWLInit, freezeWLInit, simplifyWLInit) = makeWorklist(igraphNodes, [], [], [])
      
      (* Worklists to track nodes to take action upon *)
      val spillWL = ref spillWLInit
      val freezeWL = ref freezeWLInit
      val simplifyWL = ref simplifyWLInit
      val movesWL = ref igraphMoves

      (* Stack of nodes to attempt to color *)
      val selectStack = ref []

      (* Nodes that have been coalesced *)
      val coalescedNodes = ref []

      (* Track nodes that have been colored and the colors assigned to them *)
      val coloredNodes = ref []
      val colors = ref precoloredMap

      (* Get the color associated with the given node *)
      fun color(node) =
        let
          val temp = igraphGtemp node
        in
          case Temp.Table.look(!colors, temp) of
            SOME(register) => register
          | NONE => ErrorMsg.impossible ("Missing color for node " ^ (nodeAndTempName node))
        end

      (* Set the given color for the given node *)
      fun setColor(node, color) =
        (print("Setting color " ^ color ^ " for " ^ (nodeAndTempName node) ^ ")\n");
         colors := Temp.Table.enter(!colors, (igraphGtemp node), color);
         coloredNodes := node :: !coloredNodes)
        (* TODO: also assign colors for nodes coalesced with this one *)
        
      (* Get the nodes that are adjecent to the given node that have not been stacked or coalesced *)
      fun adjacent(node) =
        case Graph.Table.look(!adjList, node) of
          SOME(adj) =>
            let
              (* Build an adjacency list with all nodes that have not been selected or coalesced *)
              fun buildAdj(head :: rest) =
                    if containsNode(!selectStack, head) orelse containsNode(!coalescedNodes, head) then
                      buildAdj(rest)
                    else
                      head :: buildAdj(rest)

                | buildAdj(nil) = nil
            in
              buildAdj(adj)
            end
        | NONE => ErrorMsg.impossible "Missing adjList entry for node"


      (* Simplify the graph by removing a node of insignificant degree *)
      fun simplify() =
        let

          fun enableMoves(node) = () (* TODO: handle moves for coalescing *)

          (* Decrement the degree of a single node *)
          fun decrementDegree(node) =
            let
              val d = degree(node)
            in
              print("Decrementing degree of " ^ (nodeAndTempName node) ^ " to " ^ (Int.toString (d - 1)) ^"\n");
              degrees := Graph.Table.enter(!degrees, node, d - 1);
              if d = Frame.numReg then
                (enableMoves(node :: adjacent(node));
                 spillWL := removeNodeFromList(!spillWL, node);

                 (* TODO: uncomment when ready to handle move-related coalescing logic *)
                 (*if moveRelated(node) then
                  freezeWL := node :: !freezeWL
                 else*)
                  simplifyWL := node :: !simplifyWL)
              else
                ()
            end
        in
          case !simplifyWL of
            node :: rest =>
              (print("Adding " ^ (nodeAndTempName node) ^ " to select stack\n");
               simplifyWL := rest;
               selectStack := node :: !selectStack;

               app decrementDegree (adjacent node))

          | nil => ErrorMsg.impossible "Cannot simplify graph"
        end

      (* Get the representative node if this node has been coalesced *)
      fun getAlias(node) =
        (* TODO: necessary for when nodes get coalesced *)
        node

      fun coalesce() = (print("Coalescing\n"); movesWL := [])

      fun freeze() = (print("Freezing\n"); freezeWL := [])

      fun selectSpill() = print("Selecting spill candidate\n")

      (* Attempt to assign colors with the current selected stack *)
      fun assignColors() =
        case !selectStack of
          node :: rest =>
            let
              val okColors = ref (Frame.registerList(
                (Frame.callersaves) @ (Frame.calleesaves) @ (Frame.argregs) @ (Frame.specialregs)))

              val alreadyColored = Option.isSome(Temp.Table.look(!colors, (igraphGtemp node)))

              fun updateOkColors(node) =
                let
                  val alias = getAlias(node)
                in
                  if containsNode(!coloredNodes @ precolored , alias) then
                    okColors := removeFromList(!okColors, color(alias), op=)
                  else
                    ()
                end

              val _ = app updateOkColors (adjacent node)
            in
              selectStack := rest;
              
              (if length(!okColors) = 0 then
                (*TODO: spill nodes*)
                ErrorMsg.impossible "Unable to allocate with spilling nodes"
              else if not alreadyColored then
                setColor(node, hd(!okColors))
              else
                print("Already colored " ^ (nodeAndTempName node) ^ "\n"));

              assignColors()
            end

        | nil => ()

      (* Loop until all worklists are empty *)
      fun processWLs() =
        if length(!simplifyWL) > 0 then
          (* Simplify a node *)
          (simplify(); processWLs())

        else if length(!movesWL) > 0 then
          (* Coalesce a node *)
          (coalesce(); processWLs())

        else if length(!freezeWL) > 0 then
          (* Freeze a node *)
          (freeze(); processWLs())

        else if length(!spillWL) > 0 then
          (* Select a spill candidate *)
          (selectSpill(); processWLs())

        else
          (* Nothing was done this iteration, so don't recurse *)
          ()

    in
      processWLs();
      assignColors();
      (instrs, !colors)
    end

end