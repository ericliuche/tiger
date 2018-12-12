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
  structure CodeGen = MipsCodegen

  (* Flag controlling whether debug messages are printed to standard out *)
  val DEBUG = false
  fun log(s) = if DEBUG then print(s) else ()

  type allocation = Frame.register Temp.Table.table

  fun alloc(instrs, frame): Assem.instr list * allocation =
    let

      (*******************************************

        Utilities for operating on sets/lists

      ********************************************)


      (* Filter the given list with the given predicate *)
      fun filter(head :: rest, pred) = if pred(head) then head :: filter(rest, pred) else filter(rest, pred)
        | filter(nil, pred) = nil

      (* Are the two move tuples equal disregarding order? *)
      fun moveEq((n1, n2), (n3, n4)) =
          (Graph.eq(n1, n3) andalso Graph.eq(n2, n4)) orelse
          (Graph.eq(n1, n4) andalso Graph.eq(n2, n3))

      (* Does the given list contain the given item using the given comparator? *)
      fun contains(head :: rest, item, eqOp) = eqOp(head, item) orelse contains(rest, item, eqOp)
        | contains(nil, item, eqOp) = false

      (* Does the given list of nodes contain the given node? *)
      fun containsNode(nodeList, node) = contains(nodeList, node, Graph.eq)

      (* Does the given list of moves contain the given move? *)
      fun containsMove(moveList, move) = contains(moveList, move, moveEq)

      (* Return the intersection of the two lists using the given comparator *)
      fun intersect(head1 :: rest1, list2, eqOp) =
            if contains(list2, head1, eqOp) then
              head1 :: intersect(rest1, list2, eqOp)
            else
              intersect(rest1, list2, eqOp)

        | intersect(nil, list2, eqOp) = nil

      (* Return the union of the two lists (without duplicates) *)
      fun union(head :: rest, other, eqOp) =
            if contains(other, head, eqOp) then union(rest, other, eqOp) else head :: union(rest, other, eqOp)

        | union(nil, other, eqOp) = other

      (* Remove all instances of the given item from the given list using the given comparator *)
      fun removeFromList(head :: rest, item, eqOp) =
            if eqOp(head, item) then
              removeFromList(rest, item, eqOp)
            else
              head :: removeFromList(rest, item, eqOp)
        | removeFromList(nil, item, eqOp) = nil


      (* Remove all instances of the given node from the given list of nodes *)
      fun removeNodeFromList(nodeList, node) = removeFromList(nodeList, node, Graph.eq)



      (*******************************************

        Initialization of the interference graph

      ********************************************)


      (* Construct a control flow graph and an interference graph *)
      val (flowGraph, flowGraphNodes) = MakeGraph.instrs2graph instrs
      val (igraph, liveOut) = Liveness.interferenceGraph flowGraph
      val igraphNodes = Graph.nodes((fn Liveness.IGRAPH{graph=graph, ...} => graph) igraph)
      val igraphMoves = (fn Liveness.IGRAPH{moves=moves, ...} => moves) igraph
      val igraphMoveNodes = foldr (fn ((n1, n2), moveList) => n1 :: n2 :: moveList) nil igraphMoves
      val igraphGtemp = (fn Liveness.IGRAPH{gtemp=gtemp, ...} => gtemp) igraph
      val igraphTnode = (fn Liveness.IGRAPH{tnode=tnode, ...} => tnode) igraph

      (* Create the initialization values for the move table and list from the interference graph *)
      val (igraphMoveTableInit, igraphMoveListInit) =
        foldr
          (fn (move as (n1, n2), (table, moveList)) =>
            let
              val n1List = case (Graph.Table.look(table, n1)) of
                             SOME(moveList) => moveList
                           | NONE => nil

              val n2List = case (Graph.Table.look(table, n2)) of
                             SOME(moveList) => moveList
                           | NONE => nil
            in
              (Graph.Table.enter(
                Graph.Table.enter(table, n1, move :: n1List),
                n2, move :: n2List),

              move :: moveList)
            end)
          ((Graph.Table.empty, nil))
          (igraphMoves)

      (* Interference graph moves as a node -> node list and a node list*)
      val igraphMoveList = ref igraphMoveListInit
      val igraphMoveTable = ref igraphMoveTableInit


      (* Print the interference graph *)
      val _ = if DEBUG then Liveness.show(TextIO.stdOut, igraph) else ()


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
        (fn (node, table) => 
          if containsNode(precolored, node) then
            Graph.Table.enter(table, node, union(removeFromList(precolored, node, Graph.eq), Graph.adj(node), Graph.eq))
          else
            Graph.Table.enter(table, node, Graph.adj(node)))
        (Graph.Table.empty)
        (igraphNodes))


      (* Return the name of the node and the associated temp as a string *)
      fun nodeAndTempName(node) =
        (Graph.nodename node) ^ " (" ^ (Frame.tempName (igraphGtemp node)) ^ ")"


      (* Stack of nodes to attempt to color *)
      val selectStack = ref []

      (* Nodes that have been coalesced *)
      val coalescedNodes = ref []
      val alias = ref (Graph.Table.empty)

      (* Nodes that have been spilled *)
      val spilledNodes = ref []

      (* Track nodes that have been colored and the colors assigned to them *)
      val coloredNodes = ref precolored
      val colors = ref precoloredMap


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

      (* Get the degree of the given node *)
      fun degree(node) =
        if containsNode(precolored, node) then 1000000 else (
        case Graph.Table.look(!degrees, node) of
          SOME(degree) => degree
        | NONE => ErrorMsg.impossible "Missing degree for node")


      (* Move lists - every move should always be in exactly on of these lists *)
      val coalescedMoves = ref []
      val constrainedMoves = ref []
      val frozenMoves = ref []
      val movesWL = ref igraphMoveListInit
      val activeMoves = ref []

      (* Get all of the moves that the given node is a part of *)
      fun nodeMoves(node) =
        let
          fun moveContainsNode((n1, n2)) = Graph.eq(n1, node) orelse Graph.eq(n2, node)

          val activeMovesForNode = filter(!activeMoves, moveContainsNode)
          val worklistMovesForNode = filter(!movesWL, moveContainsNode)
        in
          union(activeMovesForNode, worklistMovesForNode, moveEq)
        end


      (* Is the given node move related to any other node? *)
      fun moveRelated(node) = length(nodeMoves(node)) > 0

      (* Enable the moves for all nodes in the given list of nodes *)
      fun enableMoves(head :: rest) =
            let
              val moves = nodeMoves(head)
            in
              app
                (fn (move) =>
                  if containsMove(moves, move) andalso containsMove(!activeMoves, move) then
                    (activeMoves := removeFromList(!activeMoves, move, moveEq);
                     movesWL := move :: !movesWL)
                  else
                    ())
                (moves);

              enableMoves(rest)
            end

        | enableMoves(nil) = ()


      (* Initialize the spill, freeze, and simplify worklists *)
      fun makeWorklist(node :: rest, spillWL, freezeWL, simplifyWL) =
            if containsNode(precolored, node) then 
              makeWorklist(rest, spillWL, freezeWL, simplifyWL)
            else if degree(node) >= Frame.numReg then
              makeWorklist(rest, node :: spillWL, freezeWL, simplifyWL)
            else if moveRelated(node) then
              makeWorklist(rest, spillWL, node :: freezeWL, simplifyWL)
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
        (log("Setting color " ^ color ^ " for " ^ (nodeAndTempName node) ^ ")\n");

         colors := Temp.Table.enter(!colors, (igraphGtemp node), color);
         coloredNodes := node :: !coloredNodes)
        

      (* Decrement the degree of a single node *)
      fun decrementDegree(node) =
        let
          val d = degree(node)
        in
          degrees := Graph.Table.enter(!degrees, node, d - 1);
          if d = Frame.numReg then
            (enableMoves(node :: adjacent(node));
             spillWL := removeNodeFromList(!spillWL, node);

            if moveRelated(node) then
              freezeWL := node :: !freezeWL
            else
              simplifyWL := node :: !simplifyWL)
          else
            ()
        end


      (* Simplify the graph by removing a node of insignificant degree *)
      fun simplify() =
        case !simplifyWL of
          node :: rest =>
            (log("Adding " ^ (nodeAndTempName node) ^ " to select stack\n");

             simplifyWL := rest;
             selectStack := node :: !selectStack;

             app decrementDegree (adjacent node))

        | nil => ErrorMsg.impossible "Cannot simplify graph"



      (*******************************************

        Register coalescing logic

      ********************************************)


      (* Get the representative node if this node has been coalesced *)
      fun getAlias(node) =
        if containsNode(!coalescedNodes, node) then
          case (Graph.Table.look(!alias, node)) of
            SOME(nodeAlias) => getAlias(nodeAlias)
          | NONE => ErrorMsg.impossible "Missing alias for coalesced node"
        else
          node

      (* Coalesce two move-related temps into a single interference graph node *)
      fun coalesce() =
        case !movesWL of
          (move as (n1, n2)) :: rest =>
            let

              
              (* Is the given node precolored? *)
              fun isPrecolored(n) = Option.isSome(Temp.Table.look(precoloredMap, igraphGtemp n))

              (* Are the two given nodes adjacent to each other? *)
              fun isAdj(a, b) = containsNode(adjacent(a), b)

              val x = getAlias(n1)
              val y = getAlias(n2)

              val (u, v) =
                if isPrecolored(y) then
                  (y, x)
                else
                  (x, y)

              (* If the given frozen move can be simplified, move it to the simplify worklist *)
              fun addWorkList(n) =
                if not(isPrecolored(n)) andalso
                   not(moveRelated(n)) andalso
                   degree(n) < (Frame.numReg) then
                  
                  (freezeWL := removeNodeFromList(!freezeWL, n);
                   simplifyWL := n :: !simplifyWL)

                else
                  ()

              (* Add an interference edge between the two given nodes *)
              fun addEdge(u, v) =
                let
                  fun incrDegree(n) =
                    degrees := Graph.Table.enter(!degrees, n, degree(n) + 1)
                in
                  if not(isAdj(u, v)) andalso not(Graph.eq(u, v)) then
                    (log("Adding edge from " ^ (nodeAndTempName u) ^ " to " ^ (nodeAndTempName v));
                     
                    (if not(isPrecolored(u)) then
                      (adjList := Graph.Table.enter(!adjList, u, v :: adjacent(u));
                       incrDegree(u))
                    else
                      ());

                    (if not(isPrecolored(v)) then
                      (adjList := Graph.Table.enter(!adjList, v, u :: adjacent(v));
                       incrDegree(v))
                    else
                      ()))
                  else
                    ()
                end

              (* Combine the two given nodes into a single logical node for the interference graph *)
              fun combine(u, v) =
                let
                  val _ = log("Combining " ^ (nodeAndTempName u) ^ " and " ^ (nodeAndTempName v) ^ "\n")
                  val uMoves = Option.getOpt(Graph.Table.look(!igraphMoveTable, u), nil)
                  val vMoves = Option.getOpt(Graph.Table.look(!igraphMoveTable, v), nil)

                  (* Marks the given node as interfering with u from above *)
                  fun handleAdjacent(node) =
                    (addEdge(node, u); decrementDegree(node))

                in
                  ((if containsNode(!freezeWL, v) then
                    freezeWL := removeNodeFromList(!freezeWL, v)
                  else
                    spillWL := removeNodeFromList(!spillWL, v));

                  coalescedNodes := v :: !coalescedNodes;
                  alias := Graph.Table.enter(!alias, v, u);


                  (* nodeMoves[u] <- nodeMoves[u] U nodeMoves[v]*)
                  app
                    (fn ((n1, n2)) =>
                      let
                        val node = if Graph.eq(n1, v) then n2 else n1
                        val uMoves = Option.getOpt(Graph.Table.look(!igraphMoveTable, u), nil)
                      in
                        igraphMoveTable := Graph.Table.enter(!igraphMoveTable, u, (u, node) :: uMoves);
                        igraphMoveList := (u, node) :: (!igraphMoveList);
                        movesWL := (u, node) :: (!movesWL)
                      end)
                    vMoves;

                  app handleAdjacent (adjacent(v));

                  if degree(u) >= (Frame.numReg) andalso containsNode(!freezeWL, u) then
                    (freezeWL := removeNodeFromList(!freezeWL, u);
                     spillWL := u :: !spillWL)
                  else
                    ())
                end

              (* Return true if the heuristic for coalescing a precolored register is satisfied *)
              fun ok(t) =
                (degree(t) < Frame.numReg) orelse
                (isPrecolored(t)) orelse
                (isAdj(t, u))

              (* Return true if the conservative coalescing heuristic is satisfied *)
              fun conservative(nodes) =
                let
                  val K = Frame.numReg
                  val k =
                    foldr
                      (fn (node, count) => if degree(node) >= K then count + 1 else count)
                      (0)
                      (nodes)
                in
                  k < K
                end
            in
              movesWL := removeFromList(!movesWL, move, moveEq);
              (if Graph.eq(u, v) then
                (coalescedMoves := move :: !coalescedMoves;
                 addWorkList(u))

              else if isPrecolored(v) orelse isAdj(u, v) then
                (constrainedMoves := move :: !constrainedMoves;
                 addWorkList(u);
                 addWorkList(v))

              else if (isPrecolored(u) andalso
                      (foldr (fn (t, restIsOk) => restIsOk andalso ok(t)) (true) (adjacent(v)))) orelse
                      ((not (isPrecolored(u))) andalso
                      (conservative(union(adjacent(u), adjacent(v), Graph.eq)))) then
                (coalescedMoves := move :: !coalescedMoves;
                 combine(u, v);
                 addWorkList(u))


              else
                activeMoves := move :: !activeMoves)
            end 

        | _ => ErrorMsg.impossible "Cannot coalesce empty moves worklist"


      (* Freeze moves involving the given node to prevent its register from being coalesced *)
      fun freezeMoves(node) =
        let

          (* Mark the given move as frozen *)
          fun freezeMove(move as (x, y)) =
            let
              val yAlias = getAlias(y)
              val nodeAlias = getAlias(node)
              val v = if Graph.eq(yAlias, nodeAlias) then (getAlias x) else yAlias
            in
              activeMoves := removeFromList(!activeMoves, move, moveEq);
              frozenMoves := move :: !frozenMoves;

              if (length(nodeMoves(v)) = 0) andalso (degree(v) < (Frame.numReg)) then
                (freezeWL := removeNodeFromList(!freezeWL, v);
                 simplifyWL := v :: !simplifyWL)
              else
                ()
            end
        in
          app freezeMove (nodeMoves(node))
        end

      (* Process an entry fromthe freeze worklist and *)
      fun freeze() =
        case !freezeWL of
          node :: rest =>
            (freezeWL := rest;
             simplifyWL := node :: !simplifyWL;
             freezeMoves(node))
        | nil => ErrorMsg.impossible "Unable to freeze node with empty worklist"



      (*******************************************

        Register spilling logic

      ********************************************)


      (* Remove a spill candidate from the worklist and return it *)
      fun pickSpillCandidate() =
        let

          (* Calculate the cost of spilling a single node *)
          fun cost(node) =
            let
              val temp = igraphGtemp node

              (* Count the number of times a node is defined or used to determine its spill cost *)
              fun calcCost(head :: rest) =
                    (case head of
                      Assem.OPER{dst=dst, src=src, ...} =>
                        (if contains(dst, temp, op=) then 1 else 0) +
                        (if contains(src, temp, op=) then 1 else 0) +
                        calcCost(rest)
                    | Assem.MOVE{dst=dst, src=src, ...} =>
                        (if dst = temp then 1 else 0) +
                        (if src = temp then 1 else 0) +
                        calcCost(rest)
                    | Assem.LABEL{...} =>
                        calcCost(rest))

                | calcCost(nil) = 0
            in
              calcCost(instrs)
            end

          val costs = map cost (!spillWL)
          val nodesAndCosts = ListPair.zip(!spillWL, costs)

          (* Find the node with minimum cost in the spill worklist *)
          fun findMin((node, cost), (minNode, minCost)) =
            let 
              val scaledCost = Real.fromInt(cost) / Real.fromInt(degree node)
            in
              if minCost < scaledCost andalso minCost >= Real.fromInt(0) then
                (minNode, minCost)
              else
                (node, scaledCost)
            end

          val baseCase = (hd(!spillWL), Real.fromInt(~1))
          val (minNode, minCost) = foldr findMin baseCase nodesAndCosts

        in
          spillWL := removeNodeFromList(!spillWL, minNode);
          minNode
        end

      (* Select a spill candidate *)
      fun selectSpill() =
        let
          val node = pickSpillCandidate()
        in
          if not(containsNode(precolored, node)) then
            (simplifyWL := node :: !simplifyWL;
            freezeMoves(node))
          else
            ()
        end

      (* Rewrite the program be inserting appropriate load and store instructions for spilled temps *)
      fun rewriteProgram() =
        let

          val spilledTemps = map igraphGtemp (!spilledNodes)

          (* Allocate frame slots for all of the temps that we spilled *)
          val accesses = map
            (fn temp => (Frame.allocLocal(frame)(true)))
            spilledTemps

          (* Process an instruction list and insert appropriate loads and stores *)
          fun processInstrs(instr :: rest, temp, access) =
                (case instr of
                  Assem.OPER{dst=dst, src=src, assem=assem, jump=jump} =>

                    (* Insert store instructions after every def *)
                    (if contains(dst, temp, op=) then
                      let
                        val defTemp = Temp.newtemp()
                        val newDst = map (fn t => if t = temp then defTemp else t) dst
                      in
                        (Assem.OPER{dst=newDst, src=src, assem=assem, jump=jump} ::
                        CodeGen.codegen(frame)(Tree.MOVE(Frame.exp(access)(Tree.TEMP(Frame.FP)),
                                                         Tree.TEMP(defTemp)))) @
                        processInstrs(rest, temp, access)
                      end

                    (* Insert load instructions before every read *)
                    else if contains(src, temp, op=) then
                      let
                        val useTemp = Temp.newtemp()
                        val newSrc = map (fn t => if t = temp then useTemp else t) src
                      in
                        CodeGen.codegen(frame)(Tree.MOVE(Tree.TEMP(useTemp),
                                                         Frame.exp(access)(Tree.TEMP(Frame.FP)))) @
                        (Assem.OPER{dst=dst, src=newSrc, assem=assem, jump=jump} ::
                        processInstrs(rest, temp, access))
                      end

                    else
                      instr :: processInstrs(rest, temp, access))

                | Assem.MOVE{assem=assem, dst=dst, src=src} =>

                    (* Insert store instructions after a def via a move *)
                    (if dst = temp then
                      let
                        val defTemp = Temp.newtemp()
                      in
                        (Assem.MOVE{dst=defTemp, src=src, assem=assem} ::
                        CodeGen.codegen(frame)(Tree.MOVE(Frame.exp(access)(Tree.TEMP(Frame.FP)),
                                                         Tree.TEMP(defTemp)))) @
                        processInstrs(rest, temp, access)
                      end

                    (* Insert load instructions before a read via a move *)
                    else if src = temp then
                      let
                        val useTemp = Temp.newtemp()
                      in
                        CodeGen.codegen(frame)(Tree.MOVE(Tree.TEMP(useTemp),
                                                         Frame.exp(access)(Tree.TEMP(Frame.FP)))) @
                        (Assem.MOVE{dst=dst, src=useTemp, assem=assem} ::
                        processInstrs(rest, temp, access))
                      end

                    else
                      instr :: processInstrs(rest, temp, access))

                | _ => instr :: processInstrs(rest, temp, access))

            | processInstrs(nil, temp, access) = nil

        in
          foldr
            (fn ((temp, access), instrList) => processInstrs(instrList, temp, access))
            instrs
            (ListPair.zip(spilledTemps, accesses))
        end


      (*******************************************

        Color assignment logic

      ********************************************)

      (* Attempt to assign colors with the current selected stack *)
      fun assignColors() =
        case !selectStack of
          node :: rest =>
            let
              val okColors = ref (Frame.registerList((Frame.callersaves) @ (Frame.calleesaves)))

              val alreadyColored = Option.isSome(Temp.Table.look(!colors, (igraphGtemp node)))

              val _ = log("Finding OK colors for " ^ (nodeAndTempName node) ^ "\n")

              (*
                Update the list of okay colors for the current node by removing any colors already
                assigned to the given node or any node it is coalesced with
              *)
              fun updateOkColors(node) =
                let
                  val alias = getAlias(node)
                in
                  log("Alias for " ^ (nodeAndTempName node) ^ ": " ^ (nodeAndTempName alias) ^ "\n");

                  if containsNode(union(!coloredNodes, precolored, Graph.eq) , alias) then
                    (log("Removing color from OK list: " ^ (color(alias)) ^ "\n");

                    okColors := removeFromList(!okColors, color(alias), op=))

                  else
                    ()
                end

              val _ = log("Neighbors: " ^ (Int.toString(length(adjacent node))) ^ "\n")
              val _ = app updateOkColors (adjacent node)
            in
              selectStack := rest;
              
              (if length(!okColors) = 0 then
                (log("Spilling node " ^ (nodeAndTempName node) ^ "\n");

                 spilledNodes := node :: !spilledNodes)

              else if not alreadyColored then
                setColor(node, hd(!okColors))

              else
                log("Already colored " ^ (nodeAndTempName node) ^ "\n\n"));

              assignColors()
            end

        | nil =>
          (* Assign colors to all coalesced nodes *)
          app (fn node => setColor(node, color(getAlias(node)))) (!coalescedNodes)


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


      (* Filter unnecessary move instructions from the final assembly *)
      fun filterUnnecessaryMoves(head :: rest) =
            (case head of
              Assem.MOVE{src=src, dst=dst, ...} =>
                if (color(igraphTnode src)) = (color(igraphTnode dst)) then
                  filterUnnecessaryMoves(rest)
                else
                  head :: filterUnnecessaryMoves(rest)
            | _ => head :: filterUnnecessaryMoves(rest))

        | filterUnnecessaryMoves(nil) = nil


    in

      processWLs();
      assignColors();

      if length(!spilledNodes) > 0 then
        let
          val newInstrs = rewriteProgram()
        in
          alloc(newInstrs, frame)
        end

      else
        (filterUnnecessaryMoves instrs, !colors)

    end

end