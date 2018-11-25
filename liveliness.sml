signature LIVENESS = 
sig
  datatype igraph = 
    IGRAPH of {graph: Graph.graph,
               tnode: Temp.temp -> Graph.node,
               gtemp: Graph.node ->Temp.temp,
               moves: (Graph.node * Graph.node) list}

  val interferenceGraph : 
      Flow.flowgraph ->
        igraph * (Graph.node -> Temp.temp list)

  val show : TextIO.outstream * igraph -> unit
end

structure Liveness : LIVENESS = 
struct
  structure FG = Flow.Graph

  datatype igraph = 
    IGRAPH of {graph: Graph.graph,
               tnode: Temp.temp -> Graph.node,
               gtemp: Graph.node ->Temp.temp,
               moves: (Graph.node * Graph.node) list}

  fun interferenceGraph(fg as Flow.FGRAPH{control, def, use, ismove}) =
    let      
      val nodes = Graph.nodes control

      fun findOrErrorGraph(table, node) = 
        case Graph.Table.look(table, node) of
          SOME(v) => v
        | NONE => ErrorMsg.impossible "missing node"

      fun findOrErrorTemp(table, temp) = 
        case Temp.Table.look(table, temp) of
          SOME(v) => v
        | NONE => ErrorMsg.impossible "missing temp"

      fun findOneOrErrorGraph(table, node) = 
        case findOrErrorGraph(table, node) of
          item::[] => item
        | item::items => ErrorMsg.impossible "expected one item"
        | [] => ErrorMsg.impossible "no items"

      fun liveness(liveIn, liveOut) = 
        let
          fun updateNode(node, (liveIn, liveOut, fixPoint)) = 
            let
              val inSet = findOrErrorGraph(liveIn, node)              
              val outSet = findOrErrorGraph(liveOut, node)
              val useSet = Temp.Set.addList(Temp.Set.empty, findOrErrorGraph(use, node))
              val defSet = Temp.Set.addList(Temp.Set.empty, findOrErrorGraph(def, node))

              val inSet' = 
                Temp.Set.union(
                  Temp.Set.union(inSet, useSet), 
                  Temp.Set.difference(outSet, defSet))

              val outSet' = Temp.Set.union(outSet,
                foldl 
                (fn (node, succIns) => Temp.Set.union(succIns, findOrErrorGraph(liveIn, node))) 
                (Temp.Set.empty) 
                (FG.succ node))
            in
              (Graph.Table.enter(liveIn, node, inSet'),
               Graph.Table.enter(liveOut, node, outSet'),
               fixPoint andalso Temp.Set.equal(inSet, inSet') andalso Temp.Set.equal(outSet, outSet'))
            end

          fun updateNodes(liveIn, liveOut) = 
            foldl updateNode (liveIn, liveOut, true) nodes

          val (liveIn', liveOut', fixPoint) = updateNodes(liveIn, liveOut)
        in 
          if fixPoint then 
            (liveIn', liveOut')
          else
            liveness(liveIn', liveOut')
        end

      fun initLiveSet() = 
        foldl 
        (fn (node, table) => (Graph.Table.enter(table, node, Temp.Set.empty)))
        Graph.Table.empty 
        nodes

      val (liveIn, liveOut) = liveness(initLiveSet(), initLiveSet())
      val iGraph = Graph.newGraph()

      fun addNode(node, (tempToNode, nodeToTemp)) = 
        let
          fun addTemp(temp, (tempToNode, nodeToTemp)) = 
            case Temp.Table.look(tempToNode, temp) of
              SOME(_) => (tempToNode, nodeToTemp)
            | NONE =>
                let
                  val interferenceNode = Graph.newNode(iGraph)
                in
                  (Temp.Table.enter(tempToNode, temp, interferenceNode),
                   Graph.Table.enter(nodeToTemp, interferenceNode, temp))
                end
        in
          foldl 
          addTemp
          (tempToNode, nodeToTemp)
          (findOrErrorGraph(use, node) @ findOrErrorGraph(def, node))
        end

      val (tempToNode, nodeToTemp) = foldl addNode (Temp.Table.empty, Graph.Table.empty) nodes

      fun addInterference(node, moves) = 
        let
          val isMove = findOrErrorGraph(ismove, node)
          val liveOuts = Temp.Set.listItems(findOrErrorGraph(liveOut, node))

          fun addEdge(def, out::rest, false) =
            (if def <> out then
              Graph.mk_edge({from=findOrErrorTemp(tempToNode, def), 
                             to=findOrErrorTemp(tempToNode, out)})
             else
              ();
             addEdge(def, rest, false))

          | addEdge(def, out::rest, true) =
            (if def <> out andalso findOneOrErrorGraph(use, node) <> out then
              Graph.mk_edge({from=findOrErrorTemp(tempToNode, def), 
                             to=findOrErrorTemp(tempToNode, out)})
             else
              ();
            addEdge(def, rest, true))

          | addEdge(def, [], _) = ()
        in
          (app (fn def => addEdge(def, liveOuts, isMove)) (findOrErrorGraph(def, node));
           if isMove then
             (findOrErrorTemp(tempToNode, findOneOrErrorGraph(def, node)),
              findOrErrorTemp(tempToNode, findOneOrErrorGraph(use, node))) :: moves
           else
             moves)
        end

      val moves = foldl addInterference [] nodes
    in
      (IGRAPH{graph=iGraph,
              tnode=(fn temp => findOrErrorTemp(tempToNode, temp)),
              gtemp=(fn node => findOrErrorGraph(nodeToTemp, node)),
              moves=moves},
       (fn node => Temp.Set.listItems(findOrErrorGraph(liveOut, node))))
    end

  fun show(out, IGRAPH{graph, tnode, gtemp, moves}) =
    let
      fun printTemp(temp) = TextIO.output(out, "t" ^ Int.toString(temp))
      
      fun printString(str) = TextIO.output(out, str)

      fun printNode(node) = 
        (printTemp(gtemp node);
         printString(":\n\t");
          (foldl 
           (fn (t, _) => (printTemp(t); printString(","))) 
           () 
           (map gtemp (Graph.adj node)));
         printString("\n"))

      fun printMove(node1, node2) = 
        (printTemp(gtemp node1);
         printString(" - ");
         printTemp(gtemp node2);
         printString("\n"))
    in
      (printString("interference graph: \n");
       app printNode (Graph.nodes graph);
       printString("moves: \n");
       app printMove moves)
    end
end