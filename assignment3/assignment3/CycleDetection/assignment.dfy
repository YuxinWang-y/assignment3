module Predef {

  // 00: The type is non-empty.
  // ==: The type supports equality operators (== and !=).
  // !new: The type is value-based, meaning it is not allocated on the heap and represents immutable values.
  type Node(00,==,!new)

  // An edge is a pair of nodes (u, v).
  type Edge = (Node, Node)

  // The type Graph models a directed graph, that is stored using a mapping.
  // For a graph G = (V, E) we have `V == G.Keys` and `E = { (u, v) | u in G.Keys && v in G[u] }
  type Graph = G: map<Node, seq<Node>> | is_adjacency_list_graph(G)

  // An adjacency-list graph is valid when every listed neighbor is itself a node in the graph.
  ghost predicate is_adjacency_list_graph(G: map<Node, seq<Node>>)
  {
    forall u | u in G :: (forall v | v in G[u] :: v in G.Keys)
  }

  // A Path is a non-empty sequence of nodes.
  type Path = p: seq<Node> | |p| > 0 ghost witness path_witness()

  // A witness for non-empty sequences of nodes.
  ghost function path_witness(): seq<Node>
  {
    ghost var u: Node :| true; // an arbitrary node
    [u]
  }

  // A GraphColoring is a mapping that assign colors to nodes.
  datatype Color = Black | Gray | White
  type GraphColoring = map<Node, Color>

  // Assigns numbers to colors.
  ghost function ColorValue(c: Color): nat
  {
    match c
    case Black => 0
    case Gray => 1
    case White => 2
  }

  // The sum of the color values is used to prove termination.
  ghost function ColorSum(coloring: GraphColoring): nat
  {
    if |coloring| == 0
    then 0
    else
      var u: Node :| u in coloring;
      ColorValue(coloring[u]) + ColorSum(coloring - {u})
  }

  // There is a directed edge from u to v in G.
  ghost predicate IsEdge(u: Node, v: Node, G: Graph)
  {
    u in G && v in G[u]
  }

  // The sequence of nodes p is a path in the graph G.
  ghost predicate IsPath(p: Path, G: Graph)
  {
    forall i | 0 <= i < |p| - 1 :: IsEdge(p[i], p[i+1], G)
  }

  // The sequence of nodes p is a cycle in the graph G.
  ghost predicate IsCycle(p: Path, G: Graph)
  {
    IsPath(p, G) && |p| > 1 && p[0] == p[|p|-1]
  }

  // The graph G contains a cycle.
  ghost predicate HasCycle(G: Graph)
  {
    exists p: Path :: IsCycle(p, G)
  }

  // Successors of a black node are black.
  ghost predicate SuccessorsOfBlackNodesAreBlack(G: Graph, coloring: GraphColoring)
    requires coloring.Keys == G.Keys
  {
    forall u: Node | u in G :: coloring[u] == Black ==> forall v | v in G[u] :: coloring[v] == Black
  }

  // There is a lasso starting in u.
  ghost predicate HasLasso(u: Node, G: Graph)
  {
    exists p: Path, q: Path, v: Node | IsPath(p, G) && IsPath(q, G) && v in G :: IsLasso(u, v, p, q, G)
  }

  // Our witness for a cycle is a `lasso`, which consists of a path p from u to v,
  // followed by a cycle q from v to v.
  ghost predicate IsLasso(u: Node, v: Node, p: Path, q: Path, G: Graph)
  {
    IsPath(p, G) && IsCycle(q, G) && p[0] == u && p[|p|-1] == q[0] == v
  }

  // There is a lasso starting in u.
  ghost predicate HasCycleFrom(u: Node, G: Graph)
  {
    exists p: Path, q: Path, v: Node | IsPath(p, G) && IsPath(q, G) && v in G :: IsLasso(u, v, p, q, G)
  }

  trait GrayNodeTrait
  {
    const G: Graph
    var coloring: GraphColoring
    ghost var call_stack: Path  // The call stack of the recursion.

    // All gray nodes are contained in `call_stack`.
    ghost predicate GrayNodesAreOnStack()
      reads this
      requires coloring.Keys == G.Keys
    {
      forall u: Node | u in G :: coloring[u] == Gray ==> u in call_stack
    }
  }
}

abstract module Assignment refines Predef {
  trait AssignmentTrait extends GrayNodeTrait {

    @TimeLimit(60)
    // Removing a node from the coloring decreases the total color sum by exactly its color value.    
    // See also https://leino.science/papers/krml274.html.
    lemma ColorSumLemma(coloring: GraphColoring, u: Node)
      requires u in coloring
      ensures ColorSum(coloring) == ColorSum(coloring - {u}) + ColorValue(coloring[u])

    @TimeLimit(60)
    // If there is no cycle reachable from the successors of u, then there is
    // no cycle reachable from u.
    lemma CycleLemma(u: Node, G: Graph)
      requires u in G
      requires forall v: Node | v in G[u] :: !HasCycleFrom(v, G)
      ensures !HasCycleFrom(u, G)

    @TimeLimit(60)
    // Checks if there is a cycle in G in the nodes reachable from u.
    method dfs(u: Node) returns (found: bool)
      modifies this
      decreases ColorSum(coloring)
      requires u in G
      requires coloring.Keys == G.Keys
      requires coloring[u] == White
      requires |call_stack| > 0
      requires IsPath(call_stack, G)
      requires call_stack[|call_stack| - 1] == u
      requires GrayNodesAreOnStack()
      requires SuccessorsOfBlackNodesAreBlack(G, coloring)
      requires forall v: Node | v in G :: coloring[v] == Black ==> !HasCycleFrom(v, G)

      ensures coloring.Keys == old(coloring.Keys)
      ensures call_stack == old(call_stack)
      ensures forall v: Node | v in coloring.Keys :: ColorValue(coloring[v]) <= old(ColorValue(coloring[v]))
      ensures ColorValue(coloring[u]) < ColorValue(old(coloring)[u])
      ensures ColorSum(coloring) < ColorSum(old(coloring))
      ensures SuccessorsOfBlackNodesAreBlack(G, coloring)
      ensures forall v: Node | v in G :: coloring[v] == Black ==> !HasCycleFrom(v, G)
      ensures !found ==> GrayNodesAreOnStack()
      ensures !found ==> coloring[u] == Black
      ensures found <==> HasCycleFrom(u, G)

    @TimeLimit(60)
    // Checks if there is a cycle in G.
    method has_cycle() returns (found: bool)
      modifies this
      ensures found <==> HasCycle(G)
  }
}
