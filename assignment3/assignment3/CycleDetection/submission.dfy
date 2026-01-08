// Please, before you do anything else, add your names here:
// Group:    8
// Member 1: Yuxin Wang: 2078937
// Member 2: Anusha Asthana: 2115174

include "assignment.dfy"

module Submission refines Assignment {
  class HasCycleAlgorithm extends AssignmentTrait {
    @TimeLimit(60)
    lemma ColorSumLemma(coloring: GraphColoring, u: Node)
      requires u in coloring
      ensures ColorSum(coloring) == ColorSum(coloring - {u}) + ColorValue(coloring[u]) 
    {
      var pivot :| pivot in coloring && ColorSum(coloring) == ColorValue(coloring[pivot]) + ColorSum(coloring - {pivot});

      if pivot == u {
      } else {
        var v := pivot;         
        ColorSumLemma(coloring - {v}, u);
        
        calc {
          ColorSum(coloring);
          ColorValue(coloring[v]) + ColorSum(coloring - {v});
          == { ColorSumLemma (coloring - {v}, u); }
          ColorValue(coloring[v]) + ColorValue(coloring[u]) + ColorSum(coloring - {v} - {u});
          == { assert coloring - {v} - {u} == coloring - {u} - {v}; }
          ColorValue(coloring[u]) + ColorValue(coloring[v]) + ColorSum(coloring - {u} - {v});
          == { ColorSumLemma (coloring - {u}, v); }
          ColorValue(coloring[u]) + ColorSum(coloring - {u});
        }
      }
    }
    // TODO: prove this lemma

    @TimeLimit(60)
    // If there is no cycle reachable from the successors of u, then there is
    // no cycle reachable from u.
    lemma CycleLemma(u: Node, G: Graph)
      requires u in G
      requires forall v: Node | v in G[u] :: !HasCycleFrom(v, G)
      ensures !HasCycleFrom(u, G) 
      {

        if HasCycleFrom(u, G) {
          var p, q, v :| IsPath(p, G) && IsPath(q, G) && v in G && IsLasso(u, v, p, q, G);
          if |p| == 1 {
            var w := q[1];
            var p2 := q[1..];
            calc {
              p[0] == u && p[|p|-1] == v;
              ==>
              |p2| == |q| - 1;
              ==>
              IsPath(p2, G);
              ==>
              IsLasso(w, u, p2, q, G);
              ==>
              HasCycleFrom(w, G);
              ==>
              w in G[u];
              ==> 
              false; 
              ==> 
              !HasCycleFrom(v, G);
            }
            
          } else {
            // |p| > 1 
            var v1 := p[1];
            var p2 := p[1..];
            assert |p2| == |p| - 1;
            assert IsPath(p2, G);
            assert IsLasso(v1, v, p2, q, G);
            assert HasCycleFrom(v1, G);
            assert v1 in G[u];
          }
          

        }
       // Needs to prove !HasCycleFrom(u, G) == true 
      }
    // TODO: prove this lemma

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
    {
      assume ColorSum(coloring[u := Gray]) < ColorSum(coloring);  // assume (1)
      coloring := coloring[u := Gray];

      var successors := G[u];

      var i: nat := 0;

      while i < |successors|
        invariant 0 <= i <= |successors|
        invariant call_stack == old(call_stack)
        invariant call_stack[|call_stack| - 1] == u
        invariant coloring.Keys == old(coloring.Keys)
        invariant forall v: Node | v in coloring.Keys :: ColorValue(coloring[v]) <= old(ColorValue(coloring[v]))
        invariant ColorValue(coloring[u]) < old(ColorValue(coloring[u]))
        invariant ColorSum(coloring) < ColorSum(old(coloring))
        invariant GrayNodesAreOnStack()
        invariant SuccessorsOfBlackNodesAreBlack(G, coloring)
        invariant forall v: Node | v in coloring.Keys :: coloring[v] == Black ==> !HasCycleFrom(v, G)
        invariant forall k | 0 <= k < i :: coloring[successors[k]] == Black
      {
        var v := successors[i];
        if coloring[v] == White
        {
          call_stack := call_stack + [v];
          var result := dfs(v);
          call_stack := call_stack[0 .. |call_stack| - 1];
          assume ColorSum(old(coloring)) < ColorSum(coloring);  // assume (2)
          if result
          {
            assume HasCycleFrom(u, G);  // assume (3)
            return true;
          }
        }
        else if coloring[v] == Gray
        {
          assume HasCycleFrom(u, G);  // assume (4)
          return true;
        }
        i := i + 1;
      }
      CycleLemma(u, G);

      assume ColorSum(coloring[u := Black]) <= ColorSum(coloring);  // assume (5)
      coloring := coloring[u := Black];

      return false;
    }

    @TimeLimit(60)
    method has_cycle() returns (found: bool)
      modifies this
      ensures found <==> HasCycle(G)
    {
      coloring := map u | u in G :: White;

      var nodes := G.Keys;
      while nodes != {}
        invariant coloring.Keys == G.Keys
          invariant nodes <= G.Keys
          
      {
        var u :| u in nodes;
        nodes := nodes - {u};
        if coloring[u] == White
        {
          call_stack := [u];
          found := dfs(u);
          if found
          {
            return true;
          }
        }
      }
      assume !HasCycle(G);  // assume (6)
      return false;
    }
  }
}
