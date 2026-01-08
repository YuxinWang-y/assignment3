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
              w in G[u] && HasCycleFrom(w, G);
              ==>
              !HasCycleFrom(w, G) && HasCycleFrom(w, G);
              ==>
              false; 
              ==> 
              !HasCycleFrom(u, G);
            }
            
          } else {
            // |p| > 1 
            var v1 := p[1];
            var p2 := p[1..];
            calc {
              |p2| == |p| - 1;
              ==>
              IsPath(p2, G);
              ==>
              IsLasso(v1, v, p2, q, G);
              ==>  
              v1 in G[u] && HasCycleFrom(v1, G);
              ==> 
              !HasCycleFrom(v1, G) && HasCycleFrom(v1, G);
              ==>
              false 
              ==> 
              !HasCycleFrom(v, G);
            }
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
      //assume ColorSum(coloring[u := Gray]) < ColorSum(coloring);  // assume (1)
      ghost var old_coloring := coloring;
      assert coloring[u] == White;
      ColorSumLemma(coloring, u);
      coloring := coloring[u := Gray];
      ColorSumLemma(coloring, u);
      ColorSumLemma(old_coloring, u);
      assert (old_coloring - {u}) == (coloring - {u});

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
          
          if result
          {
            CycleLemma(u, G);
            // assume (3)
            ghost var w_v, p_v, q_v :| IsLasso(v, w_v, p_v, q_v, G);

            var p_u := [u] + p_v;
            var w_u := w_v;
            var q_u := q_v;

            assert IsPath(p_u, G);
            assert IsPath(q_u, G);
            assert IsLasso(u, w_u, p_u, q_u, G);
  
            return true;
          }
        }
        else if coloring[v] == Gray
        {
          CycleLemma(u, G);
          ghost var idx :| 0 <= idx < |call_stack| && call_stack[idx] == v;

          ghost var w := u;
          ghost var p_to_w := [u];
  
  
          ghost var q_cycle := [u];
  
          q_cycle := q_cycle + [v];
          
          if idx + 1 < |call_stack| {
            q_cycle := q_cycle + call_stack[idx+1..];
          }
  
          assert IsPath(p_to_w, G);
          assert IsPath(q_cycle, G);
          assert IsLasso(u, w, p_to_w, q_cycle, G);  // assume (4)
          return true;
        }
        i := i + 1;
      }
      CycleLemma(u, G);

      //assume ColorSum(coloring[u := Black]) <= ColorSum(coloring);  // assume (5)
      
      ColorSumLemma(coloring, u);
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
        invariant SuccessorsOfBlackNodesAreBlack(G, coloring)
        invariant forall v: Node | v in G :: coloring[v] == White || coloring[v] == Black
        invariant forall v: Node | v in G :: coloring[v] == Black ==> !HasCycleFrom(v, G)
        invariant forall v: Node | v in (G.Keys - nodes) :: coloring[v] == Black
        decreases |nodes| 
        

          
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
