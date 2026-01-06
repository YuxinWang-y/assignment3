module Predef {
  // a is sorted from lo (inclusive) to hi (exclusive)
  predicate sorted(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
  {
    forall j, k :: lo <= j < k < hi ==> a[j] <= a[k]
  }

  // is a max-heap up to excluding index h
  predicate isMaxHeap(a: array<int>, h: int)
    requires 0 < h <= a.Length
    reads a
  {
    forall i :: 0 < i < h ==> a[parent(i)] >= a[i]
  }

  // Parent node id in the tree
  function parent(i: nat) : int {
    (i - 1) / 2
  }

  // Left child id in the tree
  function lchild(i: nat) : nat
    ensures parent(lchild(i)) == i
  {
    2 * i + 1
  }

  // Right child id in the tree.
  function rchild(i: nat) : nat
    ensures parent(rchild(i)) == i
  {
    2 * i + 2
  }

  // a[mx] is the maximum of a[0..n]
  predicate max(a: seq<int>, n: int, mx: int)
    requires 0 <= mx < n <= |a|
  {
    forall i :: 0 <= i < n ==> a[i] <= a[mx]
  }

  // swap the elements at i and j in a
  method Swap(a: array<int>, i: int, j: int)
    modifies a
    requires 0 <= i < j < a.Length
    // requires 0 <= i < a.Length && 0 <= j < a.Length
    // requires i != j
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
    ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
    ensures multiset(a[..]) == old(multiset(a[..]))
  {
    a[i], a[j] := a[j], a[i];
  }
}

abstract module Assignment {
  import opened Predef

  // the root of a max-heap defined by a,h is the maximum of all heap elements
  @TimeLimit(60)
  lemma MaxHeapLemma(a: array<int>, h: int)
    requires 0 < h <= a.Length
    requires isMaxHeap(a, h)
    ensures max(a[..], h, 0)

  @TimeLimit(60)
  method HeapSort(a: array<int>)
    modifies a
    requires a.Length > 0
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures sorted(a, 0, a.Length)

  // Turn `a` into a sorted array by putting the head of `a` to the end,
  // inserting the last element of the heap at the top and bubbling it down.
  // @Axiom
  method {:verify true} UnHeapify(a: array<int>)
    modifies a
    requires a.Length > 0
    requires isMaxHeap(a, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures sorted(a, 0, a.Length)
}
