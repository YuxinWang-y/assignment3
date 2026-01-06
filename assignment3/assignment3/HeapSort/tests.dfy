include "submission.dfy"

abstract module Tests {
    import Predef
    import Submission

// No tests

    // @TimeLimit(60)
    // method HeapSort(a: array<int>)
    //     modifies a
    //     requires a.Length > 0
    //     ensures multiset(a[..]) == multiset(old(a[..]))
    //     ensures Predef.sorted(a, 0, a.Length)
    // {
    //     Submission.Heapify(a);
    //     Predef.UnHeapify(a);
    // }
}
