// Please, before you do anything else, add your names here:
// Group:    8
// Member 1: Yuxin Wang: 2078937
// Member 2: Anusha Asthana: 2115174

include "assignment.dfy"

module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong. 
    @TimeLimit(60)
    // turns array a into a max heap, so it should fill up left to right
    // bubble each new element upwards until the max heap property holds
    // for all i, Parent[i].key >= i.key
    method Heapify(a: array<int>)
        // What would be a good method contract?
        modifies a    
        requires a.Length > 0
        ensures isMaxHeap(a, a.Length)
        ensures multiset(a[..]) == multiset(old(a[..]))
    {
        var i := 1;
        while i < a.Length
            invariant 1 <= i <= a.Length
            // NOT ABLE TO PROVE: 
            invariant isMaxHeap(a, i)
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            var j := i;
            while j > 0 && a[parent(j)] < a[j]
                invariant 0 <= j <= i
                // NOT ABLE TO PROVE: 
                invariant isMaxHeap(a, i)
                invariant multiset(a[..]) == multiset(old(a[..]))
            {
                Swap(a, parent(j), j);
                j := parent(j);
            }

            i := i + 1;
        }        
    }

    // the root of a max-heap defined by a,h is the maximum of all heap elements
    @TimeLimit(60)
    lemma MaxHeapLemma(a: array<int>, h: int)
        // first element is the max of the max-heap
        ensures max(a[..], h, 0)
    {
        assume 0 < h <= a.Length;
        assume isMaxHeap(a, h);

        var i := 0;
        while i < h 
            invariant 0 <= i <= h
            invariant forall k :: 0 <= k < i ==> a[k] <= a[0]
        {
            if i != 0 {
                var j := i;
                while j != 0
                    invariant 0 <= j < h
                    invariant a[i] <= a[j]
                {
                    assert a[parent(j)] >= a[j];
                    j := parent(j);
                }
            }
            i := i + 1;
        }
    }

    // make array into a max-heap, 
    // then use unheapify to make it into a sorted array
    method Heapsort(a: array<int>) 
        modifies a
        requires a.Length > 0
        ensures sorted(a, 0, a.Length)
        ensures multiset(a[..]) == multiset(old(a[..]))
    {
        Heapify(a);
        Unheapify(a);
    }

    // take a max-heap and make it into a sorted array
    // swap the first element with the last element (in-place)
    // re-establish heap by bubbling first element down
    // now consider heap running from 0 to n-1
    method Unheapify(a: array<int>)
        modifies a
        requires a.Length > 0
        requires isMaxHeap(a, a.Length)
        ensures sorted(a, 0, a.Length)
        ensures multiset(a[..]) == multiset(old(a[..]))
    {
        var h := a.Length;
        while h > 1
            invariant 1 <= h <= a.Length
            invariant isMaxHeap(a, h)
            invariant sorted(a, h, a.Length)
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            Swap(a, 0, h-1);
            h := h - 1;

            var i := 0;
            while lchild(i) < h
                invariant 0 <= i < h
                invariant isMaxHeap(a, h)
                invariant multiset(a[..]) == multiset(old(a[..]))
            {
                var m := lchild(i);
                if rchild(i) < h && a[rchild(i)] > a[m]
                {
                    m := rchild(i);
                }

                if a[i] < a[m]
                {
                    Swap(a, i, m);
                    i := m;

                } else {
                    break;
                }

            }
        }

        assert h == 1;
        assert isMaxHeap(a, 1);
        MaxHeapLemma(a, 1);
    }

}
