// Please, before you do anything else, add your names here:
// Group:    <Group number>
// Member 1: <Full name 1>: <Student number 1>
// Member 2: <Full name 2>: <Student number 2>

include "assignment.dfy"

module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong. 
    @TimeLimit(60)
    method Heapify(a: array<int>)
        // What would be a good method contract?
    {
        // Good luck!
    }

    // the root of a max-heap defined by a,h is the maximum of all heap elements
    @TimeLimit(60)
    lemma MaxHeapLemma(a: array<int>, h: int)
        //...
    {
        // Good luck!
    }

    // For full points, implement Heapsort and Unheapify
}
