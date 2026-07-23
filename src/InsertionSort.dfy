// Copyright (C) 2026 Adam McKellar <dev@mckellar.eu>
// 
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.


/*/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\

  Verified Insertion Sort in Dafny

  This file contains a verified implementation of insertion sort in the programming language Dafny.
  The algorithm itself strictly follows the pseudocode available at <https://en.wikipedia.org/wiki/Insertion_sort>.
  While the algorithm itself is simple, the verification was quite a torture. The verification of 
  `InsertionSortInnerLoop` is somewhat variable.

  Dafny v4.11.0 was used for writing this code. To verify this code execute dafny with:

    dafny verify --standard-libraries --cores 100% --resource-limit 3000000 InsertionSort.dfy
  

/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\*/



/*/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\

  Verified Insertion Sort in Dafny

  This module contains methods that check the size of the input array or slice and either call a bounded variant of 
  the algorithm, where the indices are bounded by `UINT32_MAX`, or the unbounded variant. In practice, the bounded 
  variant will always be called, as an array bounded by `UINT32_MAX` is quite large.

/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\*/

module InsertionSortAdaptive {
  import opened Std.Relations
  import Std.Collections.Seq
  import opened Std.BoundedInts
  import InsertionSortBoundedU32
  import InsertionSortUnbounded

  // Sort part of an array (`a[lo..hi]`) with insertion sort.
  method InsertionSortSubarrayBy<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
    modifies a
    requires TotalOrdering(leq)
    requires lo <= hi <= a.Length
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(leq, a[lo..hi])
  {
    if a.Length <= UINT32_MAX as int {
      InsertionSortBoundedU32.InsertionSortSubarrayBy(leq, a, lo as uint32, hi as uint32);
    } else {
      InsertionSortUnbounded.InsertionSortSubarrayBy(leq, a, lo, hi);
    }
  }

  // Sort an array with insertion sort.
  method InsertionSortArrayBy<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>)
    modifies a
    requires TotalOrdering(leq)
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(leq, a[..])
  {
    if a.Length <= UINT32_MAX as int {
      InsertionSortBoundedU32.InsertionSortArrayBy(leq, a);
    } else {
      InsertionSortUnbounded.InsertionSortArrayBy(leq, a);
    }
  }

  // Returns a with insertion sort sorted sequence.
  method InsertionSortSeqBy<A(!new, ==)>(leq: (A, A) -> bool, a: seq<A>) returns (r: seq<A>)
    requires TotalOrdering(leq)
    ensures multiset(a) == multiset(r)
    ensures SortedBy(leq, r)
  {
    if |a| <= UINT32_MAX as int {
      r := InsertionSortBoundedU32.InsertionSortSeqBy(leq, a);
    } else {
      r := InsertionSortUnbounded.InsertionSortSeqBy(leq, a);
    }
  }
}


/*/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\

  Verified Insertion Sort in Dafny with Unbounded Arrays

  This module contains the verified insertion sort implementation where indices use the `nat` type.

/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\*/

module InsertionSortUnbounded {
  import opened Std.Relations
  import Std.Collections.Seq

  // Implementation details of the inner loop.
  module InsertionSortInnerLoopImpl {
    import opened Std.Relations

    lemma SortedPrefix<A(!new)>(leq: (A, A) -> bool, p: seq<A>, a: seq<A>)
      requires p <= a
      requires TotalOrdering(leq)
      requires SortedBy(leq, a)
      ensures SortedBy(leq, p)
    {}

    lemma CombineSort<A(!new)>(leq: (A, A) -> bool, pre: seq<A>, x: A, post: seq<A>)
      requires TotalOrdering(leq)
      requires SortedBy(leq, pre)
      requires SortedBy(leq, post)
      requires forall i | 0 <= i < |pre| :: leq(pre[i], x)
      requires forall i | 0 <= i < |post| :: leq(x, post[i])
      ensures SortedBy(leq, pre + [x] + post)
    {}

    method {:isolate_assertions} InsertionSortInnerLoop<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, i: nat)
      modifies a
      requires TotalOrdering(leq)
      requires lo < i < a.Length
      requires SortedBy(leq, a[lo..i])
      ensures SortedBy(leq, a[lo..i+1])
      ensures multiset(a[..]) == multiset(old(a[..]))
    {
      var x := a[i];
      var j := i;

      ghost var snap := a[..];
      SortedPrefix(leq, a[lo..j], snap[lo..i]);

      while j > lo && !leq(a[j-1], x)
        invariant lo <= j <= i < a.Length
        invariant a[..j+1] == snap[..j+1]
        invariant a[i+1..] == snap[i+1..]
        invariant a[j+1..i+1] == snap[j..i]
        invariant SortedBy(leq, a[lo..j])
        invariant SortedBy(leq, a[j+1..i+1])
        invariant forall y | j+1 <= y < i+1 :: leq(x, a[y])
        invariant multiset{x} + (multiset(a[..]) - multiset{a[j]}) == multiset(snap)
      {
        a[j] := a[j-1];
        j := j - 1;

        SortedPrefix(leq, a[lo..j], snap[lo..i]);
      }

      a[j] := x;

      CombineSort(leq, a[lo..j], a[j], a[j+1..i+1]);
      assert a[lo..i+1] == a[lo..j] + [a[j]] +  a[j+1..i+1];
    }
  }

  // Sort part of an array (`a[lo..hi]`) with insertion sort.
  method InsertionSortSubarrayBy<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
    modifies a
    requires TotalOrdering(leq)
    requires lo <= hi <= a.Length
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(leq, a[lo..hi])
  {
    if lo == hi {
      return;
    }

    for i := lo + 1 to hi
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant SortedBy(leq, a[lo..i])
    {
      InsertionSortInnerLoopImpl.InsertionSortInnerLoop(leq, a, lo, i);
    }
  }

  // Sort an array with insertion sort.
  method InsertionSortArrayBy<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>)
    modifies a
    requires TotalOrdering(leq)
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(leq, a[..])
  {
    InsertionSortSubarrayBy(leq, a, 0, a.Length);
  }

  // Returns a with insertion sort sorted sequence.
  method InsertionSortSeqBy<A(!new, ==)>(leq: (A, A) -> bool, a: seq<A>) returns (r: seq<A>)
    requires TotalOrdering(leq)
    ensures multiset(a) == multiset(r)
    ensures SortedBy(leq, r)
  {
    var arr := Seq.ToArray(a);
    assert arr[..] == a;
    InsertionSortArrayBy(leq, arr);
    r := arr[..];
  }
}


/*/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\

  Verified Insertion Sort in Dafny with Bounded Arrays

  This module is mostly a copy from the above module, with the difference being that this module uses a bounded 
  integers as indices. This means that the array size is also bound. When looking at 
  <https://github.com/aws/aws-database-encryption-sdk-dynamodb/blob/a82094c6ad32f64db21d6231e74231d55e61016c/DynamoDbEncryption/dafny/StructuredEncryption/src/OptimizedMergeSort.dfy>
  I read, "Second, is has a bounded number implementation that avoids using `nat`." This module follows this 
  reasoning and also uses this optimization. The translation should not use big integers as indices.

  I tested the JavaScript translation (Dafny 4.11.0): 
  `UINT32_MAX` produces a `number` which is correct and wanted, while `UINT64_MAX` sadly produces big ints. 
  But this is actually not a real issue for insertion sort, as insertion sort is only efficient or preferable to 
  other sorting algorithms on very small arrays.

/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\*/

module InsertionSortBoundedU32 {
  import opened Std.Relations
  import Std.Collections.Seq
  import opened Std.BoundedInts

  // Implementation details of the inner loop.
  module InsertionSortInnerLoopImpl {
    import opened Std.Relations
    import opened Std.BoundedInts

    lemma SortedPrefix<A(!new)>(leq: (A, A) -> bool, p: seq<A>, a: seq<A>)
      requires p <= a
      requires TotalOrdering(leq)
      requires SortedBy(leq, a)
      ensures SortedBy(leq, p)
    {}

    lemma CombineSort<A(!new)>(leq: (A, A) -> bool, pre: seq<A>, x: A, post: seq<A>)
      requires TotalOrdering(leq)
      requires SortedBy(leq, pre)
      requires SortedBy(leq, post)
      requires forall i | 0 <= i < |pre| :: leq(pre[i], x)
      requires forall i | 0 <= i < |post| :: leq(x, post[i])
      ensures SortedBy(leq, pre + [x] + post)
    {}

    method {:isolate_assertions} InsertionSortInnerLoop<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: uint32, i: uint32)
      modifies a
      requires TotalOrdering(leq)
      requires a.Length <= UINT32_MAX as int
      requires lo as int < i as int < a.Length
      requires SortedBy(leq, a[lo..i])
      ensures SortedBy(leq, a[lo..i+1])
      ensures multiset(a[..]) == multiset(old(a[..]))
    {
      var x := a[i];
      var j := i;

      ghost var snap := a[..];
      SortedPrefix(leq, a[lo..j], snap[lo..i]);

      while j > lo && !leq(a[j-1], x)
        invariant lo as int <= j as int <= i as int < a.Length
        invariant a[..j+1] == snap[..j+1]
        invariant a[i+1..] == snap[i+1..]
        invariant a[j+1..i+1] == snap[j..i]
        invariant SortedBy(leq, a[lo..j])
        invariant SortedBy(leq, a[j+1..i+1])
        invariant forall y | j+1 <= y < i+1 :: leq(x, a[y])
        invariant multiset{x} + (multiset(a[..]) - multiset{a[j]}) == multiset(snap)
      {
        a[j] := a[j-1];
        j := j - 1;

        SortedPrefix(leq, a[lo..j], snap[lo..i]);
      }

      a[j] := x;

      CombineSort(leq, a[lo..j], a[j], a[j+1..i+1]);
      assert a[lo..i+1] == a[lo..j] + [a[j]] +  a[j+1..i+1];
    }
  }

  // Sort part of an array (`a[lo..hi]`) with insertion sort.
  method InsertionSortSubarrayBy<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: uint32, hi: uint32)
    modifies a
    requires TotalOrdering(leq)
    requires a.Length <= UINT32_MAX as int
    requires lo as int <= hi as int <= a.Length
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(leq, a[lo..hi])
  {
    if lo == hi {
      return;
    }

    for i: uint32 := lo + 1 to hi
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant SortedBy(leq, a[lo..i])
    {
      InsertionSortInnerLoopImpl.InsertionSortInnerLoop(leq, a, lo, i);
    }
  }

  // Sort an array with insertion sort.
  method InsertionSortArrayBy<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>)
    modifies a
    requires TotalOrdering(leq)
    requires a.Length <= UINT32_MAX as int
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(leq, a[..])
  {
    InsertionSortSubarrayBy(leq, a, 0, a.Length as uint32);
  }

  // Returns a with insertion sort sorted sequence.
  method InsertionSortSeqBy<A(!new, ==)>(leq: (A, A) -> bool, a: seq<A>) returns (r: seq<A>)
    requires TotalOrdering(leq)
    requires |a| <= UINT32_MAX as int
    ensures multiset(a) == multiset(r)
    ensures SortedBy(leq, r)
  {
    var arr := Seq.ToArray(a);
    assert arr[..] == a;
    InsertionSortArrayBy(leq, arr);
    r := arr[..];
  }
}



