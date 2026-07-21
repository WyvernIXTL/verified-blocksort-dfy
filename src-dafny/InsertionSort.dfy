// Copyright (C) 2026 Adam McKellar <dev@mckellar.eu>
// 
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.


/*/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\

  Verified Insertion Sort in Dafny

  This module contains a verified implementation of insertion sort in the programming language Dafny.
  The algorithm itself strictly follows the pseudocode available at <https://en.wikipedia.org/wiki/Insertion_sort>.
  The verification was the hard part.

  Dafny v4.11.0 was used for writing this code. To verify this code execute dafny with:

    dafny verify --standard-libraries --cores 16 --resource-limit 3000000 InsertionSort.dfy
  

/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\*/


module InsertionSort {
  export
    provides InsertionSort, Relations

  import opened Relations = Std.Relations


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

  method InsertionSort<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
    modifies a
    requires TotalOrdering(leq)
    requires lo < hi <= a.Length
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(leq, a[lo..hi])
  {
    var i := lo + 1;

    while i < hi
      invariant i <= hi
      invariant lo < i <= a.Length
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant SortedBy(leq, a[lo..i])
    {
      InsertionSortInnerLoop(leq, a, lo, i);
      i := i + 1;
    }
  }

  method InsertionSortA<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>)
    modifies a
    requires TotalOrdering(leq)
    requires 0 < a.Length
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(leq, a[..])
  {
    InsertionSort(leq, a, 0, a.Length);
  }
}
