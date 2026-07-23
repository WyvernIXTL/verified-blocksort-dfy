// Copyright (C) 2026 Adam McKellar <dev@mckellar.eu>
// 
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.



/*/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\

  Verified Block Sort in Dafny

  This module contains a verified implementation of block sort in the programming language Dafny.
  This implementation is not in place! The ressource <https://every-algorithm.github.io/2023/11/27/block_sort.html>
  was used for the implementation. Instead of creating a new array for every merge a single array is used.

  I expect, without having done an analysis:
    
  | worst-case performance      | O(n log n) |
  | --------------------------- | ---------- |
  | worst-case space complexity | O(n/2)     |


/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\*/



module BlockSortUnbound {
  import opened Std.Relations

  import opened InsertionSortAdaptive


  module BlockSortUnboundImpl {
    import opened Std.Relations

    import opened InsertionSortAdaptive


    method CopySubarray<A(!new, ==)>(a: array<A>, lo: nat, hi: nat, b: array<A>)
      modifies b
      requires a != b
      requires a.Length <= b.Length
      requires lo < hi <= a.Length
      ensures b[..hi-lo] == a[lo..hi]
      // ensures forall i | 0 <= i < hi-lo :: b[i] == a[lo+i]
    {
      forall i | 0 <= i < hi-lo {
        b[i] := a[lo+i];
      }
    }

    lemma MergeSortNext<A(!new, ==)>(leq: (A, A) -> bool, a: seq<A>, x: A, y: A)
      requires TotalOrdering(leq)
      requires SortedBy(leq, a)
      requires |a| > 1
      requires leq(a[|a|-1], x) || leq(a[|a|-1], y)
      ensures SortedBy(leq, a + [x]) || SortedBy(leq, a + [y])
    {}

    lemma SortedImpliesLeq<A(!new)>(leq: (A, A) -> bool, a: seq<A>, i: nat, j: nat)
      requires TotalOrdering(leq)
      requires SortedBy(leq, a)
      requires 0 <= i <= j < |a|
      ensures leq(a[i], a[j])
    {}

    lemma SortedPrefix<A(!new)>(leq: (A, A) -> bool, p: seq<A>, a: seq<A>)
      requires p <= a
      requires TotalOrdering(leq)
      requires SortedBy(leq, a)
      ensures SortedBy(leq, p)
    {}

    method {:isolate_assertions} Merge<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, mid: nat, hi: nat, cache: array<A>)
      modifies a
      modifies cache
      requires a != cache
      requires TotalOrdering(leq)
      requires lo < mid < hi <= a.Length
      requires SortedBy(leq, a[lo..mid])
      requires SortedBy(leq, a[mid..hi])
      requires a.Length <= cache.Length
      ensures SortedBy(leq, a[lo..hi])
      // ensures multiset(a[lo..hi]) == multiset(old(a[lo..hi]))
    {
      ghost var snap := a[..];

      CopySubarray(a, lo, mid, cache);

      var left_start: nat := 0;
      var left_i: nat := left_start;
      var left_bound: nat := mid-lo;
      var right_start: nat := mid;
      var right_i: nat := right_start;
      var right_bound: nat := hi;
      var target_start: nat := lo;
      var target_i: nat := target_start;
      var target_bound: nat := hi;

      while left_i < left_bound && right_i < right_bound
        // indices invariants
        invariant left_start <= left_i <= left_bound
        invariant right_start <= right_i <= right_bound
        invariant (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
        invariant target_start <= target_i <= target_bound

        // left and right invariants
        invariant SortedBy(leq, cache[left_i..left_bound])
        invariant a[right_i..right_bound] == snap[right_i..right_bound]
        invariant SortedBy(leq, a[right_i..right_bound])

        // combinded is sorted
        // invariant SortedBy(leq, a[target_start..target_i] + cache[left_i..left_bound])
        // invariant SortedBy(leq, a[target_start..target_i] + a[right_i..right_bound])

        // target
        invariant SortedBy(leq, a[target_start..target_i])
      {
        if leq(cache[left_i], a[right_i]) {
          a[target_i] := cache[left_i];
          left_i := left_i + 1;
        } else {
          a[target_i] := a[right_i];
          right_i := right_i + 1;
        }

        target_i := target_i + 1;
      }

      while left_i < left_bound
        invariant left_i <= left_bound
        invariant left_i + (right_i - mid) == target_i - lo
        invariant lo <= target_i <= target_bound
        invariant SortedBy(leq, a[target_start..target_i])
      {
        a[target_i] := cache[left_i];
        left_i := left_i + 1;
        target_i := target_i + 1;
      }
      while right_i < right_bound
        invariant right_i <= right_bound
        invariant left_i + (right_i - mid) == target_i - lo
        invariant lo <= target_i <= target_bound
        invariant SortedBy(leq, a[target_start..target_i])
      {
        a[target_i] := a[right_i];
        right_i := right_i + 1;
        target_i := target_i + 1;
      }
    }

  }



}


