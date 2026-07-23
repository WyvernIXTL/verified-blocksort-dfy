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
  import Std.Collections.Seq

  import opened InsertionSortAdaptive


  module BlockSortUnboundImpl {
    import opened Std.Relations
    import Std.Collections.Seq

    import opened InsertionSortAdaptive


    method CopySubarray<A(!new, ==)>(a: array<A>, lo: nat, hi: nat, b: array<A>)
      modifies b
      requires a != b
      requires a.Length <= b.Length
      requires lo < hi <= a.Length
      ensures b[..hi-lo] == a[lo..hi]
    {
      forall i | 0 <= i < hi-lo {
        b[i] := a[lo+i];
      }
    }

    lemma SortedImpliesLeq<A(!new)>(leq: (A, A) -> bool, a: seq<A>, i: nat, j: nat)
      requires TotalOrdering(leq)
      requires SortedBy(leq, a)
      requires 0 <= i <= j < |a|
      ensures leq(a[i], a[j])
    {}

    lemma MultiSetTrippleSlice<A(!new)>(a: seq<A>, lo: nat, hi: nat)
      requires lo <= hi <= |a|
      ensures multiset(a[..lo]) + multiset(a[lo..hi]) + multiset(a[hi..]) == multiset(a[..])
    {
      assert a[..lo] + a[lo..hi] + a[hi..] == a;
    }

    lemma MultiSet5Slice<A(!new)>(a: seq<A>, i0: nat, i1: nat, i2: nat, i3: nat)
      requires i0 <= i1 <= i2 <= i3 <= |a|
      ensures multiset(a[..i0]) + multiset(a[i0..i1]) + multiset(a[i1..i2]) + multiset(a[i2..i3]) + multiset(a[i3..]) == multiset(a)
    {
      assert (a[..i0]) + (a[i0..i1]) + (a[i1..i2]) + (a[i2..i3]) + (a[i3..]) == (a);
    }

    ghost predicate {:opaque} MultisetInv<A(!new)>(
      a: array<A>, cache: array<A>, snap: seq<A>,
      lo: nat, mid: nat, hi: nat,
      target_i: nat, left_i: nat, right_i: nat)
      requires lo <= mid <= hi <= a.Length
      requires lo <= target_i <= hi
      requires 0 <= left_i <= mid - lo <= cache.Length
      requires mid <= right_i <= hi
      reads a, cache
    {
      multiset(a[..lo]) + multiset(a[lo..target_i]) + multiset(cache[left_i..mid-lo]) + multiset(a[right_i..hi]) + multiset(a[hi..]) == multiset(snap)
    }


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
      ensures multiset(a[..]) == multiset(old(a[..]))
    {
      ghost var snap := a[..];

      CopySubarray(a, lo, mid, cache);

      ghost var snap_cache := cache[..];

      var left_start: nat := 0;
      var left_i: nat := left_start;
      var left_bound: nat := mid-lo;
      var right_start: nat := mid;
      var right_i: nat := right_start;
      var right_bound: nat := hi;
      var target_start: nat := lo;
      var target_i: nat := target_start;
      var target_bound: nat := hi;

      // assert MultisetInv(a, cache, snap, lo, mid, hi, lo, 0, mid) by {
      //   reveal MultisetInv;
      //   MultiSet5Slice(a[..], lo, lo, mid, hi);
      // }

      // merging left with right
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

        // bridge: last placed element is <= both candidates
        invariant target_i > target_start ==>
                    left_i < left_bound ==>
                      leq(a[target_i - 1], cache[left_i])

        invariant target_i > target_start ==>
                    right_i < right_bound ==>
                      leq(a[target_i - 1], a[right_i])

        // target
        invariant SortedBy(leq, a[target_start..target_i])

        // invariant MultisetInv(a, cache, snap, lo, mid, hi, target_i, left_i, right_i)
      {
        if leq(cache[left_i], a[right_i]) {
          a[target_i] := cache[left_i];
          left_i := left_i + 1;
        } else {
          a[target_i] := a[right_i];

          SortedImpliesLeq(leq, a[right_i..right_bound], 0, (if right_i + 1 < right_bound then 1 else 0));

          right_i := right_i + 1;
        }

        target_i := target_i + 1;

        // assert MultisetInv(a, cache, snap, lo, mid, hi, target_i, left_i, right_i) by {
        //   reveal MultisetInv;
        //   MultiSet5Slice(a[..], lo, target_i, right_i, hi);
        // }
      }

      // assert MultisetInv(a, cache, snap, lo, mid, hi, target_i, left_i, right_i) by {
      assert multiset(a[..target_start]) + multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap) by {
        ghost var snap_left_i := left_start;
        ghost var snap_right_i := right_start;
        ghost var snap_target_i := target_start;

        ghost var snap_2 := snap;

        assert multiset(snap_2[..target_start]) + multiset(snap_2[target_start..snap_target_i]) + multiset(snap_cache[snap_left_i..left_bound]) + multiset(snap_2[snap_right_i..right_bound]) + multiset(snap_2[target_bound..]) == multiset(snap) by {
          assert snap[snap_target_i..snap_right_i] == snap_cache[snap_left_i..left_bound];
          assert multiset(snap[snap_target_i..snap_right_i]) == multiset(snap_cache[snap_left_i..left_bound]);
          MultiSet5Slice(snap_2, target_start, snap_target_i, snap_right_i, target_bound);
        }

        while snap_left_i < left_bound && snap_right_i < right_bound
          // indices invariants
          invariant left_start <= snap_left_i <= left_bound
          invariant right_start <= snap_right_i <= right_bound
          invariant (snap_left_i - left_start) + (snap_right_i - right_start) == (snap_target_i - target_start)
          invariant target_start <= snap_target_i <= target_bound

          invariant right_bound <= |snap_2|
          invariant target_bound <= |snap_2|

          // multiset invariant
          invariant multiset(snap_2[..target_start]) + multiset(snap_2[target_start..snap_target_i]) + multiset(snap_cache[snap_left_i..left_bound]) + multiset(snap_2[snap_right_i..right_bound]) + multiset(snap_2[target_bound..]) == multiset(snap)
        {
          if leq(snap_cache[snap_left_i], snap[snap_right_i]) {
            snap_2 := snap_2[snap_target_i := snap_cache[snap_left_i]];
            snap_left_i := snap_left_i + 1;
          } else {
            snap_2 := snap_2[snap_target_i := snap_2[snap_right_i]];
            snap_right_i := snap_right_i + 1;
          }

          snap_target_i := snap_target_i + 1;

          assert multiset(snap_2[..target_start]) + multiset(snap_2[target_start..snap_target_i]) + multiset(snap_cache[snap_left_i..left_bound]) + multiset(snap_2[snap_right_i..right_bound]) + multiset(snap_2[target_bound..]) == multiset(snap) by {
            assert snap[lo+snap_left_i..right_start] == snap_cache[snap_left_i..left_bound];
            assert multiset(snap[lo+snap_left_i..right_start]) == multiset(snap_cache[snap_left_i..left_bound]);
            MultiSet5Slice(snap_2, target_start, snap_target_i, snap_right_i, target_bound);
          }
        }
      }


      // if right is exhausted copy left
      while left_i < left_bound
        // indices invariants
        invariant left_start <= left_i <= left_bound
        invariant (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
        invariant target_start <= target_i <= target_bound

        // left and right invariants
        invariant SortedBy(leq, cache[left_i..left_bound])
        invariant a[right_i..right_bound] == snap[right_i..right_bound]
        invariant SortedBy(leq, a[right_i..right_bound])

        // bridge: last placed element is <= both candidates
        invariant target_i > target_start ==>
                    left_i < left_bound ==>
                      leq(a[target_i - 1], cache[left_i])

        invariant target_i > target_start ==>
                    right_i < right_bound ==>
                      leq(a[target_i - 1], a[right_i])

        //target
        invariant SortedBy(leq, a[target_start..target_i])

        // invariant MultisetInv(a, cache, snap, lo, mid, hi, target_i, left_i, right_i)
      {
        a[target_i] := cache[left_i];
        left_i := left_i + 1;
        target_i := target_i + 1;

        // assert MultisetInv(a, cache, snap, lo, mid, hi, target_i, left_i, right_i) by {
        //   reveal MultisetInv;
        //   MultiSet5Slice(a[..], lo, target_i, right_i, hi);
        // }
      }

      // if left is exhausted assert goal by asserting right side is allready in place
      assert SortedBy(leq, a[target_start..target_bound]) by {
        var right_i := right_i;
        var target_i := target_i;

        while right_i < right_bound
          // indices invariants
          invariant right_start <= right_i <= right_bound
          invariant (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
          invariant target_start <= target_i <= target_bound

          // left and right invariants
          invariant a[right_i..right_bound] == snap[right_i..right_bound]
          invariant SortedBy(leq, a[right_i..right_bound])

          // bridge: last placed element is <= both candidates
          invariant target_i > target_start ==>
                      right_i < right_bound ==>
                        leq(a[target_i - 1], a[right_i])

          //target
          invariant SortedBy(leq, a[target_start..target_i])
        {
          assert a[target_i] == a[right_i];
          if right_i + 1 < right_bound {
            SortedImpliesLeq(leq, a[right_i..right_bound], 0, 1);
          }
          right_i := right_i + 1;
          target_i := target_i + 1;
        }
      }

      // assert multiset(a[..]) == multiset(snap) by {
      //   reveal MultisetInv;
      //   MultiSetTrippleSlice(a[..], lo, hi);
      // }
    }

  }



}
