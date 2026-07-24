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

    lemma MultiSet4Slice<A(!new)>(a: seq<A>, i0: nat, i1: nat, i2: nat)
      requires i0 <= i1 <= i2 <= |a|
      ensures multiset(a[..i0]) + multiset(a[i0..i1]) + multiset(a[i1..i2]) + multiset(a[i2..]) == multiset(a)
    {
      assert a[..i0] + a[i0..i1] == a[..i1];
      assert a[..i1] + a[i1..i2] == a[..i2];
      assert (a[..i0]) + (a[i0..i1]) + (a[i1..i2]) + (a[i2..]) == (a);
    }

    lemma MultiSet5Slice<A(!new)>(a: seq<A>, i0: nat, i1: nat, i2: nat, i3: nat)
      requires i0 <= i1 <= i2 <= i3 <= |a|
      ensures multiset(a[..i0]) + multiset(a[i0..i1]) + multiset(a[i1..i2]) + multiset(a[i2..i3]) + multiset(a[i3..]) == multiset(a)
    {
      assert (a[..i0]) + (a[i0..i1]) + (a[i1..i2]) + (a[i2..i3]) + (a[i3..]) == (a);
    }

    lemma HeadOfCache<A(!new)>(cache: array<A>, lo: nat, hi: nat)
      requires lo < hi <= cache.Length
      ensures [cache[lo]] + cache[lo + 1..hi] == cache[lo..hi]
    {}

    lemma TailOfTarget<A(!new)>(a: array<A>, lo: nat, hi: nat)
      requires lo < hi <= a.Length
      ensures a[lo..hi-1] + [a[hi-1]] == a[lo..hi]
    {}

    lemma WindowEqualsSeqWithoutEdges<A(!new)>(snap: seq<A>, lo: nat, hi: nat)
      requires lo < hi <= |snap|
      ensures multiset(snap[lo..hi]) == multiset(snap) - multiset(snap[..lo]) - multiset(snap[hi..])
    {
      assert snap[..lo] + snap[lo..hi] + snap[hi..] == snap;
    }

    lemma MainMergeLoopBranchAPreservesSortedByInvariant<A(!new)>(leq: (A, A) -> bool, a: array<A>, cache: array<A>, snap: seq<A>, left_start: nat, left_i: nat, left_bound: nat,
                                                                  right_start: nat, right_i: nat, right_bound: nat, target_start: nat, target_i: nat, target_bound: nat)
      // Merge Method requirements
      requires a != cache
      requires TotalOrdering(leq)
      requires a.Length <= cache.Length

      // bridge
      requires |snap| == a.Length
      requires 0 <= right_start < right_bound <= a.Length
      requires 0 == left_start < left_bound <= a.Length

      // Loop Invariants
      requires left_start <= left_i < left_bound <= a.Length
      requires right_start <= right_i < right_bound <= a.Length
      requires (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
      requires target_start <= target_i < target_bound <= a.Length
      requires SortedBy(leq, cache[left_i..left_bound])
      requires a[right_i..right_bound] == snap[right_i..right_bound]
      requires SortedBy(leq, a[right_i..right_bound])
      requires target_i > target_start ==> left_i < left_bound ==> leq(a[target_i - 1], cache[left_i])
      requires target_i > target_start ==> right_i < right_bound ==>leq(a[target_i - 1], a[right_i])
      requires SortedBy(leq, a[target_start..target_i])

      // if branch condition and effects
      requires leq(cache[left_i], a[right_i])
      requires a[target_i] == cache[left_i]

      // Loop Invariant Ensure
      ensures left_start <= left_i+1 <= left_bound <= a.Length
      ensures right_start <= right_i <= right_bound <= a.Length
      ensures (left_i+1 - left_start) + (right_i - right_start) == (target_i+1 - target_start)
      ensures target_start <= target_i+1 <= target_bound <= a.Length
      ensures SortedBy(leq, cache[left_i+1..left_bound])
      ensures a[right_i..right_bound] == snap[right_i..right_bound]
      ensures SortedBy(leq, a[right_i..right_bound])
      ensures target_i+1 > target_start ==> left_i+1 < left_bound ==> leq(a[target_i], cache[left_i+1])
      ensures target_i+1 > target_start ==> right_i < right_bound ==>leq(a[target_i], a[right_i])
      ensures SortedBy(leq, a[target_start..target_i+1])
    {
      assert SortedBy(leq, a[target_start..target_i+1]) by {
        SortedImpliesLeq(leq, cache[left_i..left_bound], 0, (if left_i+1 < left_bound then 1 else 0));
        assert leq(a[target_i], cache[left_i]);
        assert leq(a[target_i], a[right_i]);
      }
    }

    lemma CopyLoopLeftPreservesSortedByInvariant<A(!new)>(leq: (A, A) -> bool, a: array<A>, cache: array<A>, snap: seq<A>, left_start: nat, left_i: nat, left_bound: nat,
                                                          right_start: nat, right_bound: nat, target_start: nat, target_i: nat, target_bound: nat)
      // Merge Method requirements
      requires a != cache
      requires TotalOrdering(leq)
      requires a.Length <= cache.Length

      // bridge
      requires |snap| == a.Length
      requires 0 == left_start < left_bound <= a.Length

      // Loop Invariants
      requires left_start <= left_i < left_bound <= a.Length
      requires right_start < right_bound <= a.Length
      requires (left_i - left_start) + (right_bound - right_start) == (target_i - target_start)
      requires target_start <= target_i < target_bound <= a.Length
      requires SortedBy(leq, cache[left_i..left_bound])
      requires target_i > target_start ==> left_i < left_bound ==> leq(a[target_i - 1], cache[left_i])
      requires SortedBy(leq, a[target_start..target_i])

      // if branch condition and effects
      requires a[target_i] == cache[left_i]

      // Loop Invariant Ensure
      ensures left_start <= left_i+1 <= left_bound <= a.Length
      ensures (left_i+1 - left_start) + (right_bound - right_start) == (target_i+1 - target_start)
      ensures target_start <= target_i+1 <= target_bound <= a.Length
      ensures SortedBy(leq, cache[left_i+1..left_bound])
      ensures target_i+1 > target_start ==> left_i+1 < left_bound ==> leq(a[target_i], cache[left_i+1])
      ensures SortedBy(leq, a[target_start..target_i+1])
    {
      assert SortedBy(leq, a[target_start..target_i+1]) by {
        SortedImpliesLeq(leq, cache[left_i..left_bound], 0, (if left_i+1 < left_bound then 1 else 0));
        assert leq(a[target_i], cache[left_i]);
      }
    }

    lemma MainMergeLoopBranchBPreservesSortedByInvariant<A(!new)>(leq: (A, A) -> bool, a: array<A>, cache: array<A>, snap: seq<A>, left_start: nat, left_i: nat, left_bound: nat,
                                                                  right_start: nat, right_i: nat, right_bound: nat, target_start: nat, target_i: nat, target_bound: nat)
      // Merge Method requirements
      requires a != cache
      requires TotalOrdering(leq)
      requires a.Length <= cache.Length

      // bridge
      requires |snap| == a.Length
      requires 0 <= right_start < right_bound <= a.Length
      requires 0 == left_start < left_bound <= a.Length

      // Loop Invariants
      requires left_start <= left_i < left_bound <= a.Length
      requires right_start <= right_i < right_bound <= a.Length
      requires (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
      requires target_start <= target_i < target_bound <= a.Length
      requires SortedBy(leq, cache[left_i..left_bound])
      requires a[right_i..right_bound] == snap[right_i..right_bound]
      requires SortedBy(leq, a[right_i..right_bound])
      requires target_i > target_start ==> left_i < left_bound ==> leq(a[target_i - 1], cache[left_i])
      requires target_i > target_start ==> right_i < right_bound ==>leq(a[target_i - 1], a[right_i])
      requires SortedBy(leq, a[target_start..target_i])

      // if branch condition and effects
      requires !leq(cache[left_i], a[right_i])
      requires a[target_i] == a[right_i]

      // Loop Invariant Ensure
      ensures left_start <= left_i <= left_bound <= a.Length
      ensures right_start <= right_i <= right_bound <= a.Length
      ensures (left_i - left_start) + (right_i+1 - right_start) == (target_i+1 - target_start)
      ensures target_start <= target_i <= target_bound <= a.Length
      ensures SortedBy(leq, cache[left_i..left_bound])
      ensures a[right_i+1..right_bound] == snap[right_i+1..right_bound]
      ensures SortedBy(leq, a[right_i+1..right_bound])
      ensures target_i+1 > target_start ==> left_i < left_bound ==> leq(a[target_i], cache[left_i])
      ensures target_i+1 > target_start ==> right_i+1 < right_bound ==>leq(a[target_i], a[right_i+1])
      ensures SortedBy(leq, a[target_start..target_i])
    {
      assert SortedBy(leq, a[target_start..target_i+1]) by {
        SortedImpliesLeq(leq, a[right_i..right_bound], 0, (if right_i+1 < right_bound then 1 else 0));
        assert leq(a[target_i], cache[left_i]);
        assert leq(a[target_i], a[right_i]);
      }
    }


    lemma MainMergeLoopBranchAPreservesPermutationInvariant<A(!new)>(leq: (A, A) -> bool, a: array<A>, cache: array<A>, snap: seq<A>, left_start: nat, left_i: nat, left_bound: nat,
                                                                     right_start: nat, right_i: nat, right_bound: nat, target_start: nat, target_i: nat, target_bound: nat)
      // Merge Method requirements
      requires a != cache
      requires TotalOrdering(leq)
      requires a.Length <= cache.Length

      // bridge
      requires |snap| == a.Length
      requires 0 <= right_start < right_bound <= a.Length
      requires 0 == left_start < left_bound <= a.Length

      // Loop Invariants
      requires left_start <= left_i < left_bound <= a.Length
      requires right_start <= right_i < right_bound <= a.Length
      requires (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
      requires target_start <= target_i < target_bound <= a.Length
      requires a[right_i..right_bound] == snap[right_i..right_bound]
      requires multiset(a[..target_start]) + multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap)

      requires target_start <= target_i + 1 <= right_i <= target_bound <= a.Length

      // if branch condition and effects
      requires a[target_i] == cache[left_i]

      // Loop Invariant Ensure
      ensures left_start <= left_i <= left_bound <= a.Length
      ensures right_start <= right_i <= right_bound <= a.Length
      ensures (left_i+1 - left_start) + (right_i - right_start) == (target_i+1 - target_start)
      ensures target_start <= target_i <= target_bound <= a.Length
      ensures a[right_i+1..right_bound] == snap[right_i+1..right_bound]
      ensures multiset(a[..target_start]) + multiset(a[target_start..target_i+1]) + multiset(cache[left_i+1..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap)
    {
      MultiSet5Slice(a[..], target_start, target_i + 1, right_i, target_bound);
      assert a[target_start..target_i] + [cache[left_i]] == a[target_start..target_i + 1];
      HeadOfCache(cache, left_i, left_bound);
      assert multiset(a[target_start..target_i + 1]) + multiset(cache[left_i + 1..left_bound]) == multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]);
    }

    lemma CopyLeftPreservesPermutationInvariant<A(!new)>(leq: (A, A) -> bool, a: array<A>, cache: array<A>, snap: seq<A>, left_start: nat, left_i: nat, left_bound: nat,
                                                         right_start: nat, right_bound: nat, target_start: nat, target_i: nat, target_bound: nat)
      // Merge Method requirements
      requires a != cache
      requires TotalOrdering(leq)
      requires a.Length <= cache.Length

      // bridge
      requires |snap| == a.Length
      requires 0 <= right_start < right_bound <= a.Length
      requires 0 == left_start < left_bound <= a.Length

      // Loop Invariants
      requires left_start <= left_i < left_bound <= a.Length
      requires right_start < right_bound <= a.Length
      requires (left_i - left_start) + (right_bound - right_start) == (target_i - target_start)
      requires target_start <= target_i < target_bound <= a.Length
      requires multiset(a[..target_start]) + multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]) + multiset(a[target_bound..]) == multiset(snap)

      requires target_start <= target_i + 1 <= target_bound <= a.Length

      // if branch condition and effects
      requires a[target_i] == cache[left_i]

      // Loop Invariant Ensure
      ensures left_start <= left_i <= left_bound <= a.Length
      ensures right_start <= right_bound <= a.Length
      ensures (left_i+1 - left_start) + (right_bound - right_start) == (target_i+1 - target_start)
      ensures target_start <= target_i <= target_bound <= a.Length
      ensures multiset(a[..target_start]) + multiset(a[target_start..target_i+1]) + multiset(cache[left_i+1..left_bound]) + multiset(a[target_bound..]) == multiset(snap)
    {
      MultiSet4Slice(a[..], target_start, target_i + 1, target_bound);
      assert a[target_start..target_i] + [cache[left_i]] == a[target_start..target_i + 1];
      HeadOfCache(cache, left_i, left_bound);
      assert multiset(a[target_start..target_i + 1]) + multiset(cache[left_i + 1..left_bound]) == multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]);
    }

    lemma MainMergeLoopBranchBPreservesPermutationInvariant<A(!new)>(leq: (A, A) -> bool, a: array<A>, cache: array<A>, snap: seq<A>, left_start: nat, left_i: nat, left_bound: nat,
                                                                     right_start: nat, right_i: nat, right_bound: nat, target_start: nat, target_i: nat, target_bound: nat)
      // Merge Method requirements
      requires a != cache
      requires TotalOrdering(leq)
      requires a.Length <= cache.Length

      // bridge
      requires |snap| == a.Length
      requires 0 <= right_start < right_bound <= a.Length
      requires 0 == left_start < left_bound <= a.Length

      // Loop Invariants
      requires left_start <= left_i < left_bound <= a.Length
      requires right_start <= right_i < right_bound <= a.Length
      requires (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
      requires target_start <= target_i < target_bound <= a.Length
      requires a[right_i..right_bound] == snap[right_i..right_bound]
      requires multiset(a[..target_start]) + multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap)

      requires target_start <= target_i + 1 <= right_i + 1 <= target_bound <= a.Length

      // if branch condition and effects
      requires a[target_i] == a[right_i]

      ensures left_start <= left_i <= left_bound <= a.Length
      ensures right_start <= right_i+1 <= right_bound <= a.Length
      ensures (left_i - left_start) + (right_i+1 - right_start) == (target_i+1 - target_start)
      ensures target_start <= target_i+1 <= target_bound <= a.Length
      ensures a[right_i+1..right_bound] == snap[right_i+1..right_bound]
      ensures multiset(a[..target_start]) + multiset(a[target_start..target_i+1]) + multiset(cache[left_i..left_bound]) + multiset(a[right_i+1..right_bound]) + multiset(a[target_bound..]) == multiset(snap)
    {
      assert a[target_start..target_i] + [a[right_i]] == a[target_start..target_i + 1];
      MultiSet5Slice(a[..], target_start, target_i + 1, right_i + 1, target_bound);
      HeadOfCache(a, right_i, right_bound);
      assert multiset(a[target_start..target_i + 1]) + multiset(a[right_i + 1..right_bound]) == multiset(a[target_start..target_i]) + multiset(a[right_i..right_bound]);
    }


    ghost predicate {:opaque} OpaqueSortedBy<A(!new)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
      reads a
      requires TotalOrdering(leq)
      requires lo <= hi <= a.Length
    {
      SortedBy(leq, a[lo..hi])
    }

    ghost predicate {:opaque} IsPerm<A(!new)>(a: seq<A>, old_a: seq<A>)
    {
      multiset(a) == multiset(old_a)
    }

    ghost predicate {:opaque} InvariantIsPerm<A(!new)>(a: array<A>, cache: array<A>, snap: seq<A>, left_i: nat, left_bound: nat,
                                                       right_i: nat, right_bound: nat, target_start: nat, target_i: nat, target_bound: nat)
      reads a
      reads cache

      // invariants
      requires |snap| == a.Length
      requires a.Length <= cache.Length

      requires left_i <= left_bound <= a.Length
      requires right_i <= right_bound <= a.Length
      requires target_start <= target_i <= target_bound <= a.Length
    {
      multiset(a[..target_start]) + multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap)
    }



    method {:isolate_assertions} Merge<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, mid: nat, hi: nat, cache: array<A>)
      modifies a

      requires a != cache
      requires TotalOrdering(leq)
      requires lo < mid < hi <= a.Length
      requires OpaqueSortedBy(leq, a, lo, mid)
      requires OpaqueSortedBy(leq, a, mid, hi)
      requires a.Length <= cache.Length

      requires a[lo..mid] == cache[0..mid-lo]

      ensures OpaqueSortedBy(leq, a, lo, hi)
      ensures IsPerm(a[..], old(a[..]))
    {
      ghost var snap := a[..];
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

      assert InvariantIsPerm(a, cache, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound) by {
        reveal InvariantIsPerm;
        assert snap[target_i..right_i] == cache[left_i..left_bound];
        assert multiset(snap[target_i..right_i]) == multiset(cache[left_i..left_bound]);
        MultiSet5Slice(a[..], target_start, target_i, right_i, target_bound);
      }

      assert OpaqueSortedBy(leq, cache, left_i, left_bound) by {
        reveal OpaqueSortedBy;
      }
      assert OpaqueSortedBy(leq, a, right_i, right_bound) by {
        reveal OpaqueSortedBy;
      }
      assert OpaqueSortedBy(leq, a, target_start, target_i) by {
        reveal OpaqueSortedBy;
      }

      // merging left with right
      while left_i < left_bound && right_i < right_bound
        // indices invariants
        invariant left_start <= left_i <= left_bound
        invariant right_start <= right_i <= right_bound
        invariant (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
        invariant target_start <= target_i <= target_bound

        // left and right invariants
        invariant OpaqueSortedBy(leq, cache, left_i, left_bound)
        invariant a[right_i..right_bound] == snap[right_i..right_bound]
        invariant OpaqueSortedBy(leq, a, right_i, right_bound)

        // bridge: last placed element is <= both candidates
        invariant target_i > target_start ==>
                    left_i < left_bound ==>
                      leq(a[target_i - 1], cache[left_i])

        invariant target_i > target_start ==>
                    right_i < right_bound ==>
                      leq(a[target_i - 1], a[right_i])

        // is sorted
        invariant OpaqueSortedBy(leq, a, target_start, target_i)

        // is permutation
        // invariant multiset(a[..target_start]) + multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap)
        invariant InvariantIsPerm(a, cache, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound)
      {
        var left := leq(cache[left_i], a[right_i]);

        if left {
          a[target_i] := cache[left_i];
        }

        assert InvSortA1: left ==> target_i+1 > target_start ==> left_i+1 < left_bound ==> leq(a[target_i], cache[left_i+1]) by {
          reveal OpaqueSortedBy;
          if left {
            assert target_i+1 > target_start ==> left_i+1 < left_bound ==> leq(a[target_i], cache[left_i+1]) by {
              MainMergeLoopBranchAPreservesSortedByInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_i, right_bound, target_start, target_i, target_bound);
            }
          }
        }

        assert InvSortA2: left ==> target_i+1 > target_start ==> right_i < right_bound ==> leq(a[target_i], a[right_i]) by {
          reveal OpaqueSortedBy;
          if left {
            assert  target_i+1 > target_start ==> right_i < right_bound ==> leq(a[target_i], a[right_i]) by {
              MainMergeLoopBranchAPreservesSortedByInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_i, right_bound, target_start, target_i, target_bound);
            }
          }
        }

        assert InvSortA3: left ==> OpaqueSortedBy(leq, a, target_start, target_i+1) by {
          reveal OpaqueSortedBy;
          if left {
            assert SortedBy(leq, a[target_start..target_i+1]) by {
              MainMergeLoopBranchAPreservesSortedByInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_i, right_bound, target_start, target_i, target_bound);
            }
          }
        }

        // assert InvPerm: left ==> multiset(a[..target_start]) + multiset(a[target_start..target_i+1]) + multiset(cache[left_i+1..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap) by {
        assert InvPerm: left ==> InvariantIsPerm(a, cache, snap, left_i+1, left_bound, right_i, right_bound, target_start, target_i+1, target_bound) by {
          if left {
            // assert multiset(a[..target_start]) + multiset(a[target_start..target_i+1]) + multiset(cache[left_i+1..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap) by{
            assert InvariantIsPerm(a, cache, snap, left_i+1, left_bound, right_i, right_bound, target_start, target_i+1, target_bound) by {
              reveal InvariantIsPerm;
              MainMergeLoopBranchAPreservesPermutationInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_i, right_bound, target_start, target_i, target_bound);
            }
          }
        }

        if left {
          target_i := target_i + 1;
          left_i := left_i + 1;
        }

        if !left {
          a[target_i] := a[right_i];
        }

        assert InvSortB1 : !left ==> target_i+1 > target_start ==> left_i < left_bound ==> leq(a[target_i], cache[left_i]) by {
          reveal OpaqueSortedBy;
          if !left {
            assert target_i+1 > target_start ==> left_i < left_bound ==> leq(a[target_i], cache[left_i]) by {
              MainMergeLoopBranchBPreservesSortedByInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_i, right_bound, target_start, target_i, target_bound);
            }
          }
        }

        assert InvSortB2 : !left ==> target_i+1 > target_start ==> right_i+1 < right_bound ==> leq(a[target_i], a[right_i+1]) by {
          reveal OpaqueSortedBy;
          if !left {
            assert target_i+1 > target_start ==> right_i+1 < right_bound ==> leq(a[target_i], a[right_i+1]) by {
              MainMergeLoopBranchBPreservesSortedByInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_i, right_bound, target_start, target_i, target_bound);
            }
          }
        }

        assert InvSortB3 : !left ==> OpaqueSortedBy(leq, a, target_start, target_i+1) by {
          reveal OpaqueSortedBy;
          if !left {
            assert SortedBy(leq, a[target_start..target_i+1]) by {
              MainMergeLoopBranchBPreservesSortedByInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_i, right_bound, target_start, target_i, target_bound);
            }
          }
        }

        assert InvPermB : !left ==> InvariantIsPerm(a, cache, snap, left_i, left_bound, right_i+1, right_bound, target_start, target_i+1, target_bound) by {
          hide SortedBy;
          if !left {
            // assert multiset(a[..target_start]) + multiset(a[target_start..target_i+1]) + multiset(cache[left_i..left_bound]) + multiset(a[right_i+1..right_bound]) + multiset(a[target_bound..]) == multiset(snap) by {
            assert InvariantIsPerm(a, cache, snap, left_i, left_bound, right_i+1, right_bound, target_start, target_i+1, target_bound) by {
              reveal InvariantIsPerm;
              MainMergeLoopBranchBPreservesPermutationInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_i, right_bound, target_start, target_i, target_bound);
            }
          }
        }

        if !left {
          target_i := target_i + 1;
          right_i := right_i + 1;
        }

        assert target_i > target_start ==> left_i < left_bound ==> leq(a[target_i - 1], cache[left_i]) by {
          reveal InvSortA1;
          reveal InvSortB1;
        }

        assert target_i > target_start ==> right_i < right_bound ==> leq(a[target_i - 1], a[right_i]) by {
          reveal InvSortA2;
          reveal InvSortB2;
        }

        assert OpaqueSortedBy(leq, a, target_start, target_i) by {
          reveal InvSortA3;
          reveal InvSortB3;
          reveal OpaqueSortedBy;
        }

        assert InvariantIsPerm(a, cache, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound) by {
          hide SortedBy;
          reveal InvPerm;
          reveal InvPermB;
        }

        assert OpaqueSortedBy(leq, cache, left_i, left_bound) by {
          reveal OpaqueSortedBy;
        }

        assert OpaqueSortedBy(leq, a, right_i, right_bound) by {
          reveal OpaqueSortedBy;
        }
      }

      assert LeftOrRight: !(left_i < left_bound) || !(right_i < right_bound);
      assert LeftOrRightEq: left_i == left_bound || right_i == right_bound by {
        reveal LeftOrRight;
      }

      // if right is exhausted copy left
      while left_i < left_bound
        // indices invariants
        invariant left_start <= left_i <= left_bound
        invariant (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
        invariant target_start <= target_i <= target_bound

        // left and right invariants
        invariant OpaqueSortedBy(leq, cache, left_i, left_bound)
        invariant a[right_i..right_bound] == snap[right_i..right_bound]
        invariant OpaqueSortedBy(leq, a, right_i, right_bound)

        // bridge: last placed element is <= both candidates
        invariant target_i > target_start ==>
                    left_i < left_bound ==>
                      leq(a[target_i - 1], cache[left_i])

        invariant target_i > target_start ==>
                    right_i < right_bound ==>
                      leq(a[target_i - 1], a[right_i])

        // is sorted
        invariant OpaqueSortedBy(leq, a, target_start, target_i)

        // is perm
        invariant InvariantIsPerm(a, cache, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound)
      {
        a[target_i] := cache[left_i];
        left_i := left_i + 1;
        target_i := target_i + 1;

        assert OpaqueSortedBy(leq, cache, left_i, left_bound) by {
          reveal OpaqueSortedBy;
        }
        assert OpaqueSortedBy(leq, a, right_i, right_bound) by {
          reveal OpaqueSortedBy;
        }
        assert OpaqueSortedBy(leq, a, target_start, target_i) by {
          reveal OpaqueSortedBy;
        }
        assert target_i > target_start ==>
            left_i < left_bound ==>
              leq(a[target_i - 1], cache[left_i]) by {
          reveal OpaqueSortedBy;
        }

        assert InvariantIsPerm(a, cache, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound) by {
          assert right_i == right_bound by {
            reveal LeftOrRight;
            reveal LeftOrRightEq;
          }
          reveal InvariantIsPerm;
          if left_i < left_bound {
            CopyLeftPreservesPermutationInvariant(leq, a, cache, snap, left_start, left_i, left_bound, right_start, right_bound, target_start, target_i, target_bound);
          }
        }
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

          // is sorted
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
