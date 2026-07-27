// Copyright (C) 2026 Adam McKellar <dev@mckellar.eu>
// 
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.



/*/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\

  Verified Block Sort in Dafny

  This module contains a verified implementation of block sort in the programming language Dafny.

  This implementation of block sort is not in place! Instead a separate array is used to maintain a copy of a block.
  Wikipedia mentions that variant of block sort "turns into a full-speed merge sort since all of the A subarrays 
  will fit into it."[^1] The reason for choosing this variant is simply complexity.

  If you are interested in block sort, have a look at these ressources:
  - <https://every-algorithm.github.io/2023/11/27/block_sort.html>
  - <https://en.wikipedia.org/wiki/Block_sort>

  I expect, without having done an analysis:
    
  | worst-case performance      | O(n log n) |
  | --------------------------- | ---------- |
  | worst-case space complexity | O(n/2)     |


  [^1]: https://en.wikipedia.org/wiki/Block_sort#Variants

/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\*/


include "InsertionSort.dfy"


module VerifiedBlockSort.BlockSortUnbound {
  import opened Std.Relations


  /* ------------------------------------------------------------------------ */
  /*                           Merge Implementation                           */
  /* ------------------------------------------------------------------------ */

  module BlockSortUnboundMergeImpl {
    import opened Std.Relations


    /* ------------------------ Lemma and Predicates ------------------------ */

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

    lemma TailOfArray<A(!new)>(a: array<A>, lo: nat, hi: nat)
      requires lo < hi < a.Length
      ensures a[lo..hi] + [a[hi]] == a[lo..hi+1]
    {}

    lemma TailEqFollowsFromSeqEq<A(!new)>(a: seq<A>, b: seq<A>)
      requires a == b
      requires |a| > 0 || |b| > 0
      ensures a[1..] == b[1..]
    {}

    ghost predicate {:opaque} OpaqueSortedBy<A(!new)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
      reads a
      requires TotalOrdering(leq)
      requires lo <= hi <= a.Length
    {
      SortedBy(leq, a[lo..hi])
    }

    ghost predicate {:opaque} OpaqueSortedBySeq<A(!new)>(leq: (A, A) -> bool, a: seq<A>)
      requires TotalOrdering(leq)
    {
      SortedBy(leq, a)
    }

    lemma OpaqueSortedBySeqFromOpaqueSortedBy<A(!new)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
      requires TotalOrdering(leq)
      requires lo <= hi <= a.Length
      requires OpaqueSortedBy(leq, a, lo, hi)
      ensures OpaqueSortedBySeq(leq, a[lo..hi])
    {
      reveal OpaqueSortedBy;
      reveal OpaqueSortedBySeq;
    }

    lemma HeadLeqNextIfOpaqueSortedBySeq<A(!new)>(leq: (A, A) -> bool, a: seq<A>)
      requires TotalOrdering(leq)
      requires OpaqueSortedBySeq(leq, a)
      requires 2 <= |a|
      ensures leq(a[0], a[1])
    {
      reveal OpaqueSortedBySeq;
    }

    lemma SortedByAddElement<A(!new)>(leq: (A, A) -> bool, a: array<A>, target_start: nat, target_i: nat)
      requires TotalOrdering(leq)
      requires 0 <= target_start < target_i <= a.Length
      requires SortedBy(leq, a[target_start..target_i-1])
      requires target_i - target_start >= 2
      requires leq(a[target_i-2], a[target_i-1])
      ensures SortedBy(leq, a[target_start..target_i])
    {
      assert forall i | target_start <= i < target_i-1 :: leq(a[i], a[target_i-2]);
      assert forall i | target_start <= i < target_i-1 :: leq(a[i], a[target_i-2]) ==>
                                                            leq(a[target_i-2], a[target_i-1]) ==>
                                                              forall i | target_start <= i < target_i-1 :: leq(a[i], a[target_i-1]);
      assert forall i | target_start <= i < target_i-1 :: leq(a[i], a[target_i-1]) ==> SortedBy(leq, a[target_start..target_i]);
    }

    lemma OpaqueSortedByAddTail<A(!new)>(leq: (A, A) -> bool, snap_target_seq: seq<A>, a: array<A>, target_start: nat, target_i: nat, x: A, y: A)
      requires TotalOrdering(leq)
      requires 0 <= target_start < target_i < a.Length
      requires a[target_start..target_i-1] == snap_target_seq
      requires OpaqueSortedBySeq(leq, snap_target_seq)
      requires 2 <= target_i - target_start
      requires leq(a[target_i-2], x)
      requires leq(a[target_i-2], y)
      ensures a[target_i-1] == x ==> OpaqueSortedBy(leq, a, target_start, target_i)
      ensures a[target_i-1] == y ==> OpaqueSortedBy(leq, a, target_start, target_i)
    {
      reveal OpaqueSortedBy;
      reveal OpaqueSortedBySeq;
      if a[target_i-1] == x {
        SortedByAddElement(leq, a, target_start, target_i);
      }
      if a[target_i-1] == y {
        SortedByAddElement(leq, a, target_start, target_i);
      }
    }

    lemma OpaqueSortedByAddTailSingle<A(!new)>(leq: (A, A) -> bool, snap_target_seq: seq<A>, a: array<A>, target_start: nat, target_i: nat, x: A)
      requires TotalOrdering(leq)
      requires 0 <= target_start < target_i <= a.Length
      requires a[target_start..target_i-1] == snap_target_seq
      requires OpaqueSortedBySeq(leq, snap_target_seq)
      requires 2 <= target_i - target_start
      requires leq(a[target_i-2], a[target_i-1])
      ensures OpaqueSortedBy(leq, a, target_start, target_i)
    {
      reveal OpaqueSortedBy;
      reveal OpaqueSortedBySeq;
      SortedByAddElement(leq, a, target_start, target_i);
    }

    lemma OpaqueSortedByFromLeq<A(!new)>(leq: (A, A) -> bool, a: array<A>, target_start: nat, target_i: nat)
      requires TotalOrdering(leq)
      requires 0 <= target_start < target_i < a.Length
      requires target_start + 1 == target_i
      requires leq(a[target_start], a[target_start+1])
      ensures OpaqueSortedBy(leq, a, target_start, target_i)
    {
      reveal OpaqueSortedBy;
    }

    lemma OpaqueSortedByFromElement<A(!new)>(leq: (A, A) -> bool, a: array<A>, target_start: nat)
      requires TotalOrdering(leq)
      requires 0 <= target_start < a.Length
      ensures OpaqueSortedBy(leq, a, target_start, target_start+1)
    {
      reveal OpaqueSortedBy;
    }

    lemma OpaqueSortedByEmpty<A(!new)>(leq: (A, A) -> bool, a: array<A>, target_start: nat, target_i: nat)
      requires TotalOrdering(leq)
      requires 0 <= target_start == target_i <= a.Length
      ensures OpaqueSortedBy(leq, a, target_start, target_i)
    {
      reveal OpaqueSortedBy;
    }

    lemma OpaqueSortedByTailFromBackup<A(!new)>(leq: (A, A) -> bool, backup: seq<A>, a: array<A>, lo: nat, hi: nat)
      requires TotalOrdering(leq)
      requires OpaqueSortedBySeq(leq, backup)
      requires lo <= hi <= a.Length
      requires 2 <= |backup|
      requires backup[1..] == a[lo..hi]
      ensures OpaqueSortedBy(leq, a, lo, hi)
    {
      reveal OpaqueSortedBy;
      reveal OpaqueSortedBySeq;
    }

    lemma  OpaqueSortedByFromBackup<A(!new)>(leq: (A, A) -> bool, backup: seq<A>, a: array<A>, lo: nat, hi: nat)
      requires TotalOrdering(leq)
      requires OpaqueSortedBySeq(leq, backup)
      requires lo <= hi <= a.Length
      requires backup == a[lo..hi]
      ensures OpaqueSortedBy(leq, a, lo, hi)
    {
      reveal OpaqueSortedBy;
      reveal OpaqueSortedBySeq;
    }


    ghost predicate {:opaque} IsPermutation<A(!new)>(a: seq<A>, old_a: seq<A>)
    {
      multiset(a) == multiset(old_a)
    }

    ghost predicate {:opaque} IsPermutationInvariant<A(!new)>(a: array<A>, cache: array<A>, cache_min_size: nat, snap: seq<A>, left_i: nat, left_bound: nat,
                                                              right_i: nat, right_bound: nat, target_start: nat, target_i: nat, target_bound: nat)
      reads a
      reads cache

      // invariants
      requires |snap| == a.Length
      requires cache_min_size <= cache.Length

      requires left_i <= left_bound <= cache_min_size
      requires right_i <= right_bound <= a.Length
      requires target_start <= target_i <= target_bound <= a.Length
    {
      multiset(a[..target_start]) + multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]) + multiset(a[right_i..right_bound]) + multiset(a[target_bound..]) == multiset(snap)
    }


    /* ------------------------ Merge Implementation ------------------------ */

    // merge two blocks together
    method Merge<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, mid: nat, hi: nat, cache: array<A>)
      modifies a

      // comparison predicate requirements
      requires TotalOrdering(leq)

      // indices requirements
      requires lo < mid < hi <= a.Length

      // cache requirements
      requires cache != a
      requires mid - lo <= cache.Length
      requires cache[0..mid-lo] == a[lo..mid]

      // requires sorted blocks
      requires OpaqueSortedBy(leq, a, lo, mid)
      requires OpaqueSortedBy(leq, a, mid, hi)

      // ensures sorted
      ensures OpaqueSortedBy(leq, a, lo, hi)

      // ensures is permutations
      ensures IsPermutation(a[..], old(a[..]))
    {
      ghost var snap := a[..];
      ghost var cache_min_size := mid - lo;
      assert cache_min_size <= cache.Length;

      var left_start: nat := 0;
      var left_i: nat := left_start;
      var left_bound: nat := mid - lo;
      var right_start: nat := mid;
      var right_i: nat := right_start;
      var right_bound: nat := hi;
      var target_start: nat := lo;
      var target_i: nat := target_start;
      var target_bound: nat := hi;

      // assert opaque preconditions of loop
      assert OpaqueSortedBy(leq, cache, left_i, left_bound) by {
        reveal OpaqueSortedBy;
      }
      assert OpaqueSortedBy(leq, a, right_i, right_bound) by {
        reveal OpaqueSortedBy;
      }
      assert OpaqueSortedBy(leq, a, target_start, target_i) by {
        reveal OpaqueSortedBy;
      }
      assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound) by {
        reveal IsPermutationInvariant;
        MultiSet5Slice(a[..], target_start, target_i, right_i, target_bound);
      }

      assert {:split_here} true;

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
        invariant IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound)
      {
        ghost var snap_left := cache[left_i..left_bound];
        assert LeftSortedBackup: OpaqueSortedBySeq(leq, snap_left) by {
          OpaqueSortedBySeqFromOpaqueSortedBy(leq, cache, left_i, left_bound);
        }
        ghost var snap_right := a[right_i..right_bound];
        assert RightSortedBackup: OpaqueSortedBySeq(leq, snap_right) by {
          OpaqueSortedBySeqFromOpaqueSortedBy(leq, a, right_i, right_bound);
        }
        ghost var snap_target := a[target_start..target_i];
        assert TargetSortedBackup: OpaqueSortedBySeq(leq, snap_target) by {
          OpaqueSortedBySeqFromOpaqueSortedBy(leq, a, target_start, target_i);
        }

        var left := leq(cache[left_i], a[right_i]);

        if left {
          a[target_i] := cache[left_i];
        }

        assert AUpdatedTailLeft: left ==> a[target_start..target_i] + [cache[left_i]] == a[target_start..target_i + 1];
        assert PermLeft: left ==> IsPermutationInvariant(a, cache, cache_min_size, snap, left_i+1, left_bound, right_i, right_bound, target_start, target_i+1, target_bound) by { // EXPENSIVE
          MultiSet5Slice(a[..], target_start, target_i + 1, right_i, target_bound);
          reveal AUpdatedTailLeft;
          HeadOfCache(cache, left_i, left_bound);
          reveal IsPermutationInvariant;
          assert {:focus} left ==> multiset(a[target_start..target_i + 1]) + multiset(cache[left_i + 1..left_bound]) == multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]);
        }

        assert RightDoesNotChangePersist: left ==> a[right_i..right_bound] == snap[right_i..right_bound];

        if left {
          left_i := left_i + 1;
        }

        if !left {
          a[target_i] := a[right_i];
        }

        assert AUpdatedTailRight: !left ==> a[target_start..target_i] + [a[right_i]] == a[target_start..target_i + 1];
        assert PermRight: !left ==> IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i+1, right_bound, target_start, target_i+1, target_bound) by { // EXPENSIVE
          MultiSet5Slice(a[..], target_start, target_i + 1, right_i + 1, target_bound);
          reveal AUpdatedTailRight;
          HeadOfCache(a, right_i, right_bound);
          reveal IsPermutationInvariant;
          assert {:focus} !left ==> multiset(a[target_start..target_i + 1]) + multiset(a[right_i + 1..right_bound]) == multiset(a[target_start..target_i]) + multiset(a[right_i..right_bound]);
        }

        assert RightDoesNotChangeUdate: !left ==> a[right_i+1..right_bound] == snap[right_i+1..right_bound] by {
          TailEqFollowsFromSeqEq(a[right_i..right_bound], snap[right_i..right_bound]);
        }

        if !left {
          right_i := right_i + 1;
        }

        target_i := target_i + 1;


        assert RightDoesNotChange: a[right_i..right_bound] == snap[right_i..right_bound] by {
          if left {
            reveal RightDoesNotChangePersist;
          } else {
            reveal RightDoesNotChangeUdate;
          }
        }
        assert SortedLeft: OpaqueSortedBy(leq, cache, left_i, left_bound) by {
          reveal LeftSortedBackup;
          if !left {
            OpaqueSortedByFromBackup(leq, snap_left, cache, left_i, left_bound);
          } else {
            if 2 <= |snap_left| {
              OpaqueSortedByTailFromBackup(leq, snap_left, cache, left_i, left_bound);
            } else {
              OpaqueSortedByEmpty(leq, cache, left_i, left_bound);
            }
          }
        }
        assert SortedRight: OpaqueSortedBy(leq, a, right_i, right_bound) by {
          reveal RightSortedBackup;
          if left {
            OpaqueSortedByFromBackup(leq, snap_right, a, right_i, right_bound);
          } else {
            if 2 <= |snap_right| {
              OpaqueSortedByTailFromBackup(leq, snap_right, a, right_i, right_bound);
            } else {
              OpaqueSortedByEmpty(leq, a, right_i, right_bound);
            }
          }
        }
        assert SortedTarget: OpaqueSortedBy(leq, a, target_start, target_i) by {
          if 2 <= target_i - target_start {
            reveal TargetSortedBackup;
            OpaqueSortedByAddTail(leq, snap_target, a, target_start, target_i, snap_left[0], snap_right[0]);
          } else if 2 == target_i - target_start {
            OpaqueSortedByFromLeq(leq, a, target_start, target_i);
          } else if 1 == target_i - target_start {
            OpaqueSortedByFromElement(leq, a, target_start);
          } else {
            OpaqueSortedByEmpty(leq, a, target_start, target_i);
          }
        }
        assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound) by {
          if left {
            reveal PermLeft;
          } else {
            reveal PermRight;
          }
        }
        assert left ==> left_i < left_bound ==> leq(a[target_i - 1], cache[left_i]) by {
          if left {
            if left_i < left_bound {
              reveal LeftSortedBackup;
              HeadLeqNextIfOpaqueSortedBySeq(leq, snap_left);
            }
          }
        }
        assert !left ==> right_i < right_bound ==> leq(a[target_i-1], a[right_i]) by {
          if !left {
            if right_i < right_bound {
              reveal RightSortedBackup;
              HeadLeqNextIfOpaqueSortedBySeq(leq, snap_right);
            }
          }
        }
        reveal SortedLeft;
        reveal SortedRight;
        reveal SortedTarget;
        reveal RightDoesNotChange;
      }

      assert LeftOrRight: !(left_i < left_bound) || !(right_i < right_bound);
      assert LeftOrRightEq: left_i == left_bound || right_i == right_bound by {
        reveal LeftOrRight;
      }
      assert FromLeftFollowsRightEq: left_i < left_bound ==> right_i == right_bound by {
        reveal LeftOrRight;
        reveal LeftOrRightEq;
      }

      assert {:split_here} true;


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
        invariant IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound)
      {
        ghost var snap_left := cache[left_i..left_bound];
        assert LeftSortedBackup: OpaqueSortedBySeq(leq, snap_left) by {
          OpaqueSortedBySeqFromOpaqueSortedBy(leq, cache, left_i, left_bound);
        }
        ghost var snap_target := a[target_start..target_i];
        assert TargetSortedBackup: OpaqueSortedBySeq(leq, snap_target) by {
          OpaqueSortedBySeqFromOpaqueSortedBy(leq, a, target_start, target_i);
        }

        a[target_i] := cache[left_i];

        assert AUpdatedTail: a[target_start..target_i] + [cache[left_i]] == a[target_start..target_i + 1] by {
          assert a[target_i] == cache[left_i];
          TailOfArray(a, target_start, target_i);
        }
        assert Perm: IsPermutationInvariant(a, cache, cache_min_size, snap, left_i+1, left_bound, right_i, right_bound, target_start, target_i+1, target_bound) by { // EXPENSIVE
          MultiSet5Slice(a[..], target_start, target_i + 1, right_i, target_bound);
          reveal AUpdatedTail;
          HeadOfCache(cache, left_i, left_bound);
          reveal IsPermutationInvariant;
          assert {:focus} multiset(a[target_start..target_i + 1]) + multiset(cache[left_i + 1..left_bound]) == multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]);
        }

        left_i := left_i + 1;
        target_i := target_i + 1;

        assert SortedLeft: OpaqueSortedBy(leq, cache, left_i, left_bound) by {
          reveal LeftSortedBackup;
          if 2 <= |snap_left| {
            OpaqueSortedByTailFromBackup(leq, snap_left, cache, left_i, left_bound);
          } else {
            OpaqueSortedByEmpty(leq, cache, left_i, left_bound);
          }
        }
        assert SortedRight: OpaqueSortedBy(leq, a, right_i, right_bound) by {
          OpaqueSortedByEmpty(leq, a, right_i, right_bound);
        }
        assert SortedTarget: OpaqueSortedBy(leq, a, target_start, target_i) by {
          if 2 <= target_i - target_start {
            reveal TargetSortedBackup;
            OpaqueSortedByAddTailSingle(leq, snap_target, a, target_start, target_i, snap_left[0]);
          } else if 2 == target_i - target_start {
            OpaqueSortedByFromLeq(leq, a, target_start, target_i);
          } else if 1 == target_i - target_start {
            OpaqueSortedByFromElement(leq, a, target_start);
          } else {
            OpaqueSortedByEmpty(leq, a, target_start, target_i);
          }
        }
        assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound) by {
          reveal Perm;
        }
        assert left_i < left_bound ==> leq(a[target_i - 1], cache[left_i]) by {
          if left_i < left_bound {
            reveal LeftSortedBackup;
            HeadLeqNextIfOpaqueSortedBySeq(leq, snap_left);
          }
        }
        reveal SortedLeft;
        reveal SortedRight;
        reveal SortedTarget;
      }

      assert {:split_here} true;

      // if left is exhausted assert goal by asserting right side is allready in place
      assert OpaqueSortedBy(leq, a, target_start, target_bound) by {
        var right_i := right_i;
        var target_i := target_i;

        while right_i < right_bound
          // indices invariants
          invariant right_start <= right_i <= right_bound
          invariant (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
          invariant target_start <= target_i <= target_bound

          // left and right invariants
          invariant a[right_i..right_bound] == snap[right_i..right_bound]
          invariant OpaqueSortedBy(leq, a, right_i, right_bound)

          // bridge: last placed element is <= both candidates
          invariant target_i > target_start ==>
                      right_i < right_bound ==>
                        leq(a[target_i - 1], a[right_i])

          // is sorted
          invariant OpaqueSortedBy(leq, a, target_start, target_i)
        {
          ghost var snap_right := a[right_i..right_bound];
          assert RightSortedBackup: OpaqueSortedBySeq(leq, snap_right) by {
            OpaqueSortedBySeqFromOpaqueSortedBy(leq, a, right_i, right_bound);
          }
          ghost var snap_target := a[target_start..target_i];
          assert TargetSortedBackup: OpaqueSortedBySeq(leq, snap_target) by {
            OpaqueSortedBySeqFromOpaqueSortedBy(leq, a, target_start, target_i);
          }

          assert a[target_i] == a[right_i];

          right_i := right_i + 1;
          target_i := target_i + 1;

          assert SortedRight: OpaqueSortedBy(leq, a, right_i, right_bound) by {
            reveal RightSortedBackup;
            if 2 <= |snap_right| {
              OpaqueSortedByTailFromBackup(leq, snap_right, a, right_i, right_bound);
            } else {
              OpaqueSortedByEmpty(leq, a, right_i, right_bound);
            }
          }
          assert SortedTarget: OpaqueSortedBy(leq, a, target_start, target_i) by {
            if 2 <= target_i - target_start {
              reveal TargetSortedBackup;
              OpaqueSortedByAddTailSingle(leq, snap_target, a, target_start, target_i, snap_right[0]);
            } else if 2 == target_i - target_start {
              OpaqueSortedByFromLeq(leq, a, target_start, target_i);
            } else if 1 == target_i - target_start {
              OpaqueSortedByFromElement(leq, a, target_start);
            } else {
              OpaqueSortedByEmpty(leq, a, target_start, target_i);
            }
          }
          assert right_i < right_bound ==> leq(a[target_i-1], a[right_i]) by {
            if right_i < right_bound {
              reveal RightSortedBackup;
              HeadLeqNextIfOpaqueSortedBySeq(leq, snap_right);
            }
          }
          reveal SortedRight;
          reveal SortedTarget;
        }
      }

      assert {:split_here} true;

      assert IsPermutation(a[..], snap) by {
        var right_i := right_i;
        var target_i := target_i;

        while right_i < right_bound
          // indices invariants
          invariant right_start <= right_i <= right_bound
          invariant (left_i - left_start) + (right_i - right_start) == (target_i - target_start)
          invariant target_start <= target_i <= target_bound

          // left and right invariants
          invariant a[right_i..right_bound] == snap[right_i..right_bound]

          // is perm
          invariant IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound)
        {
          assert a[target_i] == a[right_i];

          assert AUpdate: a[target_start..target_i] + [a[right_i]] == a[target_start..target_i + 1] by {
            TailOfArray(a, target_start, target_i);
          }
          assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i+1, right_bound, target_start, target_i+1, target_bound) by { // EXPENSIVE
            reveal IsPermutationInvariant;
            reveal AUpdate;
            MultiSet5Slice(a[..], target_start, target_i + 1, right_i + 1, target_bound);
            HeadOfCache(a, right_i, right_bound);
            assert {:focus} multiset(a[target_start..target_i + 1]) + multiset(a[right_i + 1..right_bound]) == multiset(a[target_start..target_i]) + multiset(a[right_i..right_bound]);
          }

          right_i := right_i + 1;
          target_i := target_i + 1;
        }

        reveal IsPermutationInvariant;
        MultiSet5Slice(a[..], target_start, target_i, right_i, target_bound);
        reveal IsPermutation;
      }
    }


    method CopySubarray<A(!new, ==)>(a: array<A>, lo: nat, hi: nat, b: array<A>)
      modifies b
      requires a != b
      requires hi - lo <= b.Length
      requires lo < hi <= a.Length
      ensures b[..hi-lo] == a[lo..hi]
    {
      forall i | 0 <= i < hi-lo {
        b[i] := a[lo+i];
      }
    }

    method MergeWithCopyToCache<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, mid: nat, hi: nat, cache: array<A>)
      modifies a
      modifies cache

      // comparison predicate requirements
      requires TotalOrdering(leq)

      // indices requirements
      requires lo < mid < hi <= a.Length

      // cache requirements
      requires cache != a
      requires mid - lo <= cache.Length

      // requires sorted blocks
      requires OpaqueSortedBy(leq, a, lo, mid)
      requires OpaqueSortedBy(leq, a, mid, hi)

      // ensures sorted
      ensures OpaqueSortedBy(leq, a, lo, hi)

      // ensures is permutations
      ensures IsPermutation(a[..], old(a[..]))
    {
      CopySubarray(a, lo, mid, cache);
      Merge(leq, a, lo, mid, hi, cache);
    }
  }


  /* ------------------------------------------------------------------------ */
  /*                         Block Sort Implementation                        */
  /* ------------------------------------------------------------------------ */

  module BlockSortUnboundImpl {
    import opened Std.Relations
    import Std.Collections.Seq
    import Std.Arithmetic.Power2
    import Std.Arithmetic.Power
    import Std.Arithmetic.Logarithm

    import opened InsertionSortAdaptive
    import opened BlockSortUnboundMergeImpl


    lemma Pow2_Log2(pow: nat)
      requires pow > 0
      ensures Power2.Pow2(Logarithm.Log(2, pow)) <= pow < Power2.Pow2(Logarithm.Log(2, pow) + 1)
    {}

    function FloorPowerOfTwo(n: nat): nat
    {
      Power2.Pow2(Logarithm.Log(2, n))
    }

    lemma FloorPowerOfTwoMinimum(min: nat, n: nat)
      requires 0 < min <= n
      requires min == FloorPowerOfTwo(min)
      ensures min <= FloorPowerOfTwo(n)
    {
      Logarithm.LemmaLogIsOrdered(2, min, n);
      Power.LemmaPowIncreases(2, Logarithm.Log(2, min), Logarithm.Log(2, n));
    }

    method BlockSort<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>)
      modifies a

      // requires total ordering
      requires TotalOrdering(leq)

      // ensures sorted
      // ensures OpaqueSortedBy(leq, a, 0, a.Length)

      // ensures is permutations
      // ensures IsPermutation(a[..], old(a[..]))
    {
      if a.Length <= 16 {
        InsertionSortAdaptive.InsertionSortArrayBy(leq, a);
        return;
      }

      var power_of_two := FloorPowerOfTwo(a.Length);
      var denominator := power_of_two / 16;

      assert 0 < denominator by {
        FloorPowerOfTwoMinimum(16, a.Length);
      }
      var numerator_step := a.Length % denominator;
      var integer_step := a.Length / denominator;
    }
  }
}
