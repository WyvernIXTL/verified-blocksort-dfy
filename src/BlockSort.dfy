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



module BlockSortUnbound2 {
  import opened Std.Relations
  import Std.Collections.Seq

  import opened InsertionSortAdaptive


  module BlockSortUnboundImpl {
    import opened Std.Relations
    import Std.Collections.Seq

    import opened InsertionSortAdaptive


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


    ghost predicate {:opaque} OpaqueSortedBy<A(!new)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
      reads a
      requires TotalOrdering(leq)
      requires lo <= hi <= a.Length
    {
      SortedBy(leq, a[lo..hi])
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


    // merge two blocks together
    method {:isolate_assertions} Merge<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, mid: nat, hi: nat, cache: array<A>)
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

        var left := leq(cache[left_i], a[right_i]);

        if left {
          a[target_i] := cache[left_i];
        }

        assert left ==> IsPermutationInvariant(a, cache, cache_min_size, snap, left_i+1, left_bound, right_i, right_bound, target_start, target_i+1, target_bound) by {
          if left {
            assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i+1, left_bound, right_i, right_bound, target_start, target_i+1, target_bound) by {
              reveal IsPermutationInvariant;
              MultiSet5Slice(a[..], target_start, target_i + 1, right_i, target_bound);
              assert a[target_start..target_i] + [cache[left_i]] == a[target_start..target_i + 1];
              HeadOfCache(cache, left_i, left_bound);
              assert multiset(a[target_start..target_i + 1]) + multiset(cache[left_i + 1..left_bound]) == multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]);
            }
          }
        }

        if left {
          left_i := left_i + 1;
        }

        if !left {
          a[target_i] := a[right_i];
        }

        assert !left ==> IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i+1, right_bound, target_start, target_i+1, target_bound) by {
          if !left {
            assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i+1, right_bound, target_start, target_i+1, target_bound) by {
              reveal IsPermutationInvariant;
              assert a[target_start..target_i] + [a[right_i]] == a[target_start..target_i + 1];
              MultiSet5Slice(a[..], target_start, target_i + 1, right_i + 1, target_bound);
              HeadOfCache(a, right_i, right_bound);
              assert multiset(a[target_start..target_i + 1]) + multiset(a[right_i + 1..right_bound]) == multiset(a[target_start..target_i]) + multiset(a[right_i..right_bound]);
            }
          }
        }

        if !left {
          right_i := right_i + 1;
        }

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
        assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound) by { // EXPENSIVE
          reveal IsPermutationInvariant;
          // MultiSet5Slice(a[..], target_start, target_i, right_i, target_bound);
        }
        assert left ==> left_i < left_bound ==> leq(a[target_i - 1], cache[left_i]) by {
          reveal OpaqueSortedBy;
        }
        assert !left ==> right_i < right_bound ==> leq(a[target_i - 1], a[right_i]) by {
          reveal OpaqueSortedBy;
        }
      }

      assert LeftOrRight: !(left_i < left_bound) || !(right_i < right_bound);
      assert LeftOrRightEq: left_i == left_bound || right_i == right_bound by {
        reveal LeftOrRight;
      }
      assert FromLeftFollowsRightEq: left_i < left_bound ==> right_i == right_bound by {
        reveal LeftOrRight;
        reveal LeftOrRightEq;
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
        invariant IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound)
      {
        a[target_i] := cache[left_i];

        assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i+1, left_bound, right_i, right_bound, target_start, target_i+1, target_bound) by {
          reveal IsPermutationInvariant;
          MultiSet5Slice(a[..], target_start, target_i + 1, right_i, target_bound);
          assert a[target_start..target_i] + [cache[left_i]] == a[target_start..target_i + 1];
          HeadOfCache(cache, left_i, left_bound);
          assert multiset(a[target_start..target_i + 1]) + multiset(cache[left_i + 1..left_bound]) == multiset(a[target_start..target_i]) + multiset(cache[left_i..left_bound]);
        }

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
        assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i, right_bound, target_start, target_i, target_bound) by { // EXPENSIVE
          reveal IsPermutationInvariant;
        }
        assert target_i > target_start ==> left_i < left_bound ==> leq(a[target_i - 1], cache[left_i]) by {
          reveal OpaqueSortedBy;
        }
      }


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
          assert a[target_i] == a[right_i];

          right_i := right_i + 1;
          target_i := target_i + 1;

          assert OpaqueSortedBy(leq, a, right_i, right_bound) by {
            reveal OpaqueSortedBy;
          }
          assert OpaqueSortedBy(leq, a, target_start, target_i) by {
            reveal OpaqueSortedBy;
          }
          assert target_i > target_start ==> right_i < right_bound ==> leq(a[target_i - 1], a[right_i]) by {
            reveal OpaqueSortedBy;
          }
        }
      }

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

          assert IsPermutationInvariant(a, cache, cache_min_size, snap, left_i, left_bound, right_i+1, right_bound, target_start, target_i+1, target_bound) by {
            reveal IsPermutationInvariant;
            assert a[target_start..target_i] + [a[right_i]] == a[target_start..target_i + 1];
            MultiSet5Slice(a[..], target_start, target_i + 1, right_i + 1, target_bound);
            HeadOfCache(a, right_i, right_bound);
            assert multiset(a[target_start..target_i + 1]) + multiset(a[right_i + 1..right_bound]) == multiset(a[target_start..target_i]) + multiset(a[right_i..right_bound]);
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
      requires a.Length <= b.Length
      requires lo < hi <= a.Length
      ensures b[..hi-lo] == a[lo..hi]
    {
      forall i | 0 <= i < hi-lo {
        b[i] := a[lo+i];
      }
    }

  }



}
