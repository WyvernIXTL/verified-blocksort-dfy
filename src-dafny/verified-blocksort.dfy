
import opened Std.Relations


/* -------------------------- Verified Insert Sort -------------------------- */

method InsertionSort<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
  modifies a
  requires TotalOrdering(leq)
  requires lo < hi <= a.Length
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures SortedBy(leq, a[lo..hi])
{
  var i := lo + 1;

  while i < hi
    invariant lo <= i <= hi
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var x := a[i];
    var j := i;

    while j > lo && !leq(a[j-1], x)
      invariant lo <= j < hi
      invariant multiset{x} + (multiset(a[..]) - multiset{a[j]}) == multiset(old(a[..]))
    {
      a[j] := a[j-1];
      j := j - 1;
    }

    a[j] := x;
    i := i + 1;
  }
}
