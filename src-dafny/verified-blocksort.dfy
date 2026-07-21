
import opened Std.Relations


/* -------------------------- Verified Insert Sort -------------------------- */

// method InsertionSortShift<A(!new, ==)>(a: array<A>, j: nat)
//   modifies a
//   requires 0 < j < a.Length
//   ensures a[j] == a[j-1]
//   ensures a[..j] == old(a[..j])
//   ensures a[j+1..] == old(a[j+1..])
// {
//   a[j] := a[j-1];
// }

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

method InsertionSortInnerLoop<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, i: nat)
  modifies a
  requires TotalOrdering(leq)
  requires lo+1 < i < a.Length
  requires SortedBy(leq, a[lo..i])
  ensures SortedBy(leq, a[lo..i+1])
{
  var x := a[i];
  var j := i;

  SortedPrefix(leq, a[lo..j], old(a[lo..i]));

  while j > lo && !leq(a[j-1], x)
    invariant lo <= j <= i < a.Length
    invariant a[..j+1] == old(a[..j+1])
    invariant a[i+1..] == old(a[i+1..])
    invariant a[j+1..i+1] == old(a[j..i])
    invariant SortedBy(leq, a[lo..j])
    invariant SortedBy(leq, a[j+1..i+1])
    invariant forall y | j+1 <= y < i+1 :: leq(x, a[y])
  {
    a[j] := a[j-1];
    j := j - 1;

    SortedPrefix(leq, a[lo..j], old(a[lo..i]));
  }

  a[j] := x;

  CombineSort(leq, a[lo..j], a[j], a[j+1..i+1]);
  assert a[lo..i+1] == a[lo..j] + [a[j]] +  a[j+1..i+1];
  assert SortedBy(leq, a[lo..i+1]);
}



// method InsertionSort<A(!new, ==)>(leq: (A, A) -> bool, a: array<A>, lo: nat, hi: nat)
//   modifies a
//   requires TotalOrdering(leq)
//   requires lo < hi <= a.Length
//   ensures multiset(a[..]) == multiset(old(a[..]))
//   ensures SortedBy(leq, a[lo..hi])
// {
//   var i := lo + 1;

//   while i < hi
//     invariant lo <= i <= hi
//     invariant multiset(a[..]) == multiset(old(a[..]))
//     invariant SortedBy(leq, a[lo..i])
//   {
//     ghost var a_snap := a[..];
//     // assert a_snap[lo..i] == a[lo..i];
//     // assert SortedBy(leq, a_snap[lo..i]);

//     var x := a[i];
//     var j := i;

//     while j > lo && !leq(a[j-1], x)
//       invariant lo <= j < hi
//       invariant j <= i
//       invariant multiset{x} + (multiset(a[..]) - multiset{a[j]}) == multiset(old(a[..]))
//       invariant a_snap[lo..j] == a[lo..j]
//       invariant a_snap[j..i] == a[j+1..i+1]
//       invariant SortedBy(leq, a[lo..j])
//       invariant SortedBy(leq, a[j+1..i+1])
//       // invariant SortedBy(leq, a[j+1..i+1])
//       // invariant forall z | z in a_snap[j..i] :: leq(x, z)
//     {
//       a[j] := a[j-1];
//       j := j - 1;
//     }

//     // assert forall z | z in a_snap[lo..j] :: leq(z, x);

//     // assert a_snap[j] == a[j];
//     // assert SortedBy(leq, a[lo..j]);
//     // assert SortedBy(leq, a[j+1..i+1]);

//     a[j] := x;

//     // assert SortedBy(leq, a[lo..i+1]);

//     i := i + 1;

//     // assert SortedBy(leq, a[lo..i]);
//   }
// }
