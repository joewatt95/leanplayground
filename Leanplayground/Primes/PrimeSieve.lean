import Leanplayground.Primes.LazyList
import Leanplayground.Primes.Utils

open LazyList Utils

namespace PrimeSieve
/-
Sieve of Eratosthenes using lazy, infinite lists.

For more details, see:
https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf
-/

-- Ord is the typeclass for decidable linear orderings.
variable [Ord α]

/-
We need to use partial here to get Lean to stop complaining about the inability
to prove termination.
-/
private partial def merge : LazyList α → LazyList α → LazyList α
| LazyList.nil, xs
| xs, LazyList.nil => xs
| xs@(x L:: xs'), ys@(y L:: ys') =>
  open Ordering in
  match x <=>? y with
  | lt => x L:: xs'.get <:merge:> ys
  | eq => x L:: xs'.get <:merge:> ys'.get
  | gt => y L:: xs <:merge:> ys'.get

private partial def union : LazyList (LazyList α) → LazyList α
| (x L:: xs) L:: ys =>
  ys.get
    |> pairwise merge
    |> union
    |> (xs.get <:merge:> .)
    |> (x L:: .)
| _ => default

private def minus : LazyList α → LazyList α → LazyList α
| x L:: xs', ys@(y L:: ys') =>
  open Ordering in
  match x <=>? y with
  | lt => x L:: xs'.get <:minus:> ys
  | eq => xs'.get <:minus:> ys'.get
  | _ => default
| _, _ => default

partial def primes : LazyList Nat :=
  2 L:: oddPrimes ()
  where
    oddPrimes _ :=
      oddPrimes ()
        |>.map oddMultsFromSquare
        |> union
        |> (oddsFrom5 <:minus:> .)
        |> (3 L:: .)
    oddMultsFromSquare n := n |> (. ^2) |> iterate (. + 2 * n)
    oddsFrom5 := iterate (. + 2) 5

-- #eval primes.take' 100

end PrimeSieve