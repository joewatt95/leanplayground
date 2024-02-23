import Leanplayground.Primes.Utils

namespace LazyList

open Utils

/-
Lazy, possible infinite, lists as an inductive type with a type constructor
that's polymorphic over type universes.

Γ ⊢ ok
------------------------------
Γ ⊢ LazyList : Type u → Type u
                                                  Γ ⊢ head : α
Γ ⊢ α : Type u                Γ ⊢ α : Type u      Γ ⊢ tail : LazyList α
---------------------         -------------------------------------------------
Γ ⊢ nil : LazyList α             Γ ⊢ head L:: ↑tail : LazyList α

Note that Lean utilizes the isomorphism of types/categories (β ≅ Unit → β) in
order to coerce at compile-time (b : β) to the function (λ _ => b) so that
we may simply write (cons x lazyList) instead of
(cons x (Thunk.mk <| λ _ => lazyList))
-/
inductive LazyList : Type u → Type u where
| nil : LazyList α
| cons : α → Thunk (LazyList α) → LazyList α
deriving Inhabited

-- What precedence level should this be at?
macro:65 head:term "L::" tail:term : term =>
  `(LazyList.cons $head $tail)

/-
The Stream type class is used to model an iterator interface.
This enables the use of the data type in for ... in loops.

TODO: Atm, getting the next element of the stream evaluates the caddr alongside
the cadr. Fix this.
-/
instance : Stream (LazyList α) α where
  next?
    | x L:: xs => some ⟨x, xs.get⟩
    | _ => none

instance : ToStream (LazyList α) (LazyList α)  where
  toStream := id

def LazyList.head [Inhabited α] : LazyList α → α
| x L:: _ => x
| _ => default

def LazyList.tail : LazyList α → LazyList α
| _ L:: xs => xs.get
| xs => xs

def LazyList.empty : LazyList α := LazyList.nil

def LazyList.isEmpty : LazyList α → Bool
| LazyList.nil => true
| _ => false

@[simp]
def LazyList.take : Nat → LazyList α → List α
| n + 1, x L:: xs => x :: take n xs.get
| _, _ => []

def LazyList.take' : Nat → LazyList α → Array α
| n, xs => Id.run do
  let mut acc := #[]
  for x in xs, _ in [0 : n] do
    acc := acc.push x
  return acc

/-
Return type is polymorphic over a type universe u and a type constructor
m : Type u → Type.
-/
def LazyList.nth {α : Type u} {m : Type u → Type} [Pure m] [Inhabited <| m α]
  : Nat → LazyList α → m α
| n, xs => Id.run do
  for x in xs, index in [0 : n + 1] do
    if index = n then
      return pure x
  return default

-- def LazyList.nth' {m : Type u → Type} [Pure m] [Inhabited <| m α]
--   : Nat → LazyList α → Nat × m α
--   | n, xs => Id.run do
--     let mut index := 0
--     let mut result := ⟨index, default⟩
--     for x in xs do
--       if index = n then
--         result := ⟨n, pure x⟩
--         break
--       index := index + 1
--     return result

class ToLazyList (m : Type u → Type v) (α : Type u) where
  toLazyList : m α → LazyList α

instance : ToLazyList LazyList α where
  toLazyList := id

-- Note that this eagerly evaluates the whole stream to reverse it into a list,
-- which it then reverses into a lazy list.
instance [Stream (m α) α] : ToLazyList m α where
  toLazyList xs := Id.run do
    let mut reversed := default
    let mut result := default
    for x in xs do
      reversed := x :: reversed
    for x in reversed do
      result := x L:: result
    return result

@[simp]
def LazyList.map (f : α → β) : LazyList α → LazyList β
| x L:: xs => f x L:: map f xs.get
| _ => LazyList.nil

def LazyList.head? {m : Type u → Type} [Pure m] [Inhabited <| m α]
  : LazyList α → m α
| xs => Id.run do
  for x in xs, _ in [0] do
    return pure x
  return default

@[simp]
def map2 (op : α → β → γ) : LazyList α → LazyList β → LazyList γ
| x L:: xs, y L:: ys => (x <:op:> y) L:: map2 op xs.get ys.get
| _, _ => LazyList.nil

@[simp]
def LazyList.concat : LazyList α → LazyList α → LazyList α
| LazyList.nil, ys => ys
| x L:: xs, ys => x L:: xs.get <:concat:> ys

@[simp]
def LazyList.join : LazyList (LazyList α) -> LazyList α
| LazyList.nil => LazyList.nil
| LazyList.nil L:: xss => LazyList.join xss.get
| (x L:: xs) L:: xss => -- x L:: (xs.get <:concat:> LazyList.join xss.get)
  sorry
  -- xs <:concat:> (xss |>.get |> join)

/-
  This is based on:
  https://github.com/leanprover/lean4-samples/blob/main/ListComprehension/ListComprehension.lean
-/
declare_syntax_cat compClause
syntax "for" term "in" term : compClause
syntax "if" term : compClause
syntax "L[" term " | " compClause,* "]" : term
syntax "L[" term,* "]" : term

macro_rules
| `(L[]) => `(LazyList.nil)
| `(L[$t]) => `($t L:: ⟨λ _ => LazyList.nil⟩)
| `(L[$t, $ts,*]) => `($t L:: L[$ts,*])
| `(L[$t |]) => `(pure $t)
| `(L[$t | for $x in $xs]) => `(
    $xs |>.map (λ $x => $t)
  )
| `(L[$t | if $x]) => `(if $x then pure $t else LazyList.nil)
| `(L[$t | $c, $cs,*]) => `(LazyList.join L[L[$t | $cs,*] | $c])

instance : Monad LazyList where
  pure x := L[x]
  map := LazyList.map
  -- seq fns xs := L[f x | for f in fns, for x in xs ()]
  bind xs f := xs |>.map f |>.join

/-
This is macro instead of a function because I don't know how to write a
polymorphic function whose type can be specialized to both
(id <$> x = x) and ((g ∘ f) <$> x = g <$> f <$> x)
As a macro, this gets expanded first before the type checking is done.
-/
-- macro "lawfulFunctorLazyList" : term => `(
--   let rec proof
--     | LazyList.nil => rfl
--     | _ L:: xs =>
--       -- Apply inductive hypothesis via a recursive call.
--       have := proof xs.get
--       -- Finish off with simplifications and rewriting.
--       show _ by simp [Thunk.get, (. <$> .)] at *; rw [this];
--   proof
-- )

-- instance : LawfulFunctor LazyList where
--   -- id <$> x = x
--   id_map := lawfulFunctorLazyList
--   -- (g ∘ f) <$> x = g <$> f <$> x
--   comp_map _ _ := lawfulFunctorLazyList
--   -- Not sure what this last law is for.
--   map_const := show _ by simp [Functor.mapConst, (. <$> .)]

instance : LawfulMonad LazyList where
  -- Not sure what this is for.
  map_const := by simp [Functor.mapConst, (. <$> .)]
  -- id <$> x L:: xs = x L:: xs
  id_map :=
    let rec go
      | L[] => rfl
      | _ L:: xs =>
        have := go xs.get
        by simp [Thunk.get, (. <$> .)] at *; rw [this]
    go
  seqLeft_eq := by
    unfold SeqLeft.seqLeft
    unfold Applicative.toSeqLeft
    unfold Monad.toApplicative
    unfold instMonadLazyList
    simp [(. <$> .), LazyList.join, LazyList.map] at *
    sorry
  seqRight_eq := sorry
  pure_seq := sorry
  bind_pure_comp := sorry
  bind_map := sorry
  pure_bind := sorry
  bind_assoc := sorry

    -- Id.run do
    -- let mut result := LazyList.nil
    -- for f in fns, x in xs () do
    --   result := f x L:: result
    -- return result

-- instance :
--   let inBounds lazyList index :=
--     lazyList
--     |>.nth' index
--     |>.snd
--     |> (. ≠ none)
--   GetElem (LazyList α) Nat α inBounds
--   where
--     getElem lazyList index h :=
--       lazyList
--       |>.nth' index
--       |>.snd
--       |> λ
--         | some x => x
--         | none => sorry

def pairwise (f : α → α → β) (xs : LazyList α) : LazyList β :=
  map2 f xs <| LazyList.tail xs

-- theorem thm1 : ∀ xs : List α, take xs.length (listToLazyList xs) = xs
--   | [] => rfl
--   | x :: xs => show _ by
--     -- Expand out all the definitions.
--     simp [List.foldr, Thunk.get, take]
--     -- Finish off the proof via a recursive call to the inductive hypothesis.
--     exact thm1 _

partial def iterate (f : α → α) (x : α) : LazyList α :=
  x L:: iterate f <| f x

-- This says that iterate produces infinite lists.
theorem thm_iterate {x : α}
-- We need an extra hypothesis that iterate is equal to its definition.
-- This is because it's a partial function which we can't prove will always
-- terminate properly.
-- Lean treats such functions as having opaque definitions because otherwise,
-- one may be able to use some diagonalization argument to prove ⊥
(h : ∀ {x : α} {f}, iterate f x = x L:: iterate f <| f x) :
∀ n, (iterate f x |>.take n |>.length) = n

| 0 =>
  have {xs} : xs.take 0 = [] := rfl
  have : (iterate f x).take 0 = [] := @this <| iterate f x
  by rw [this]; simp

| n + 1 =>
  have := calc
    (iterate f x |>.take (n + 1))
    = (x L:: iterate f <| f x).take (n + 1) := congrArg (. |>.take <| n + 1) h
  _ = x :: ((iterate f <| f x) |>.take n)   := rfl;
  calc
    (iterate f x |>.take (n + 1) |>.length)
    = (x :: ((iterate f <| f x) |>.take n) |>.length) := congrArg List.length this
  _ = ((iterate f <| f x) |>.take n |>.length) + 1 := rfl
  _ = n + 1 := congrArg (. + 1) <| thm_iterate h _

-- #eval iterate (. + 1) 0 |>.map (. + 1) |>.take 5
-- #eval L[x + 1 | for x in iterate id 0] |>.take 5

-- #eval L[(. + x) | for x in iterate (. + 1) 0] <*> iterate (. + 1) 0 |>.take 3

-- #check LazyList.take 3 $ L[x | for x in iterate (. + 1) 0, if true]

end LazyList
