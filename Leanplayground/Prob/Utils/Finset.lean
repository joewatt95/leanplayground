import Mathlib.Data.Finset.Functor

namespace Finset

open Classical in
noncomputable def filterM {m : Type → Type u} [Monad m]
  (p : α → m Bool) (finset : Finset α)
  : m <| Finset α :=
  List.toFinset <$> finset.toList.filterM p

end Finset
