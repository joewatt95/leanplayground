import Canonical

inductive MyNat
  | zero : MyNat
  | succ : MyNat → MyNat

def add (a : MyNat) : MyNat → MyNat
  | .zero => a
  | .succ b => .succ (add a b)

theorem add_comm' {a b : MyNat} :
  add a b = add b a :=
    MyNat.rec (motive := fun t ↦ add t b = add b t)
      (MyNat.rec (motive := fun t ↦ add MyNat.zero t = t) (Eq.refl MyNat.zero)
        (fun a a_ih ↦ by simp only [MyNat.succ.injEq, add.eq_2] <;> exact a_ih) b)
      (fun a a_ih ↦
        Eq.rec (motive := fun a_1 t ↦ add a.succ b = a_1.succ)
          (MyNat.rec (motive := fun t ↦ add a.succ t = (add a t).succ)
            (by simp only [MyNat.succ.injEq, add.eq_1] <;> exact Eq.refl a)
            (fun a_1 a_ih ↦ by simp only [MyNat.succ.injEq, add.eq_2] <;> exact a_ih) b)
          a_ih)
      a
