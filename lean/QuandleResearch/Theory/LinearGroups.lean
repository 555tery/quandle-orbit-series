import QuandleResearch.Theory.Groups

namespace QuandleResearch
noncomputable section
abbrev GeneralLinear (K : Type) [Field K] (n : Nat) :=
  (Matrix (Fin n) (Fin n) K)ˣ
abbrev SpecialLinear (K : Type) [Field K] (n : Nat) :=
  Matrix.SpecialLinearGroup (Fin n) K

/-- Entrywise maps are pinned to an actual field automorphism, rather than
specified by arbitrary sets of group automorphisms. -/
def IsEntrywiseGL {K : Type} [Field K] {n : Nat} (psi : K ≃+* K)
    (phi : GeneralLinear K n ≃* GeneralLinear K n) : Prop :=
  ∀ A i j, (phi A).val i j = psi (A.val i j)
def IsEntrywiseSL {K : Type} [Field K] {n : Nat} (psi : K ≃+* K)
    (phi : SpecialLinear K n ≃* SpecialLinear K n) : Prop :=
  ∀ A i j, (phi A).val i j = psi (A.val i j)
end
end QuandleResearch
