import QuandleResearch.Basic.Biquandle

/-! Switch convention of Fenn–Jordan-Santana–Kauffman, as stated in
problem-28a/free-biquandle.tex, section 2. This does not assert the equivalence
with the BNS convention; that is a separate mathematical result. -/
namespace QuandleResearch
noncomputable section

def switch12 {X : Type} (r : X × X → X × X) (p : X × X × X) : X × X × X :=
  let q := r (p.1,p.2.1)
  (q.1,q.2,p.2.2)
def switch23 {X : Type} (r : X × X → X × X) (p : X × X × X) : X × X × X :=
  let q := r p.2
  (p.1,q.1,q.2)
def BraidEquation {X : Type} (r : X × X → X × X) : Prop :=
  ∀ p, switch12 r (switch23 r (switch12 r p)) =
    switch23 r (switch12 r (switch23 r p))
structure StrongBiquandle where
  carrier : Type
  switch : Equiv.Perm (carrier × carrier)
  braid : BraidEquation switch
  downBijective : ∀ a, Function.Bijective (fun b => (switch (a,b)).1)
  upBijective : ∀ b, Function.Bijective (fun a => (switch (a,b)).2)
  fixedFirst : ∀ a, ∃! b, switch (a,b) = (a,b)
  fixedSecond : ∀ b, ∃! a, switch (a,b) = (a,b)
namespace StrongBiquandle
def Hom (A B : StrongBiquandle) (f : A.carrier → B.carrier) : Prop :=
  ∀ a b, let r := A.switch (a,b)
         B.switch (f a,f b) = (f r.1,f r.2)
def Iso (A B : StrongBiquandle) : Prop :=
  ∃ e : A.carrier ≃ B.carrier, A.Hom B e
def FreeOn (A : StrongBiquandle) {X : Type} (gen : X → A.carrier) : Prop :=
  ∀ (B : StrongBiquandle) (f : X → B.carrier),
    ∃! h : A.carrier → B.carrier, A.Hom B h ∧ ∀ x, h (gen x) = f x
end StrongBiquandle
namespace Biquandle
/-- The switch formula used in the repository research note. -/
def switchMap (B : Biquandle) (a b : B.carrier) : B.carrier × B.carrier :=
  let u := (B.beta a).symm b
  (u, B.beta u (B.associated.op a u))
end Biquandle
end
end QuandleResearch
