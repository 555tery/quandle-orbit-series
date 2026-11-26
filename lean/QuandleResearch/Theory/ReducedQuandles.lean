import QuandleResearch.Theory.OrbitSeries

/-! Darné, Nilpotent quandles, arXiv:2205.02480v3, Definition 7.1,
Fact 7.3 and Definition 7.5; Inoue, arXiv:1205.5891, Definition 3.1.
The source's left notation is translated to the library's right notation.
The quotient is specified by its universal property, not assumed to exist
by a new axiom. -/
namespace QuandleResearch
noncomputable section
namespace Quandle

def Reduced (Q : Quandle) : Prop :=
  ∀ (x : Q.carrier) (g : Q.Inn), Q.op x (g.val x) = x

def IsReducedQuotient (Q R : Quandle) (p : Q.HomType R) : Prop :=
  R.Reduced ∧ Function.Surjective p ∧
    ∀ (S : Quandle), S.Reduced → ∀ f : Q.HomType S,
      ∃! h : R.HomType S, h.comp p = f

end Quandle

def reducedRelators {G : Type*} [Group G] (X : Set G) : Set G :=
  {z | ∃ x ∈ X, ∃ g : G, z = comm x (g*x*g⁻¹)}
abbrev ReducedGroup {G : Type*} [Group G] (X : Set G) :=
  G ⧸ Subgroup.normalClosure (reducedRelators X)

end
end QuandleResearch
