import QuandleResearch.Theory.Interfaces

/-!
# Issue 13: BCNW Question 5.7 — extension closure of orbit-series classes
https://github.com/555tery/quandle-orbit-series/issues/13

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / published open question
M. Bonatto, A. S. Crans, T. Nasybullov, G. T. Whitney, *Quandles with orbit series conditions*, Journal of Algebra (2021), [DOI](https://doi.org/10.1016/j.jalgebra.2020.09.026), [arXiv v3, Question 5.7](https://arxiv.org/html/2004.10227v3).
Are the classes \(\mathcal{OS}\) and \(\mathcal{OS}_\omega\) closed under extensions?
-/

namespace QuandleResearch.Issue013
noncomputable section

def extensionOS : Prop :=
  ∀ (Q B : Quandle) (f : Q.carrier → B.carrier), Q.Hom B f → Function.Surjective f →
    B.rack.OS Set.univ → (∀ b, Q.rack.OS {x | f x = b}) → Q.rack.OS Set.univ
def extensionOSomega : Prop :=
  ∀ (Q B : Quandle) (f : Q.carrier → B.carrier), Q.Hom B f → Function.Surjective f →
    B.rack.OSomega Set.univ → (∀ b, Q.rack.OSomega {x | f x = b}) → Q.rack.OSomega Set.univ

end
end QuandleResearch.Issue013
