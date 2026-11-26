import QuandleResearch.Theory.Interfaces

/-!
# Issue 48: Gonçalves–Nasybullov §1 (2018) — parametric orientable quadratic equations in free groups
https://github.com/555tery/quandle-orbit-series/issues/48

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly formulated question
Gonçalves–Nasybullov, *Explicit solutions of certain orientable quadratic equations in free groups*, [arXiv:1808.08456v2, p.2, equation (2)](https://arxiv.org/pdf/1808.08456v2#page=2). Verified against the original PDF page.

## Target
For g,h,l and B_g=∏_{j=1}^g[x_j,y_j] in F_{2g}, determine for which integers c_i and words w_i the equation ∏_{j=1}^h[u_j,v_j]=∏_{i=1}^l(B_g^{w_i})^{c_i} admits a solution, and provide solutions when they exist. The source uses a^b=bab⁻¹ and [a,b]=aba⁻¹b⁻¹. This is explicitly asked in the text, not a numbered problem.

## Source context / leads for later audit
Proposition 1.1 gives a necessary bound when c_i have the same sign. The authors already mention Culler's general decision algorithm and prove explicit special-case constructions; the subsequent audit must distinguish a decision algorithm from the requested parametric criteria and explicit solutions.
-/

namespace QuandleResearch.Issue048
noncomputable section

def boundaryWord (g : Nat) : FreeGroup (Fin g × Bool) :=
  (List.ofFn (fun i : Fin g =>
    let x := FreeGroup.of (i, false)
    let y := FreeGroup.of (i, true)
    x*y*x⁻¹*y⁻¹)).prod
def equation {g h l : Nat} (c : Fin l → Int) (w : Fin l → FreeGroup (Fin g × Bool))
    (u v : Fin h → FreeGroup (Fin g × Bool)) : Prop :=
  (List.ofFn (fun j => u j * v j * (u j)⁻¹ * (v j)⁻¹)).prod =
    (List.ofFn (fun i => (w i * boundaryWord g * (w i)⁻¹) ^ c i)).prod
def verifiesCriterion {g h l : Nat} (criterion : (Fin l → Int) →
    (Fin l → FreeGroup (Fin g × Bool)) → Prop) : Prop :=
  ∀ c w, criterion c w ↔ ∃ (u v : Fin h → FreeGroup (Fin g × Bool)), equation c w u v
def verifiesConstruction {g h l : Nat} (criterion : (Fin l → Int) →
    (Fin l → FreeGroup (Fin g × Bool)) → Prop)
    (solution : (Fin l → Int) → (Fin l → FreeGroup (Fin g × Bool)) →
      (Fin h → FreeGroup (Fin g × Bool)) × (Fin h → FreeGroup (Fin g × Bool))) : Prop :=
  ∀ c w, criterion c w → equation c w (solution c w).1 (solution c w).2

end
end QuandleResearch.Issue048
