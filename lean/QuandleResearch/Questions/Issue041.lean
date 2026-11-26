import QuandleResearch.Theory.Interfaces

/-!
# Issue 41: BNN Question 8 (2013) — automorphism versus endomorphism twisted classes
https://github.com/555tery/quandle-orbit-series/issues/41

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 34..

## Target
Does a group exist for which [e]_φ is a subgroup for every automorphism φ, but [e]_θ fails to be a subgroup for some endomorphism θ?

## Source context / leads for later audit
Related Question 5(a,b).
-/

namespace QuandleResearch.Issue041
noncomputable section

def question : Prop := ∃ (G : Type) (_ : Group G), AllAut G ∧ ¬ AllEnd G

end
end QuandleResearch.Issue041
