import QuandleResearch.Proofs.Kourovka88a.Greedy

/-! Exact statement audit and dependency report. These are audits of the
conditional reductions, NOT an audit of a proof of the existential target. -/
namespace QuandleResearch.Issue070

example : answer ↔
    (∃ (G : Type) (_ : Group G), ¬ IsCyclic G ∧ Group.FG G ∧
      ∃ a : G, ∀ g : G, ∃ n : ℤ, IsConj g (a ^ n)) := Iff.rfl

#print axioms good_iff_quotient
#print axioms mem_limit_iff
#print axioms limit_normal
#print axioms answer_of_chain
#print axioms greedy_cover
#print axioms answer_of_greedy_relators

#print axioms nextRelator_eq
#print axioms nextRelator_eq_one
#print axioms adjoin_eq_of_mem
#print axioms greedyStages_normal
#print axioms greedyStages_mono
#print axioms greedyStages_progress
#print axioms greedyStages_strict_of_bad
#print axioms greedyStages_stationary
#print axioms greedyStages_cover
#print axioms answer_of_greedyStages

end QuandleResearch.Issue070
