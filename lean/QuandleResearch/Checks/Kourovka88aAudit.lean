import QuandleResearch.Proofs.Kourovka88a.Heights

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

#print axioms letterWeight_pos
#print axioms rawWeight_append
#print axioms length_le_rawWeight
#print axioms rawWeight_eq_zero_iff
#print axioms weightedLength_eq_zero_iff
#print axioms mem_letters
#print axioms mem_boundedWords
#print axioms mem_weightedBallCover
#print axioms weightedLength_commWord
#print axioms commWord_ne_one
#print axioms answer_of_weighted_survival
#print axioms heightRelator_one
#print axioms heightRelator_mem_of_one
#print axioms normalClosure_all_heights

end QuandleResearch.Issue070
