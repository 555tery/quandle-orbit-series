import QuandleResearch.Proofs.Kourovka88a.WeightedGreedy

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

#print axioms exists_minBad
#print axioms mem_badBall
#print axioms badBall_subset
#print axioms badBall_card_decreases
#print axioms weighted_cover
#print axioms weightedRelator_eq
#print axioms weightedStages_normal
#print axioms weightedStages_mono
#print axioms weightedStages_progress
#print axioms weightedStages_cover
#print axioms answer_of_weightedStages
#print axioms answer_of_weightedStages_short

#print axioms weightedStages_eq_stage
#print axioms weightedRankHeightRelator_one
#print axioms weightedRankHeightRelator_mem
#print axioms weightedHeightStage_eq
#print axioms answer_of_heightStages_short

#print axioms rawWeight_le_of_sublist
#print axioms weightedLength_mk_le
#print axioms weightedLength_mul_le
#print axioms reduce_positive
#print axioms toWord_positiveWord
#print axioms positiveWord_append
#print axioms weightedLength_positive_mul
#print axioms rawWeight_replicate
#print axioms weightedLength_a_zpow
#print axioms weightedLength_b_zpow
#print axioms positiveWord_repeat
#print axioms weightedLength_positive_pow
#print axioms positiveWord_longBlock
#print axioms weightedLength_longBlock

#print axioms adjacent_eq_odd
#print axioms no_odd_cube
#print axioms cube_even_descend
#print axioms cubeFree_of_binary_rec
#print axioms thueMorse_even
#print axioms thueMorse_odd
#print axioms thueMorse_cubeFree
#print axioms thueLetter_eq_iff
#print axioms thuePrefix_length
#print axioms thuePrefix_get
#print axioms thuePrefix_cubeFree

#print axioms exists_eligiblePrefixEnd_after
#print axioms nextPrefixEnd_spec
#print axioms nextPrefixEnd_min
#print axioms prefixEnd_eligible
#print axioms prefixEnd_lt_succ
#print axioms prefixEnd_gt_index
#print axioms gubaPrefix_odd_length
#print axioms gubaPrefix_last
#print axioms gubaPrefix_first
#print axioms gubaPrefix_second
#print axioms positiveWord_length_le
#print axioms exists_gubaEvenPrefix_weight_gt
#print axioms chooseEvenPrefixIndex_spec
#print axioms chooseEvenPrefixIndex_min
#print axioms positiveWord_longRaw
#print axioms weightedLength_longRaw_twice
#print axioms weightedLength_longConjugator_twice

#print axioms markerInterval_of_large
#print axioms positiveWeight_append
#print axioms positiveWeight_nil
#print axioms positiveWeight_zero_imp_nil
#print axioms prefix_of_positiveWeight_le
#print axioms factor_of_weighted_interval
#print axioms longRaw_prefix
#print axioms longRaw_resolvent_factor
#print axioms positiveWeight_separator
#print axioms positiveWeight_resolvent_end
#print axioms guba19_threshold
#print axioms guba19_resolvent

end QuandleResearch.Issue070
