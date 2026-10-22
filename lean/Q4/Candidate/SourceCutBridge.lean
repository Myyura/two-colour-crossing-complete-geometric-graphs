import Q4.Candidate.SourceSelectedEdges

/-! Integer-threshold bridge to represented MaxCut. Negative or excessively
large source thresholds are retained without natural-subtraction truncation. -/
namespace Q4.Candidate.SourceCutBridge
open Q4.Candidate.CoreEncoding Q4.Candidate.SourceSelectedEdges

theorem sourceOpt_threshold {α : Type*} (es : List (α × α)) (k : ℤ) :
    (sourceOpt es : ℤ) ≤ (es.length : ℤ)-k ↔
      ∃chi : α → Bool, k ≤ (Q4.cutCount es chi : ℤ) := by
  obtain ⟨⟨z,hz⟩,hmin⟩ := sourceOpt_spec es
  constructor
  · intro h
    have hsum : (Q4.monoCount es z : ℤ)+(Q4.cutCount es z : ℤ)=es.length := by
      exact_mod_cast Q4.mono_add_cut es z
    refine ⟨z,?_⟩
    rw [hz] at hsum
    omega
  · rintro ⟨chi,hchi⟩
    have hsum : (Q4.monoCount es chi : ℤ)+(Q4.cutCount es chi : ℤ)=es.length := by
      exact_mod_cast Q4.mono_add_cut es chi
    have hlo : (sourceOpt es : ℤ) ≤ Q4.monoCount es chi := by exact_mod_cast hmin chi
    omega

theorem permutation_threshold {n : ℕ} (pi : Equiv.Perm (Fin n)) (k : ℤ) :
    (sourceOpt (sourcePairs pi).toList : ℤ) ≤ ((sourcePairs pi).card : ℤ)-k ↔
      ∃chi : Fin n → Bool, k ≤ (Q4.cutCount (sourcePairs pi).toList chi : ℤ) := by
  simpa only [Finset.length_toList] using sourceOpt_threshold (sourcePairs pi).toList k

end Q4.Candidate.SourceCutBridge
#print axioms Q4.Candidate.SourceCutBridge.sourceOpt_threshold
#print axioms Q4.Candidate.SourceCutBridge.permutation_threshold
