import Q4.Candidate.OriginalCapCrossing

/-! Exact finite palette counting on actual rational original-cap chords.
The selected endpoints range over two disjoint consecutive blocks. -/
namespace Q4.Candidate.OriginalCapAlternation
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open scoped BigOperators

theorem cap_ordered (a b c d : ℚ) (hab : a<b) (hcd : c<d) :
    ProperCross (original a) (original b) (original c) (original d) ↔
      (a<c ∧ c<b ∧ b<d) ∨ (c<a ∧ a<d ∧ d<b) := by
  by_cases hcb : c<b
  · by_cases had : a<d
    · rw [Q4.Candidate.OriginalCapCrossing.separated_order a b c d hab hcd had hcb]
      tauto
    · have hda : d≤a := le_of_not_gt had
      have hc : orient (original a) (original b) (original c)≥0 := by
        rw [original_vandermonde]
        have h1 : c-a≤0 := by linarith
        have h2 : c-b≤0 := by linarith
        have hprod := mul_nonneg_of_nonpos_of_nonpos h1 h2
        have : 0≤(b-a)*((c-a)*(c-b))/100 := by positivity
        nlinarith
      have hd : orient (original a) (original b) (original d)≥0 := by
        rw [original_vandermonde]
        have h1 : d-a≤0 := by linarith
        have h2 : d-b≤0 := by linarith
        have hprod := mul_nonneg_of_nonpos_of_nonpos h1 h2
        have : 0≤(b-a)*((d-a)*(d-b))/100 := by positivity
        nlinarith
      have hnot : ¬ProperCross (original a) (original b) (original c) (original d) := by
        intro h; have := mul_nonneg hc hd; exact (not_lt_of_ge this) h.1
      simp only [hnot,false_iff]
      rintro (h|h) <;> linarith [h.1,h.2.1,h.2.2]
  · have hbc : b≤c := le_of_not_gt hcb
    have hc : orient (original a) (original b) (original c)≥0 := by
      rw [original_vandermonde]
      have h1 : 0≤b-a := by linarith
      have h2 : 0≤c-a := by linarith
      have h3 : 0≤c-b := by linarith
      positivity
    have hd : orient (original a) (original b) (original d)≥0 := by
      rw [original_vandermonde]
      have h1 : 0≤b-a := by linarith
      have h2 : 0≤d-a := by linarith
      have h3 : 0≤d-b := by linarith
      positivity
    have hnot : ¬ProperCross (original a) (original b) (original c) (original d) := by
      intro h; have := mul_nonneg hc hd; exact (not_lt_of_ge this) h.1
    simp only [hnot,false_iff]
    rintro (h|h) <;> linarith [h.1,h.2.1,h.2.2]

def cross {O : ℕ} (ys : Fin O → ℚ) (a b c d : Fin O) : Prop :=
  ProperCross (original (ys a)) (original (ys b)) (original (ys c)) (original (ys d))

instance {O : ℕ} (ys : Fin O → ℚ) (a b c d : Fin O) : Decidable (cross ys a b c d) := by
  unfold cross ProperCross
  infer_instance

theorem cross_ordered {O : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (a b c d : Fin O) (hab : a<b) (hcd : c<d) :
    cross ys a b c d ↔ (a<c ∧ c<b ∧ b<d) ∨ (c<a ∧ a<d ∧ d<b) := by
  rw [cross,cap_ordered _ _ _ _ (hy hab) (hy hcd)]
  simp only [hy.lt_iff_lt]

theorem cross_reverse_second {O : ℕ} (ys : Fin O → ℚ) (a b c d : Fin O) :
    cross ys a b c d ↔ cross ys a b d c := by
  unfold cross
  rw [properCross_swap_edges (original (ys a)) (original (ys b)),
    properCross_reverse_first,properCross_swap_edges]

end Q4.Candidate.OriginalCapAlternation
#print axioms Q4.Candidate.OriginalCapAlternation.cap_ordered
#print axioms Q4.Candidate.OriginalCapAlternation.cross_ordered
#print axioms Q4.Candidate.OriginalCapAlternation.cross_reverse_second
