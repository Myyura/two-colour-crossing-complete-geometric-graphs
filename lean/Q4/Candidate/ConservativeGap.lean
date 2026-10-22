import Q4.Candidate.ReductionGap

/-! A deliberately looser local crossing bound still yields a one-query
threshold. This is a separate version; it does not claim the manuscript's
exact local count or its narrower 2^-19 aggregate window. -/
namespace Q4.Candidate.ConservativeGap
open Q4.Candidate.ReductionGap

theorem local_bound (n q H : ℝ) (hn : 0≤n) (hH : 0≤H)
    (hq : q=(2:ℝ)^20*(n+1)) :
    2*(n*q)*H^16 ≤ (q^2*H^16)/(2:ℝ)^19 := by
  have hh := local_error_bound n q H hn hH hq
  norm_num at hh ⊢
  linarith

theorem actual_error_window (n : ℝ) (hn : 0≤n) (eAlg eUnary eLocal : ℝ)
    (q d H : ℝ) (hq : q=(2:ℝ)^20*(n+1)) (hd : d=n*q+1)
    (hH : H=(2:ℝ)^20000*d^40)
    (ha : eAlg≤(2:ℝ)^310*d^14*H^15)
    (hu : eUnary≤10*(n*q)*H^13) (hl : eLocal≤2*(n*q)*H^16) :
    (2:ℝ)^18*(eAlg+eUnary+eLocal)<q^2*H^16 := by
  have hq1 : 1≤q := by rw [hq]; nlinarith
  have hq0 : 0≤q := by linarith
  have hnq : n≤q := by rw [hq]; nlinarith
  have hd1 : 1≤d := by rw [hd]; exact le_add_of_nonneg_left (mul_nonneg hn hq0)
  have hlarge : (2:ℝ)^44≤H := by rw [hH]; exact actual_scale_large d hd1
  have hH0 : 0<H := lt_of_lt_of_le (by positivity) hlarge
  have hs : 0<q^2*H^16 := mul_pos (pow_pos (by linarith) _) (pow_pos hH0 _)
  have hA := ha.trans (algebraic_error_bound d q H hd1 hq1
    (by rw [hH]; exact actual_scale_lower d hd1))
  have hU := hu.trans (unary_error_bound n q H hn hnq hq0 hlarge)
  have hL := hl.trans (local_bound n q H hn (le_of_lt hH0) hq)
  norm_num at hA hU hL ⊢
  linarith

/-- Even this conservative accounting remains strictly within the required
quarter-signal separation of the integer source threshold. -/
theorem quarter_gap (Δ e : ℝ) (hΔ : 0<Δ) (h : (2:ℝ)^18*e<Δ) : 4*e<Δ := by
  by_cases he : 0≤e
  · norm_num at h
    linarith
  · linarith

end Q4.Candidate.ConservativeGap
#print axioms Q4.Candidate.ConservativeGap.local_bound
#print axioms Q4.Candidate.ConservativeGap.actual_error_window
#print axioms Q4.Candidate.ConservativeGap.quarter_gap
