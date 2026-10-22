import Q4.Candidate.CoreEncoding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The explicit integer greedy construction in candidate Lemma 5.3.
Only internal gaps receive copies. A zero needed step really uses zero
copies, so the total count bound has no additive term proportional to W. -/
namespace Q4.Candidate.RankCorrection
open scoped BigOperators

def copiesNeeded (R T w : ℕ) : ℕ := if R<T then (T-R-1)/w+1 else 0
def stepValue (R T w : ℕ) : ℕ := R+w*copiesNeeded R T w

theorem step_target (R T w : ℕ) (hw : 0<w) : T ≤ stepValue R T w := by
  by_cases h : R<T
  · have he := Nat.mod_add_div (T-R-1) w
    have hm := Nat.mod_lt (T-R-1) hw
    have hsub : T-R-1+R+1=T := by omega
    simp only [stepValue,copiesNeeded,ite_eq_left h]
    nlinarith
  · simp only [stepValue,copiesNeeded,ite_eq_right h,mul_zero,add_zero]
    omega

theorem step_overshoot (R T w B : ℕ) (hwB : w≤B) (hR : R<T+B) :
    stepValue R T w < T+B := by
  by_cases h : R<T
  · have he := Nat.mod_add_div (T-R-1) w
    have hsub : T-R-1+R+1=T := by omega
    simp only [stepValue,copiesNeeded,ite_eq_left h]
    nlinarith [Nat.zero_le ((T-R-1)%w)]
  · simpa only [stepValue,copiesNeeded,ite_eq_right h,mul_zero,add_zero] using hR

def cumulative (slope : ℕ) (weight : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => stepValue (cumulative slope weight n) (slope*(n+1)) (weight n)

def multiplicity (slope : ℕ) (weight : ℕ → ℕ) (gap : ℕ) : ℕ :=
  copiesNeeded (cumulative slope weight gap) (slope*(gap+1)) (weight gap)

def copyCount (slope : ℕ) (weight : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => copyCount slope weight n+multiplicity slope weight n

theorem cumulative_bounds (slope B n : ℕ) (weight : ℕ → ℕ) (hB : 0<B)
    (hw : ∀ i<n, 0<weight i ∧ weight i≤B) :
    slope*n ≤ cumulative slope weight n ∧ cumulative slope weight n < slope*n+B := by
  induction n with
  | zero => simp [cumulative,hB]
  | succ n ih =>
    have hn := ih (fun i hi => hw i (by omega))
    have hwi := hw n (by omega)
    refine ⟨step_target _ _ _ hwi.1,step_overshoot _ _ _ _ hwi.2 ?_⟩
    have he : slope*(n+1) = slope*n+slope := by ring
    rw [he]
    omega

theorem cumulative_eq_sum (slope n : ℕ) (weight : ℕ → ℕ) :
    cumulative slope weight n = ∑ i ∈ Finset.range n, weight i*multiplicity slope weight i := by
  induction n with
  | zero => simp [cumulative]
  | succ n ih =>
    simp only [Finset.sum_range_succ,cumulative,stepValue,multiplicity,ih]

theorem count_weight_bound (slope B n : ℕ) (weight : ℕ → ℕ)
    (hw : ∀ i<n, B≤4*weight i) :
    B*copyCount slope weight n ≤ 4*cumulative slope weight n := by
  induction n with
  | zero => simp [copyCount,cumulative]
  | succ n ih =>
    have hn := ih (fun i hi => hw i (by omega))
    have hnew := Nat.mul_le_mul_right (multiplicity slope weight n) (hw n (by omega))
    dsimp only [copyCount,cumulative,stepValue]
    change B*(copyCount slope weight n+multiplicity slope weight n) ≤
      4*(cumulative slope weight n+weight n*multiplicity slope weight n)
    nlinarith

/-- The actual finite construction meets every prefix target, uses only gaps
0,...,n-1, and its total copy count is paid by total weight, not by n. -/
theorem greedy_correction (slope B n : ℕ) (weight : ℕ → ℕ) (hB : 0<B)
    (hw : ∀ i<n, 0<weight i ∧ weight i≤B ∧ B≤4*weight i) :
    (∀ r≤n, slope*r ≤ cumulative slope weight r ∧
      cumulative slope weight r < slope*r+B) ∧
    B*copyCount slope weight n < 4*(slope*n+B) := by
  have hall (r : ℕ) (hr : r≤n) := cumulative_bounds slope B r weight hB
    (fun i hi => ⟨(hw i (by omega)).1,(hw i (by omega)).2.1⟩)
  refine ⟨hall,?_⟩
  have hc := count_weight_bound slope B n weight (fun i hi => (hw i hi).2.2)
  have hf := (hall n (by omega)).2
  omega

def error (slope : ℕ) (weight : ℕ → ℕ) (r : ℕ) : ℕ :=
  cumulative slope weight r-slope*r

theorem error_bounds (slope B n r : ℕ) (weight : ℕ → ℕ) (hB : 0<B) (hr : r≤n)
    (hw : ∀ i<n, 0<weight i ∧ weight i≤B) :
    error slope weight r < B ∧ cumulative slope weight r=slope*r+error slope weight r := by
  have hb := cumulative_bounds slope B r weight hB (fun i hi => hw i (by omega))
  unfold error
  omega

/-- The left cumulative and right negative-prefix responses cancel both
negative slopes with one common offset, independent of the selected ranks. -/
theorem affine_correction (beta : ℤ) (slopeL slopeR B n r t : ℕ)
    (weightL weightR : ℕ → ℕ) (hB : 0<B) (hr : r≤n) (ht : t≤n)
    (hL : ∀ i<n, 0<weightL i ∧ weightL i≤B)
    (hR : ∀ i<n, 0<weightR i ∧ weightR i≤B) :
    let eL := error slopeL weightL r
    let eR := error slopeR weightR t
    eL<B ∧ eR<B ∧
      beta-(slopeL:ℤ)*r-(slopeR:ℤ)*t+cumulative slopeL weightL r-
        cumulative slopeR weightR n+cumulative slopeR weightR t =
      beta-cumulative slopeR weightR n+eL+eR := by
  have hbL := error_bounds slopeL B n r weightL hB hr hL
  have hbR := error_bounds slopeR B n t weightR hB ht hR
  refine ⟨hbL.1,hbR.1,?_⟩
  rw [hbL.2,hbR.2]
  push_cast
  ring

end Q4.Candidate.RankCorrection

#print axioms Q4.Candidate.RankCorrection.step_target
#print axioms Q4.Candidate.RankCorrection.step_overshoot
#print axioms Q4.Candidate.RankCorrection.cumulative_bounds
#print axioms Q4.Candidate.RankCorrection.cumulative_eq_sum
#print axioms Q4.Candidate.RankCorrection.count_weight_bound
#print axioms Q4.Candidate.RankCorrection.greedy_correction
#print axioms Q4.Candidate.RankCorrection.affine_correction
