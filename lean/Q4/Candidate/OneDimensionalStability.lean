import Q4.Candidate.AlternationKernel
import Q4.Candidate.ThresholdApproximation

/-!
Candidate Lemma 2.2 on the actual restricted Lebesgue measure. The transform,
norm square, ordered alternating event, threshold existence and L1 distance are
all the objects proved in the imported modules; the norm identity is not an
assumption. This is one dimensional stability, not Theorem 2.1.
-/

open MeasureTheory Set

namespace Q4.Candidate.OneDimensionalStability

open Q4.Candidate.UnitIntervalMeasure
open Q4.Candidate.AlternatingTriples
open Q4.Candidate.AlternationKernel
open Q4.Candidate.ThresholdApproximation

noncomputable def deficit (h : ℝ → Bool) : ℝ := 1/3 - normSq unit h

theorem deficit_eq_alternations (h : ℝ → Bool) (hh : Measurable h) :
    deficit h = 8 * tripleMass unit h := by
  unfold deficit
  rw [kernel_identity unit h hh]
  ring

theorem deficit_nonneg (h : ℝ → Bool) (hh : Measurable h) : 0 ≤ deficit h := by
  rw [deficit_eq_alternations h hh]
  exact mul_nonneg (by norm_num) measureReal_nonneg

/-- Lemma 2.2, including an actual attained threshold in one of the two
orientations, with the manuscript's exact coefficient 4 and exponent 1/3. -/
theorem one_dimensional_stability (h : ℝ → Bool) (hh : Measurable h) :
    0 ≤ deficit h ∧ ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      (∫ x, |ThresholdApproximation.sign {x | h x = true} x -
        ThresholdApproximation.sign (if o then Iic t else Ioi t) x| ∂unit)
        ≤ 4 * (deficit h)^(1/3 : ℝ) := by
  have hD := deficit_nonneg h hh
  have hP : MeasurableSet {x | h x = true} := hh (measurableSet_singleton true)
  obtain ⟨o,t,ht,hb⟩ := attained_threshold_L1_cubic zero_left_mass zero_right_mass h hP
  refine ⟨hD,o,t,ht,?_⟩
  have hpow : (4 * (deficit h)^(1/3 : ℝ))^3 = 64 * deficit h := by
    rw [mul_pow, ← Real.rpow_mul_natCast hD (1/3 : ℝ) 3]
    norm_num
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hD _))
  rw [hpow, deficit_eq_alternations h hh]
  nlinarith

end Q4.Candidate.OneDimensionalStability

#print axioms Q4.Candidate.OneDimensionalStability.deficit_eq_alternations
#print axioms Q4.Candidate.OneDimensionalStability.deficit_nonneg
#print axioms Q4.Candidate.OneDimensionalStability.one_dimensional_stability
