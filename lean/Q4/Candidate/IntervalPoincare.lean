import Q4.Candidate.AnalyticVariance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! The L1 interval Poincaré estimate used on the diagonal segments in §2.
The derivative is the actual derivative of an absolutely continuous function;
the fundamental theorem of calculus is proved in the imported mathlib module.
-/

open MeasureTheory Set

namespace Q4.Candidate.IntervalPoincare

theorem oscillation_bound {F : ℝ → ℝ} {a b x y : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOnInterval F a b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |F x-F y| ≤ ∫ t in a..b, |deriv F t| := by
  have hsub (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      |F v-F u| ≤ ∫ t in a..b, |deriv F t| := by
    have hsmall : AbsolutelyContinuousOnInterval F u v := hF.mono (by
      rw [uIcc_of_le hab, uIcc_of_le huv]
      exact Icc_subset_Icc hu.1 hv.2)
    rw [← hsmall.integral_deriv_eq_sub]
    exact (intervalIntegral.abs_integral_le_integral_abs huv).trans
      (intervalIntegral.integral_mono_interval hu.1 huv hv.2
        (ae_of_all _ (fun t => abs_nonneg (deriv F t))) hF.intervalIntegrable_deriv.abs)
  rcases le_total x y with hxy | hyx
  · simpa only [abs_sub_comm] using hsub x y hx hy hxy
  · exact hsub y x hy hx hyx

noncomputable def intervalMean (F : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b-a)⁻¹ * ∫ x in Icc a b, F x

theorem distance_to_mean_bound {F : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hF : AbsolutelyContinuousOnInterval F a b) (hx : x ∈ Icc a b) :
    |F x-intervalMean F a b| ≤ ∫ t in a..b, |deriv F t| := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hm : μ.real univ = b-a := by simp [μ, Real.volume_real_Icc, hab.le]
  have hfi : Integrable F μ := by
    have hcont : ContinuousOn F (Icc a b) := by simpa only [uIcc_of_le hab.le] using hF.continuousOn
    exact hcont.integrableOn_Icc
  have he : F x-intervalMean F a b = (b-a)⁻¹ * ∫ y, F x-F y ∂μ := by
    rw [integral_sub (integrable_const _) hfi, integral_const]
    simp only [smul_eq_mul, hm, intervalMean, μ]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr (sub_pos.mpr hab))]
  calc
    _ ≤ (b-a)⁻¹ * ∫ y, |F x-F y| ∂μ :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => F x-F y))
        (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
    _ ≤ (b-a)⁻¹ * ∫ _y, (∫ t in a..b, |deriv F t|) ∂μ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
      apply integral_mono_ae ((integrable_const _).sub hfi).abs (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact oscillation_bound hab.le hF hx hy
    _ = _ := by
      rw [integral_const]
      simp only [smul_eq_mul, hm]
      field_simp [ne_of_gt (sub_pos.mpr hab)]

theorem interval_poincare {F : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : AbsolutelyContinuousOnInterval F a b) :
    (∫ x in Icc a b, |F x-intervalMean F a b|) ≤
      (b-a) * (∫ t in a..b, |deriv F t|) := by
  have hcont : ContinuousOn F (Icc a b) := by simpa only [uIcc_of_le hab.le] using hF.continuousOn
  have hfi : IntegrableOn F (Icc a b) := hcont.integrableOn_Icc
  calc
    _ ≤ ∫ _x in Icc a b, (∫ t in a..b, |deriv F t|) := by
      apply integral_mono_ae (hfi.sub (integrable_const _)).abs (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact distance_to_mean_bound hab hF hx
    _ = _ := by simp [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hab.le)]

end Q4.Candidate.IntervalPoincare

#print axioms Q4.Candidate.IntervalPoincare.oscillation_bound
#print axioms Q4.Candidate.IntervalPoincare.distance_to_mean_bound
#print axioms Q4.Candidate.IntervalPoincare.interval_poincare
