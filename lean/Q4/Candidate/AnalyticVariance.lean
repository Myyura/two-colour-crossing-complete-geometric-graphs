import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Analytic ingredients of candidate §2, specifically its variance and affine-ramp
step (2.8). These are actual Lebesgue/Bochner integral statements. They do not
assert continuous stability; the operator identities, quantiles, smoothing and
two-threshold approximation remain separate obligations.
-/

open MeasureTheory Set

namespace Q4.Candidate.AnalyticVariance

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem integral_sq_sub_const (F : α → ℝ)
    (hF : Integrable F μ) (hF2 : Integrable (fun x => F x ^ 2) μ) (c : ℝ) :
    (∫ x, (F x - c)^2 ∂μ) =
      (∫ x, F x^2 ∂μ) - 2 * c * (∫ x, F x ∂μ) + c^2 := by
  have he : (fun x => (F x - c)^2) =
      (fun x => (F x^2 - 2*c*F x) + c^2) := by
    funext x
    ring
  have hmul : Integrable (fun x => 2*c*F x) μ := hF.const_mul (2*c)
  have hsub : Integrable (fun x => F x^2 - 2*c*F x) μ := hF2.sub hmul
  rw [he, integral_add hsub (integrable_const (c^2)),
    integral_sub hF2 hmul, integral_const_mul]
  simp

theorem variance_eq_second_moment (F : α → ℝ)
    (hF : Integrable F μ) (hF2 : Integrable (fun x => F x ^ 2) μ) :
    (∫ x, (F x - ∫ y, F y ∂μ)^2 ∂μ) =
      (∫ x, F x^2 ∂μ) - (∫ x, F x ∂μ)^2 := by
  rw [integral_sq_sub_const F hF hF2]
  ring

/-- The exact identity underlying (2.8), with no variance or product-integral
formula assumed. Square-integrability is expressed by its actual integrals. -/
theorem double_difference_eq_twice_variance (F : α → ℝ)
    (hF : Integrable F μ) (hF2 : Integrable (fun x => F x ^ 2) μ) :
    (∫ x, ∫ y, (F y - F x)^2 ∂μ ∂μ) =
      2 * (∫ x, (F x - ∫ y, F y ∂μ)^2 ∂μ) := by
  simp_rw [integral_sq_sub_const F hF hF2]
  have hmul : Integrable (fun x => 2*F x*(∫ y, F y ∂μ)) μ :=
    (hF.const_mul 2).mul_const _
  have hsub : Integrable (fun x => (∫ y, F y^2 ∂μ) - 2*F x*(∫ y, F y ∂μ)) μ :=
    (integrable_const _).sub hmul
  rw [integral_add hsub hF2,
    integral_sub (integrable_const _) hmul,
    integral_mul_const, integral_const_mul]
  simp
  ring

/-- Exact evaluation of the ramp integral, including the nonnegative remainder
around its best constant. -/
theorem affine_ramp_integral (l a : ℝ) :
    (∫ s in (0 : ℝ)..l, (2*s-a)^2) = l^3/3 + l*(a-l)^2 := by
  have he : (fun s : ℝ => (2*s-a)^2) =
      (fun s => (4*s^2 - (4*a)*s) + a^2) := by funext s; ring
  have h1 : IntervalIntegrable (fun s : ℝ => 4*s^2) volume 0 l :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 l
  have h2 : IntervalIntegrable (fun s : ℝ => (4*a)*s) volume 0 l :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 l
  have h3 : IntervalIntegrable (fun s : ℝ => 4*s^2 - (4*a)*s) volume 0 l := h1.sub h2
  rw [he, intervalIntegral.integral_add h3 (intervalIntegrable_const (c := a^2)),
    intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_id,
    intervalIntegral.integral_const]
  simp
  ring

theorem affine_ramp_lower (l a : ℝ) (hl : 0 ≤ l) :
    l^3/3 ≤ ∫ s in (0 : ℝ)..l, (2*s-a)^2 := by
  rw [affine_ramp_integral]
  exact le_add_of_nonneg_right (mul_nonneg hl (sq_nonneg _))

theorem affine_interval_lower (F : ℝ → ℝ) (b l a c : ℝ)
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hbl : b+l ≤ 1)
    (hF : IntervalIntegrable (fun s => (F s-c)^2) volume 0 1)
    (hramp : ∀ s ∈ Icc b (b+l), F s-c = 2*(s-b)-a) :
    l^3/3 ≤ ∫ s in (0 : ℝ)..1, (F s-c)^2 := by
  have he : (∫ s in b..b+l, (F s-c)^2) =
      ∫ s in b..b+l, (2*(s-b)-a)^2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith : b ≤ b+l)] at hs
    exact congrArg (fun x : ℝ => x^2) (hramp s hs)
  have hshift : (∫ s in b..b+l, (2*(s-b)-a)^2) =
      ∫ s in (0 : ℝ)..l, (2*s-a)^2 := by
    simpa using intervalIntegral.integral_comp_sub_right (fun s : ℝ => (2*s-a)^2) b
      (a := b) (b := b+l)
  calc
    l^3/3 ≤ ∫ s in (0 : ℝ)..l, (2*s-a)^2 := affine_ramp_lower l a hl
    _ = ∫ s in b..b+l, (F s-c)^2 := (he.trans hshift).symm
    _ ≤ ∫ s in (0 : ℝ)..1, (F s-c)^2 :=
      intervalIntegral.integral_mono_interval hb (by linarith) hbl
        (ae_of_all _ (fun s => sq_nonneg (F s-c))) hF

end Q4.Candidate.AnalyticVariance

#print axioms Q4.Candidate.AnalyticVariance.double_difference_eq_twice_variance
#print axioms Q4.Candidate.AnalyticVariance.affine_ramp_integral
#print axioms Q4.Candidate.AnalyticVariance.affine_ramp_lower
#print axioms Q4.Candidate.AnalyticVariance.affine_interval_lower
