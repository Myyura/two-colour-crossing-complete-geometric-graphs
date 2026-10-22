import Q4.Candidate.ThresholdHalfSelection

/-! Exact real-power arithmetic for the continuous two-phase stability
theorem. These lemmas state only scalar estimates, never geometric or
variational assumptions. -/

namespace Q4.Candidate.StabilityConstants

theorem fourth_root_small (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1/4096) :
    α^(1/4:ℝ) ≤ 1/8 := by
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (by norm_num : (0:ℝ) ≤ 1/8)
  rw [←Real.rpow_mul_natCast hα (1/4:ℝ) 4]
  norm_num
  exact hα1

theorem root_powers (α : ℝ) (hα : 0 ≤ α) :
    (α^(1/12:ℝ))^3 = α^(1/4:ℝ) ∧ (α^(1/12:ℝ))^12 = α := by
  constructor
  · rw [←Real.rpow_mul_natCast hα (1/12:ℝ) 3]
    norm_num
  · rw [←Real.rpow_mul_natCast hα (1/12:ℝ) 12]
    norm_num

theorem agreement_bound (m α : ℝ) (hα : 0 ≤ α)
    (hm : m^3 ≤ 6144*α^(1/4:ℝ)) : m ≤ 19*α^(1/12:ℝ) := by
  have hroot := (root_powers α hα).1
  have hnonneg : 0 ≤ α^(1/12:ℝ) := Real.rpow_nonneg hα _
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity : 0 ≤ 19*α^(1/12:ℝ))
  rw [mul_pow,hroot]
  nlinarith [Real.rpow_nonneg hα (1/4:ℝ)]

theorem total_bound (h : ℝ) (hh : 0 < h) (hsmall : 257*h ≤ 1)
    (D : ℝ)
    (hD : D ≤ 384*h+90*(257*h)^(1/4:ℝ)+114*(257*h)^(1/12:ℝ)+6*h^3) :
    D ≤ 594*(257*h)^(1/12:ℝ) := by
  have hα : 0 < 257*h := by positivity
  have hαroot : 257*h ≤ (257*h)^(1/12:ℝ) := by
    have hx := Real.rpow_le_rpow_of_exponent_ge hα hsmall (show (1/12:ℝ) ≤ 1 by norm_num)
    simpa only [Real.rpow_one] using hx
  have htroot : (257*h)^(1/4:ℝ) ≤ (257*h)^(1/12:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hα hsmall (by norm_num)
  have hh1 : h ≤ 1 := by linarith
  have hh3 : h^3 ≤ h := by
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1),
      mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh1)]
  linarith

theorem scaled_root (h : ℝ) (hh : 0 ≤ h) :
    (257*h)^(1/12:ℝ) ≤ 2*h^(1/12:ℝ) := by
  have hleft := (root_powers (257*h) (by positivity)).2
  have hright := (root_powers h hh).2
  apply le_of_pow_le_pow_left₀ (n := 12) (by decide) (by positivity : 0 ≤ 2*h^(1/12:ℝ))
  rw [hleft,mul_pow,hright]
  nlinarith

theorem large_parameter (h : ℝ) (hh : 0 ≤ h) (hlarge : 1/4096 ≤ 257*h) :
    2 ≤ 4096*h^(1/12:ℝ) := by
  have hroot : (1/4:ℝ) ≤ h^(1/12:ℝ) := by
    apply le_of_pow_le_pow_left₀ (n := 12) (by decide) (Real.rpow_nonneg hh _)
    rw [(root_powers h hh).2]
    norm_num
    linarith
  linarith

end Q4.Candidate.StabilityConstants

#print axioms Q4.Candidate.StabilityConstants.fourth_root_small
#print axioms Q4.Candidate.StabilityConstants.agreement_bound
#print axioms Q4.Candidate.StabilityConstants.total_bound
#print axioms Q4.Candidate.StabilityConstants.scaled_root
#print axioms Q4.Candidate.StabilityConstants.large_parameter
