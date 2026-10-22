import Q4.Candidate.TwoPhaseStability

namespace Q4.Candidate.GridInitialConstants

set_option exponentiation.threshold 8192

/-- The finite-grid initial support threshold from the actual continuous
stability constant. All inequalities are exact real/rational arithmetic. -/
theorem initial_fraction_bound (a rho : ℝ) (ha : 0 ≤ a) (hrho : rho ≤ a)
    (hsmall : a ≤ 1/(2:ℝ)^4096) :
    2048*(5*a)^(1/72:ℝ)+rho ≤ 1/1048576 := by
  have hroot : (5*a)^(1/72:ℝ) ≤ 1/(2:ℝ)^32 := by
    apply le_of_pow_le_pow_left₀ (n := 72) (by decide)
      (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^32)
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ 5*a) (1/72:ℝ) 72]
    simp only [Nat.cast_ofNat]
    rw [show (1/72:ℝ)*72=1 by norm_num,Real.rpow_one]
    calc
      5*a ≤ 5*(1/(2:ℝ)^4096) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ ≤ _ := by norm_num
  have hr : rho ≤ 1/(2:ℝ)^21 := by
    have hnum : 1/(2:ℝ)^4096 ≤ 1/(2:ℝ)^21 := by norm_num
    linarith
  norm_num at hroot hr
  linarith

end Q4.Candidate.GridInitialConstants

#print axioms Q4.Candidate.GridInitialConstants.initial_fraction_bound
