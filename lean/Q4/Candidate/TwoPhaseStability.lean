import Q4.Candidate.StabilityConstants
import Q4.Candidate.DiagonalRounding
import Q4.Candidate.OperatorPerturbation
import Q4.Candidate.AntiperiodicReplacement

/-! The complete continuous two-phase stability theorem for measurable
Boolean colorings of the unit square, with the actual comparison energy
and the actual spin L1 distance. Every auxiliary coloring is constructed
by previously proved existence or explicit formulas. -/

open MeasureTheory Set

namespace Q4.Candidate.TwoPhaseStability
open Q4.Candidate.UnitIntervalMeasure Q4.Candidate.AlternationKernel
open Q4.Candidate.ComparisonEnergy Q4.Candidate.DiagonalHalves
open Q4.Candidate.AntiperiodicThreshold Q4.Candidate.StabilityConstants

theorem distance_le_two (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) :
    EnergyLipschitz.distance unit f g ≤ 2 := by
  calc
    _ ≤ ∫ p : Point, (2:ℝ) ∂unit.prod unit :=
      integral_mono (EnergyLipschitz.pointDistance_integrable unit f g hf hg)
        (integrable_const _) (fun p => (EnergyLipschitz.pointDistance_bounds f g p).2)
    _ = 2 := by simp

theorem small_parameter_stability (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (hsmall : 257*h ≤ 1/4096)
    (hE : energy unit f ≤ 1/12+h^6) :
    ∃ phase : Bool, EnergyLipschitz.distance unit f (canonical phase) ≤
      594*(257*h)^(1/12:ℝ) := by
  have hh1 : h ≤ 1 := by linarith
  have hα : 0 < 257*h := by positivity
  have hα1 : 257*h ≤ 1 := by linarith
  obtain ⟨b,hb,happrox,henergy⟩ := DiagonalRounding.exists_diagonal_rounding f hf h hh hh1 hE
  let f1 : Point → Bool := fun p => b (p.1+p.2)
  have hf1 : Measurable f1 := hb.comp (measurable_fst.add measurable_snd)
  obtain ⟨o0,o1,c,hc,d,hd,hhalves⟩ := ThresholdHalfSelection.two_threshold_halves_rpow
    b hb (257*h) hα (fourth_root_small _ hα.le hsmall) henergy
  let f2 := diagonal (threshold o0 c) (threshold o1 d)
  have hf2 : Measurable f2 := diagonal_measurable _ _ (threshold_measurable o0 c) (threshold_measurable o1 d)
  change EnergyLipschitz.distance unit f1 f2 ≤ 30*(257*h)^(1/4:ℝ) at hhalves
  have hop := OperatorPerturbation.near_optimal_perturbation unit f1 f2 hf1 hf2 (257*h) henergy
  have hat : 257*h ≤ (257*h)^(1/4:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hα hα1
      (show (1/4:ℝ) ≤ 1 by norm_num)
  have hop512 : differenceSq unit f2 ≤ 512*(257*h)^(1/4:ℝ) := by linarith
  have hm3 := agreement_cubic_of_operator_bound o0 o1 c d ((257*h)^(1/4:ℝ)) hc hd hop512
  have hm := agreement_bound _ (257*h) hα.le hm3
  have hmean := (deficit_bounds unit f hf (h^6) hE).1
  have hmean' : |mean unit f| ≤ 3*h^3 := by
    have hpos : 0 ≤ 3*h^3 := by positivity
    nlinarith [sq_abs (mean unit f),abs_nonneg (mean unit f),
      sq_nonneg (|mean unit f|+3*h^3)]
  have htri := EnergyLipschitz.distance_triangle unit f f1 f2 hf hf1 hf2
  obtain ⟨phase,hphase⟩ := AntiperiodicReplacement.close_to_phase f hf o0 o1 c d hc
  refine ⟨phase,total_bound h hh hα1 _ ?_⟩
  change EnergyLipschitz.distance unit f1 _ ≤ _ at hhalves
  change EnergyLipschitz.distance unit f f1 ≤ _ at happrox
  change EnergyLipschitz.distance unit f (canonical phase) ≤
    3*EnergyLipschitz.distance unit f f2+6*agreementMass (threshold o0 c) (threshold o1 d)+
      2*|mean unit f| at hphase
  linarith

/-- A positive smoothing scale needs no upper restriction: for large scales
the actual diameter-two estimate supplies the same bound. -/
theorem positive_parameter_stability (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (hE : energy unit f ≤ 1/12+h^6) :
    ∃ phase : Bool, EnergyLipschitz.distance unit f (canonical phase) ≤
      4096*h^(1/12:ℝ) := by
  by_cases hs : 257*h ≤ 1/4096
  · obtain ⟨phase,hphase⟩ := small_parameter_stability f hf h hh hs hE
    have hr := scaled_root h hh.le
    have hn := Real.rpow_nonneg hh.le (1/12:ℝ)
    exact ⟨phase,by linarith⟩
  · exact ⟨true,(distance_le_two f (canonical true) hf
      (AntiperiodicReplacement.canonical_measurable true)).trans
        (large_parameter h hh.le (le_of_not_ge hs))⟩

/-- Zero excess is handled without assuming existence of a limiting phase:
the minimum of the two fixed phase distances must itself be zero. -/
theorem zero_excess_stability (f : Point → Bool) (hf : Measurable f)
    (hE : energy unit f ≤ 1/12) :
    ∃ phase : Bool, EnergyLipschitz.distance unit f (canonical phase) = 0 := by
  let m := min (EnergyLipschitz.distance unit f (canonical true))
    (EnergyLipschitz.distance unit f (canonical false))
  have hm : 0 ≤ m := le_min (EnergyLipschitz.distance_nonneg _ _ _)
    (EnergyLipschitz.distance_nonneg _ _ _)
  have hm0 : m = 0 := by
    by_contra hmne
    have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hmne)
    let h := (m/8192)^12
    have hh : 0 < h := by dsimp [h]; positivity
    obtain ⟨phase,hphase⟩ := positive_parameter_stability f hf h hh (by linarith [pow_nonneg hh.le 6])
    have he : h^(1/12:ℝ) = m/8192 := by
      dsimp [h]
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ m/8192)]
      norm_num
    have hmin : m ≤ EnergyLipschitz.distance unit f (canonical phase) := by
      cases phase
      · exact min_le_right _ _
      · exact min_le_left _ _
    rw [he] at hphase
    linarith
  by_cases ht : EnergyLipschitz.distance unit f (canonical true) ≤
      EnergyLipschitz.distance unit f (canonical false)
  · exact ⟨true,by simpa only [m,min_eq_left ht] using hm0⟩
  · exact ⟨false,by simpa only [m,min_eq_right (le_of_not_ge ht)] using hm0⟩

/-- Candidate Theorem 2.1, including zero excess, for the Borel Boolean
representation used by the finite geometric reduction. -/
theorem two_phase_stability (f : Point → Bool) (hf : Measurable f)
    (ε : ℝ) (hε : 0 ≤ ε) (hE : energy unit f ≤ 1/12+ε) :
    ∃ phase : Bool, EnergyLipschitz.distance unit f (canonical phase) ≤
      4096*ε^(1/72:ℝ) := by
  rcases eq_or_lt_of_le hε with hz | hp
  · subst ε
    obtain ⟨phase,hphase⟩ := zero_excess_stability f hf (by simpa using hE)
    exact ⟨phase,by rw [hphase]; positivity⟩
  · have hh : 0 < ε^(1/6:ℝ) := Real.rpow_pos_of_pos hp _
    have hpow : (ε^(1/6:ℝ))^6 = ε := by
      rw [←Real.rpow_mul_natCast hε (1/6:ℝ) 6]
      norm_num
    obtain ⟨phase,hphase⟩ := positive_parameter_stability f hf (ε^(1/6:ℝ)) hh
      (by simpa only [hpow] using hE)
    refine ⟨phase,?_⟩
    rw [←Real.rpow_mul hε] at hphase
    norm_num at hphase
    exact hphase

end Q4.Candidate.TwoPhaseStability

#print axioms Q4.Candidate.TwoPhaseStability.small_parameter_stability
#print axioms Q4.Candidate.TwoPhaseStability.positive_parameter_stability
#print axioms Q4.Candidate.TwoPhaseStability.zero_excess_stability
#print axioms Q4.Candidate.TwoPhaseStability.two_phase_stability
