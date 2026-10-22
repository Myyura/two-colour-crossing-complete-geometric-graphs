import Q4.Candidate.AlternatingTriples
import Q4.Candidate.UnitIntervalMeasure
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Attainment and actual threshold-error interpretation for Lemma 2.2. This module
proves the cubic disagreement estimate with an attained threshold, using actual
atomless measures supported on [0,1]. The operator norm identity is separate.
-/

open MeasureTheory Set
open scoped symmDiff

namespace Q4.Candidate.ThresholdApproximation

open Q4.Candidate.AlternatingTriples

variable {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]

noncomputable def thresholdError (μ : Measure ℝ) (P : Set ℝ) (o : Bool) (t : ℝ) : ℝ :=
  if o then μ.real (Pᶜ ∩ Iic t) + μ.real (P ∩ Ioi t)
  else μ.real (P ∩ Iic t) + μ.real (Pᶜ ∩ Ioi t)

omit [IsFiniteMeasure μ] [NullSingletonClass μ] in
theorem thresholdError_nonneg (P : Set ℝ) (o : Bool) (t : ℝ) :
    0 ≤ thresholdError μ P o t := by
  cases o <;> simp only [thresholdError, Bool.false_eq_true, ite_false, ite_true] <;>
    exact add_nonneg measureReal_nonneg measureReal_nonneg

omit [NullSingletonClass μ] in
theorem restrict_zero_left (hzero : μ.real (Iic (0 : ℝ)) = 0) (P : Set ℝ) :
    (μ.restrict P).real (Iic (0 : ℝ)) = 0 := by
  rw [measureReal_restrict_apply measurableSet_Iic]
  exact le_antisymm ((measureReal_mono inter_subset_left).trans_eq hzero) measureReal_nonneg

theorem before_mass_continuous (hzero : μ.real (Iic (0 : ℝ)) = 0)
    (P : Set ℝ) : ContinuousOn (fun t => μ.real (P ∩ Iic t)) (Icc (0 : ℝ) 1) := by
  let ν := μ.restrict P
  have hz : ν.real (Iic (0 : ℝ)) = 0 := restrict_zero_left hzero P
  have hc : ContinuousOn (fun t => ∫ x in (0 : ℝ)..t, (1 : ℝ) ∂ν) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      intervalIntegral.continuousOn_primitive_interval'
        (μ := ν) (f := fun _ => (1 : ℝ)) intervalIntegrable_const
        (a := (0 : ℝ)) (b₁ := (0 : ℝ)) (b₂ := (1 : ℝ)) left_mem_uIcc
  apply hc.congr
  intro t ht
  have he := Iic_mass_eq_integral_one (μ := ν) hz t ht.1
  simpa only [ν, measureReal_restrict_apply measurableSet_Iic, inter_comm] using he

theorem after_mass_continuous (hzero : μ.real (Iic (0 : ℝ)) = 0)
    (P : Set ℝ) (hP : MeasurableSet P) :
    ContinuousOn (fun t => μ.real (P ∩ Ioi t)) (Icc (0 : ℝ) 1) := by
  have hc := (continuousOn_const (c := μ.real P)).sub (before_mass_continuous hzero P)
  apply hc.congr
  intro t _
  have hp := before_after_mass (μ := μ) P hP t
  change μ.real (P ∩ Ioi t) = μ.real P - μ.real (P ∩ Iic t)
  linarith

theorem thresholdError_continuous (hzero : μ.real (Iic (0 : ℝ)) = 0)
    (P : Set ℝ) (hP : MeasurableSet P) (o : Bool) :
    ContinuousOn (thresholdError μ P o) (Icc (0 : ℝ) 1) := by
  cases o
  · exact (before_mass_continuous hzero P).add (after_mass_continuous hzero Pᶜ hP.compl)
  · exact (before_mass_continuous hzero Pᶜ).add (after_mass_continuous hzero P hP)

theorem minimum_threshold_exists (hzero : μ.real (Iic (0 : ℝ)) = 0)
    (P : Set ℝ) (hP : MeasurableSet P) :
    ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      ∀ o' : Bool, ∀ u ∈ Icc (0 : ℝ) 1, thresholdError μ P o t ≤ thresholdError μ P o' u := by
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨a, ha, hma⟩ := isCompact_Icc.exists_isMinOn hne
    (thresholdError_continuous hzero P hP true)
  obtain ⟨b, hb, hmb⟩ := isCompact_Icc.exists_isMinOn hne
    (thresholdError_continuous hzero P hP false)
  by_cases hab : thresholdError μ P true a ≤ thresholdError μ P false b
  · refine ⟨true, a, ha, ?_⟩
    intro o' u hu
    cases o'
    · exact hab.trans (hmb hu)
    · exact hma hu
  · refine ⟨false, b, hb, ?_⟩
    intro o' u hu
    cases o'
    · exact hmb hu
    · exact (le_of_lt (lt_of_not_ge hab)).trans (hma hu)

omit [NullSingletonClass μ] in
theorem thresholdError_zero (hzero : μ.real (Iic (0 : ℝ)) = 0)
    (P : Set ℝ) (hP : MeasurableSet P) : thresholdError μ P true 0 = μ.real P := by
  have hpos : μ.real (P ∩ Iic (0 : ℝ)) = 0 := by
    simpa only [measureReal_restrict_apply measurableSet_Iic, inter_comm] using
      restrict_zero_left hzero P
  have hneg : μ.real (Pᶜ ∩ Iic (0 : ℝ)) = 0 := by
    simpa only [measureReal_restrict_apply measurableSet_Iic, inter_comm] using
      restrict_zero_left hzero Pᶜ
  have hp := before_after_mass (μ := μ) P hP 0
  simp only [thresholdError, ite_true, hneg, zero_add]
  linarith

/-- There really is a threshold attaining the cubic approximation estimate.
Neither its existence nor its quantiles are assumptions. The remaining link to
the deficit D(h) is the independent norm/kernel identity (2.3). -/
theorem attained_threshold_cubic (hzero : μ.real (Iic (0 : ℝ)) = 0)
    (hone : μ.real (Ioi (1 : ℝ)) = 0)
    (h : ℝ → Bool) (hP : MeasurableSet {x | h x = true}) :
    ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      (thresholdError μ {x | h x = true} o t)^3 ≤ 64 * tripleMass μ h := by
  obtain ⟨o,t,ht,hmin⟩ := minimum_threshold_exists hzero {x | h x = true} hP
  refine ⟨o,t,ht,threshold_distance_cubic hzero hone h hP
    (thresholdError μ {x | h x = true} o t) (thresholdError_nonneg _ _ _) ?_ ?_ ?_⟩
  · have hc := hmin true 0 (by norm_num)
    rwa [thresholdError_zero hzero _ hP] at hc
  · intro u hu
    exact hmin true u hu
  · intro u hu
    exact hmin false u hu

noncomputable def sign (P : Set ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ P then 1 else -1

omit [IsFiniteMeasure μ] [NullSingletonClass μ] in
theorem sign_l1_distance (P Q : Set ℝ) (hP : MeasurableSet P) (hQ : MeasurableSet Q) :
    (∫ x, |sign P x - sign Q x| ∂μ) = 2 * μ.real (P ∆ Q) := by
  classical
  have he : (fun x => |sign P x - sign Q x|) =
      (P ∆ Q).indicator (fun _ => (2 : ℝ)) := by
    funext x
    by_cases hp : x ∈ P <;> by_cases hq : x ∈ Q <;>
      norm_num [sign, Set.mem_symmDiff, hp, hq]
  rw [he, integral_indicator (hP.symmDiff hQ), integral_const]
  simp [mul_comm]

omit [NullSingletonClass μ] in
theorem thresholdError_symmDiff (P : Set ℝ) (hP : MeasurableSet P) (o : Bool) (t : ℝ) :
    thresholdError μ P o t = μ.real (P ∆ (if o then Iic t else Ioi t)) := by
  have hf : P ∆ Iic t = (Pᶜ ∩ Iic t) ∪ (P ∩ Ioi t) := by
    ext x
    simp only [Set.mem_symmDiff, mem_Iic, mem_union]
    constructor
    · intro hx
      rcases hx with ⟨hp,hn⟩ | ⟨hp,hn⟩
      · exact Or.inr ⟨hp,lt_of_not_ge hn⟩
      · exact Or.inl ⟨hn,hp⟩
    · intro hx
      rcases hx with hx | hx
      · exact Or.inr ⟨hx.2,hx.1⟩
      · exact Or.inl ⟨hx.1,not_le_of_gt hx.2⟩
  have hb : P ∆ Ioi t = (P ∩ Iic t) ∪ (Pᶜ ∩ Ioi t) := by
    ext x
    simp only [Set.mem_symmDiff, mem_union, mem_Ioi]
    constructor
    · intro hx
      rcases hx with ⟨hp,hn⟩ | ⟨hp,hn⟩
      · exact Or.inl ⟨hp,le_of_not_gt hn⟩
      · exact Or.inr ⟨hn,hp⟩
    · intro hx
      rcases hx with hx | hx
      · exact Or.inl ⟨hx.1,not_lt_of_ge hx.2⟩
      · exact Or.inr ⟨hx.2,hx.1⟩
  cases o
  · simp only [thresholdError, Bool.false_eq_true, ite_false, hb]
    rw [measureReal_union (Set.disjoint_left.mpr (by intro x hx hy; exact hy.1 hx.1))
      (hP.compl.inter measurableSet_Ioi)]
  · simp only [thresholdError, ite_true, hf]
    rw [measureReal_union (Set.disjoint_left.mpr (by intro x hx hy; exact hx.1 hy.1))
      (hP.inter measurableSet_Ioi)]

/-- The attained estimate is expressed in the actual L1 distance of the two
sign functions, with the factor two for disagreement explicitly verified. -/
theorem attained_threshold_L1_cubic (hzero : μ.real (Iic (0 : ℝ)) = 0)
    (hone : μ.real (Ioi (1 : ℝ)) = 0)
    (h : ℝ → Bool) (hP : MeasurableSet {x | h x = true}) :
    ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      (∫ x, |sign {x | h x = true} x - sign (if o then Iic t else Ioi t) x| ∂μ)^3
        ≤ 512 * tripleMass μ h := by
  obtain ⟨o,t,ht,hbound⟩ := attained_threshold_cubic hzero hone h hP
  refine ⟨o,t,ht,?_⟩
  have hQ : MeasurableSet (if o then Iic t else Ioi t) := by
    cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact measurableSet_Ioi
    · exact measurableSet_Iic
  rw [sign_l1_distance _ _ hP hQ, ← thresholdError_symmDiff _ hP o t]
  nlinarith

theorem attained_threshold_L1 (hzero : μ.real (Iic (0 : ℝ)) = 0)
    (hone : μ.real (Ioi (1 : ℝ)) = 0)
    (h : ℝ → Bool) (hP : MeasurableSet {x | h x = true}) :
    ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      (∫ x, |sign {x | h x = true} x - sign (if o then Iic t else Ioi t) x| ∂μ)
        ≤ 8 * (tripleMass μ h) ^ (1/3 : ℝ) := by
  obtain ⟨o,t,ht,hb⟩ := attained_threshold_L1_cubic hzero hone h hP
  refine ⟨o,t,ht,?_⟩
  have hI : 0 ≤ tripleMass μ h := measureReal_nonneg
  have hpow : (8 * (tripleMass μ h) ^ (1/3 : ℝ))^3 = 512 * tripleMass μ h := by
    rw [mul_pow, ← Real.rpow_mul_natCast hI (1/3 : ℝ) 3]
    norm_num
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hI _))
  rwa [hpow]

theorem unit_attained_threshold_L1
    (h : ℝ → Bool) (hP : MeasurableSet {x | h x = true}) :
    ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      (∫ x, |sign {x | h x = true} x - sign (if o then Iic t else Ioi t) x|
        ∂Q4.Candidate.UnitIntervalMeasure.unit)
        ≤ 8 * (tripleMass Q4.Candidate.UnitIntervalMeasure.unit h) ^ (1/3 : ℝ) :=
  attained_threshold_L1 Q4.Candidate.UnitIntervalMeasure.zero_left_mass
    Q4.Candidate.UnitIntervalMeasure.zero_right_mass h hP

end Q4.Candidate.ThresholdApproximation

#print axioms Q4.Candidate.ThresholdApproximation.minimum_threshold_exists
#print axioms Q4.Candidate.ThresholdApproximation.attained_threshold_cubic
#print axioms Q4.Candidate.ThresholdApproximation.sign_l1_distance
#print axioms Q4.Candidate.ThresholdApproximation.attained_threshold_L1_cubic
#print axioms Q4.Candidate.ThresholdApproximation.attained_threshold_L1
#print axioms Q4.Candidate.ThresholdApproximation.unit_attained_threshold_L1
