import Q4.Candidate.AntiperiodicThreshold
import Q4.Candidate.EnergyLipschitz

/-! Actual two-dimensional cost of replacing the upper diagonal half by
the negative lower half, and transfer to a canonical phase. -/
open MeasureTheory Set

namespace Q4.Candidate.AntiperiodicReplacement
open Q4.Candidate.UnitIntervalMeasure Q4.Candidate.AlternationKernel
open Q4.Candidate.ComparisonEnergy Q4.Candidate.DiagonalHalves
open Q4.Candidate.AntiperiodicThreshold

theorem anti_measurable (b : ℝ → Bool) (hb : Measurable b) : Measurable (anti b) :=
  diagonal_measurable b _ hb ((measurable_of_countable Bool.not).comp hb)

theorem canonical_measurable (o : Bool) : Measurable (canonical o) :=
  Measurable.ite (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const)
    measurable_const measurable_const

theorem replacement_cost (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1) :
    EnergyLipschitz.distance unit (diagonal b0 b1) (anti b0) ≤ 2*agreementMass b0 b1 := by
  let d : ℝ → ℝ := fun s => |spin (b1 s)-spin (!(b0 s))|
  let g : ℝ → ℝ := fun s => |spin (joined b0 b1 s)-spin (joined b0 (fun s => !(b0 s)) s)|
  have hn : Measurable (fun s => !(b0 s)) := (measurable_of_countable Bool.not).comp h0
  have hd : Measurable d := ((measurable_spin_comp _ h1).sub (measurable_spin_comp _ hn)).norm
  have hg : Measurable g := ((measurable_spin_comp _ (joined_measurable _ _ h0 h1)).sub
    (measurable_spin_comp _ (joined_measurable _ _ h0 hn))).norm
  have hde (s : ℝ) : d s = 2*({s | b0 s=b1 s} : Set ℝ).indicator (fun _ => (1:ℝ)) s := by
    cases he0 : b0 s <;> cases he1 : b1 s <;> norm_num [d,spin,he0,he1]
  have he := joined_square_integral g (fun _ => 0) d hg measurable_const hd 2 (by norm_num)
    (fun s => spin_distance_bound _ _) (fun _ => by norm_num) (fun s => spin_distance_bound _ _)
    (by intro s hs; simp [g,joined,hs.2])
    (by intro s hs; simp [g,d,joined,show ¬s+1<1 by linarith [hs.1]])
  have hdi : Integrable d unit := Integrable.of_bound hd.aestronglyMeasurable 2
    (Filter.Eventually.of_forall (fun s => spin_distance_bound _ _))
  have hw : Integrable (fun s => (1-s)*d s) unit := by
    apply Integrable.of_bound ((measurable_const.sub measurable_id).mul hd).aestronglyMeasurable 2
    filter_upwards [ae_restrict_mem measurableSet_Ioc (μ := (volume : Measure ℝ))] with s hs
    dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by linarith [hs.2] : 0 ≤ 1-s)]
    have hb := spin_distance_bound (b1 s) (!(b0 s))
    change ‖d s‖ ≤ 2 at hb
    nlinarith [norm_nonneg (d s),hs.1,hs.2]
  calc
    _ = ∫ s, (1-s)*d s ∂unit := by
      change (∫ p, g (p.1+p.2) ∂unit.prod unit) = _
      rw [he]
      simp only [mul_zero,zero_add]
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rfl
    _ ≤ ∫ s, d s ∂unit := by
      apply integral_mono_ae hw hdi
      filter_upwards [ae_restrict_mem measurableSet_Ioc (μ := (volume : Measure ℝ))] with s hs
      have hn : 0 ≤ d s := abs_nonneg _
      nlinarith [hs.1,hs.2]
    _ = 2*agreementMass b0 b1 := by
      simp_rw [hde]
      rw [integral_const_mul,integral_indicator (measurableSet_eq_fun h0 h1)]
      simp [agreementMass]

/-- Once the actual lower half is a threshold, the preceding replacement
cost and the true mean select an actual canonical phase for the original f. -/
theorem close_to_phase (f : Point → Bool) (hf : Measurable f)
    (o0 o1 : Bool) (c d : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    ∃ phase : Bool, EnergyLipschitz.distance unit f (canonical phase) ≤
      3*EnergyLipschitz.distance unit f (diagonal (threshold o0 c) (threshold o1 d))+
      6*agreementMass (threshold o0 c) (threshold o1 d)+2*|mean unit f| := by
  let b0 := threshold o0 c
  let b1 := threshold o1 d
  have h0 := threshold_measurable o0 c
  have h1 := threshold_measurable o1 d
  have h2 := diagonal_measurable b0 b1 h0 h1
  have h3 := anti_measurable b0 h0
  have hcost := replacement_cost b0 b1 h0 h1
  have htri := EnergyLipschitz.distance_triangle unit f (diagonal b0 b1) (anti b0) hf h2 h3
  have hm := EnergyLipschitz.mean_lipschitz unit (anti b0) f h3 hf
  rw [EnergyLipschitz.distance_symm unit (anti b0) f] at hm
  have hm' : |mean unit (anti b0)| ≤ |mean unit f|+
      EnergyLipschitz.distance unit f (anti b0) := by
    have ha := abs_sub_le (mean unit (anti b0)) (mean unit f) 0
    simp only [sub_zero] at ha
    linarith
  obtain ⟨phase,hphase⟩ := exists_phase_le_twice_abs_mean o0 c hc
  have hlast := EnergyLipschitz.distance_triangle unit f (anti b0) (canonical phase)
    hf h3 (canonical_measurable phase)
  change EnergyLipschitz.distance unit (anti b0) (canonical phase) ≤ 2*|mean unit (anti b0)| at hphase
  refine ⟨phase,?_⟩
  change EnergyLipschitz.distance unit f (canonical phase) ≤
    3*EnergyLipschitz.distance unit f (diagonal b0 b1)+6*agreementMass b0 b1+2*|mean unit f|
  linarith

end Q4.Candidate.AntiperiodicReplacement

#print axioms Q4.Candidate.AntiperiodicReplacement.replacement_cost
#print axioms Q4.Candidate.AntiperiodicReplacement.close_to_phase
