import Q4.Candidate.DiagonalHalves
import Q4.Candidate.DiagonalCoordinates

/-! Exact mean and phase distances for the antiperiodic extension of an
actual threshold. All square integrals use genuine restricted Lebesgue
measure; the diagonal-density formula is derived from a preserving map. -/

open MeasureTheory Set

namespace Q4.Candidate.AntiperiodicThreshold

open Q4.Candidate.UnitIntervalMeasure Q4.Candidate.AlternationKernel
open Q4.Candidate.DiagonalHalves Q4.Candidate.DiagonalCoordinates

theorem square_measure : unit.prod unit = volume.restrict (interior 0) := by
  rw [unit_eq_closed_interval,Measure.prod_restrict]
  simp only [Q4.Candidate.DiagonalCoordinates.interior,sub_zero]
  rfl

theorem diagonal_weight (s : ℝ) :
    max (upper 0 s-lower 0 s) 0 =
      (Ioc (0:ℝ) 1).indicator (fun t => t) s+
      (Ioc (1:ℝ) 2).indicator (fun t => 2-t) s := by
  classical
  by_cases h0 : s ≤ 0
  · have h1 : s ≤ 1 := by linarith
    have hs : s-1 ≤ 0 := by linarith
    have hm0 : s ∉ Ioc (0:ℝ) 1 := fun h => not_lt_of_ge h0 h.1
    have hm1 : s ∉ Ioc (1:ℝ) 2 := fun h => not_lt_of_ge h1 h.1
    simp [lower,upper,min_eq_right h1,max_eq_left hs,max_eq_right h0,hm0,hm1]
  · have hs0 : 0 < s := lt_of_not_ge h0
    by_cases h1 : s ≤ 1
    · have hs : s-1 ≤ 0 := by linarith
      have hm0 : s ∈ Ioc (0:ℝ) 1 := ⟨hs0,h1⟩
      have hm1 : s ∉ Ioc (1:ℝ) 2 := fun h => not_lt_of_ge h1 h.1
      simp [lower,upper,min_eq_right h1,max_eq_left hs,max_eq_left hs0.le,hm0,hm1]
    · have hs1 : 1 < s := lt_of_not_ge h1
      have hm0 : s ∉ Ioc (0:ℝ) 1 := fun h => not_le_of_gt hs1 h.2
      by_cases h2 : s ≤ 2
      · have hs : 0 ≤ s-1 := by linarith
        have hlen : 0 ≤ 1-(s-1) := by linarith
        have hm1 : s ∈ Ioc (1:ℝ) 2 := ⟨hs1,h2⟩
        simp [lower,upper,min_eq_left hs1.le,max_eq_right hs,max_eq_left hlen,hm0,hm1]
        ring
      · have hs : 0 ≤ s-1 := by linarith
        have hlen : 1-(s-1) ≤ 0 := by linarith
        have hm1 : s ∉ Ioc (1:ℝ) 2 := fun h => h2 h.2
        simp [lower,upper,min_eq_left hs1.le,max_eq_right hs,max_eq_right hlen,hm0,hm1]

/-- The exact triangular density of u+v on the unit square, obtained from
the actual diagonal change of variables and its finite interval fibers. -/
theorem diagonal_density (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ s, ‖g s‖ ≤ C) :
    (∫ p : ℝ × ℝ, g (p.1+p.2) ∂unit.prod unit) =
      (∫ s in (0:ℝ)..1, s*g s)+(∫ s in (1:ℝ)..2, (2-s)*g s) := by
  have hG : Integrable (fun p : ℝ × ℝ => g (p.1+p.2)) (unit.prod unit) :=
    Integrable.of_bound (hg.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun p => hbound (p.1+p.2)))
  rw [square_measure] at hG ⊢
  rw [interior_diagonal_integral _ 0 hG]
  have hpoint (s : ℝ) : (∫ u in Icc (lower 0 s) (upper 0 s), g (u+(s-u))) =
      (Ioc (0:ℝ) 1).indicator (fun t => t*g t) s+
      (Ioc (1:ℝ) 2).indicator (fun t => (2-t)*g t) s := by
    simp only [add_sub_cancel,integral_const,smul_eq_mul,measureReal_restrict_apply_univ,Real.volume_real_Icc]
    rw [diagonal_weight,add_mul]
    classical
    by_cases h0 : s ∈ Ioc (0:ℝ) 1 <;> by_cases h1 : s ∈ Ioc (1:ℝ) 2 <;>
      simp [h0,h1]
  simp_rw [hpoint]
  have hi0 : IntegrableOn (fun s => s*g s) (Ioc (0:ℝ) 1) := by
    apply IntegrableOn.of_bound (by simp [Real.volume_Ioc])
      (measurable_id.mul hg).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos hs.1]
    nlinarith [hbound s,norm_nonneg (g s),hs.1,hs.2]
  have hi1 : IntegrableOn (fun s => (2-s)*g s) (Ioc (1:ℝ) 2) := by
    apply IntegrableOn.of_bound (by simp [Real.volume_Ioc])
      ((measurable_const.sub measurable_id).mul hg).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by linarith [hs.2] : 0 ≤ 2-s)]
    nlinarith [hbound s,norm_nonneg (g s),hs.1,hs.2]
  rw [integral_add (hi0.integrable_indicator measurableSet_Ioc) (hi1.integrable_indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioc,integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (1:ℝ) ≤ 2)]

theorem weighted_interval_integrable (w g : ℝ → ℝ) (hw : Continuous w) (hg : Measurable g)
    (C : ℝ) (hbound : ∀ s, ‖g s‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable (fun s => w s*g s) volume a b := by
  have hi : IntervalIntegrable w volume a b := hw.intervalIntegrable a b
  exact ⟨hi.1.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hbound),
    hi.2.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hbound)⟩

theorem joined_square_integral (g g0 g1 : ℝ → ℝ) (hg : Measurable g)
    (h0 : Measurable g0) (h1 : Measurable g1) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ s, ‖g s‖ ≤ C) (hb0 : ∀ s, ‖g0 s‖ ≤ C) (hb1 : ∀ s, ‖g1 s‖ ≤ C)
    (hlower : ∀ s ∈ Ioo (0:ℝ) 1, g s = g0 s)
    (hupper : ∀ s ∈ Ioo (0:ℝ) 1, g (s+1) = g1 s) :
    (∫ p : ℝ × ℝ, g (p.1+p.2) ∂unit.prod unit) =
      ∫ s in (0:ℝ)..1, s*g0 s+(1-s)*g1 s := by
  rw [diagonal_density g hg C hC hb]
  have hl : (∫ s in (0:ℝ)..1, s*g s) = ∫ s in (0:ℝ)..1, s*g0 s := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro s hs
    dsimp only
    rw [hlower s hs]
  have hu : (∫ s in (1:ℝ)..2, (2-s)*g s) = ∫ s in (0:ℝ)..1, (1-s)*g1 s := by
    have hshift := intervalIntegral.integral_comp_add_right (fun s => (2-s)*g s) 1
      (a := (0:ℝ)) (b := (1:ℝ))
    norm_num only at hshift
    rw [← hshift]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro s hs
    dsimp only
    rw [hupper s hs]
    ring
  rw [hl,hu]
  exact (intervalIntegral.integral_add
    (weighted_interval_integrable (fun s => s) g0 continuous_id h0 C hb0 0 1)
    (weighted_interval_integrable (fun s => 1-s) g1 (continuous_const.sub continuous_id) h1 C hb1 0 1)).symm

noncomputable def anti (b : ℝ → Bool) : (ℝ × ℝ) → Bool := diagonal b (fun s => !(b s))
noncomputable def canonical (o : Bool) (p : ℝ × ℝ) : Bool := if p.1+p.2 < 1 then o else !o

theorem spin_not (o : Bool) : spin (!o) = -spin o := by cases o <;> norm_num [spin]

theorem anti_mean (b : ℝ → Bool) (hb : Measurable b) :
    Q4.Candidate.ComparisonEnergy.mean unit (anti b) =
      ∫ s in (0:ℝ)..1, (2*s-1)*spin (b s) := by
  have hn : Measurable (fun s => !(b s)) := (measurable_of_countable Bool.not).comp hb
  have he := joined_square_integral
    (fun s => spin (joined b (fun s => !(b s)) s)) (fun s => spin (b s)) (fun s => -spin (b s))
    (measurable_spin_comp _ (joined_measurable b _ hb hn))
    (measurable_spin_comp _ hb) (measurable_spin_comp _ hb).neg 1 (by norm_num)
    (fun s => le_of_eq (spin_norm _)) (fun s => le_of_eq (spin_norm _))
    (fun s => by rw [norm_neg]; exact le_of_eq (spin_norm _))
    (by intro s hs; simp [joined,hs.2])
    (by intro s hs; simp [joined,show ¬s+1 < 1 by linarith [hs.1],spin_not])
  change (∫ p : ℝ × ℝ, spin (joined b (fun s => !(b s)) (p.1+p.2)) ∂unit.prod unit) = _
  rw [he]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  ring

theorem weighted_threshold_integral (w : ℝ → ℝ) (hw : Continuous w)
    (o : Bool) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..1, w s*spin (threshold o c s)) =
      spin o*(2*(∫ s in (0:ℝ)..c, w s)-(∫ s in (0:ℝ)..1, w s)) := by
  have hi := weighted_interval_integrable w _ hw
    (measurable_spin_comp _ (threshold_measurable o c)) 1 (fun s => le_of_eq (spin_norm _))
  have hp := intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c 1)
  have hl : (∫ s in (0:ℝ)..c, w s*spin (threshold o c s)) = (∫ s in (0:ℝ)..c, w s)*spin o := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr_Ioo_of_le hc.1
    intro s hs
    simp [threshold,hs.2.le]
  have hr : (∫ s in c..1, w s*spin (threshold o c s)) = (∫ s in c..1, w s)*(-spin o) := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr_Ioo_of_le hc.2
    intro s hs
    simp [threshold,not_le.mpr hs.1,spin_not]
  rw [hl,hr] at hp
  have hwadd := intervalIntegral.integral_add_adjacent_intervals
    (hw.intervalIntegrable (μ := volume) 0 c) (hw.intervalIntegrable (μ := volume) c 1)
  rw [← hp,← hwadd]
  ring

/-- The actual antiperiodic threshold has the manuscript's exact signed mean. -/
theorem antiperiodic_threshold_mean (o : Bool) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    Q4.Candidate.ComparisonEnergy.mean unit (anti (threshold o c)) =
      -2*spin o*c*(1-c) := by
  rw [anti_mean _ (threshold_measurable o c),weighted_threshold_integral (fun s => 2*s-1)
    ((continuous_const.mul continuous_id).sub continuous_const) o c hc]
  have hi (t : ℝ) : (∫ s in (0:ℝ)..t, (2*s-1)) = t^2-t := by
    have hlin : IntervalIntegrable (fun s : ℝ => 2*s) volume 0 t :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hlin
      (intervalIntegrable_const (c := (1:ℝ))),intervalIntegral.integral_const_mul,
      integral_id,intervalIntegral.integral_const]
    simp
    ring
  rw [hi c,hi 1]
  ring

noncomputable def distance (f g : (ℝ × ℝ) → Bool) : ℝ :=
  ∫ p, |spin (f p)-spin (g p)| ∂unit.prod unit

theorem spin_distance_bound (a b : Bool) : ‖|spin a-spin b|‖ ≤ 2 := by
  cases a <;> cases b <;> norm_num [spin]

/-- Both diagonal halves contribute complementary density weights, which sum
to one; this proves the actual 2D phase distance equals a 1D threshold distance. -/
theorem real_abs_measurable (g : ℝ → ℝ) (hg : Measurable g) : Measurable (fun s => |g s|) :=
  continuous_abs.measurable.comp hg

theorem anti_phase_distance (b : ℝ → Bool) (hb : Measurable b) (o : Bool) :
    distance (anti b) (canonical o) = ∫ s in (0:ℝ)..1, |spin (b s)-spin o| := by
  let g : ℝ → ℝ := fun s => |spin (joined b (fun s => !(b s)) s)-
    spin (if s<1 then o else !o)|
  let g0 : ℝ → ℝ := fun s => |spin (b s)-spin o|
  have hn : Measurable (fun s => !(b s)) := (measurable_of_countable Bool.not).comp hb
  have hg : Measurable g := real_abs_measurable _ ((measurable_spin_comp _ (joined_measurable b _ hb hn)).sub
    (measurable_spin_comp _ (Measurable.ite
      (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const)))
  have hg0 : Measurable g0 := real_abs_measurable _ ((measurable_spin_comp _ hb).sub measurable_const)
  have he := joined_square_integral g g0 g0 hg hg0 hg0 2 (by norm_num)
    (fun s => spin_distance_bound _ _) (fun s => spin_distance_bound _ _) (fun s => spin_distance_bound _ _)
    (by intro s hs; simp [g,g0,joined,hs.2])
    (by
      intro s hs
      simp only [g,g0,joined,ite_eq_right (show ¬s+1<1 by linarith [hs.1]),add_sub_cancel_right,spin_not]
      rw [show -spin (b s) - -spin o = -(spin (b s)-spin o) by ring,abs_neg])
  change (∫ p : ℝ × ℝ, g (p.1+p.2) ∂unit.prod unit) = _
  rw [he]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [g0]
  ring

theorem threshold_distance_same (o : Bool) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..1, |spin (threshold o c s)-spin o|) = 2*(1-c) := by
  have hi := bounded_interval_integrable (fun s => |spin (threshold o c s)-spin o|)
    (real_abs_measurable _ ((measurable_spin_comp _ (threshold_measurable o c)).sub measurable_const)) 2
    (fun s => spin_distance_bound _ _)
  have hp := intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c 1)
  have hl : (∫ s in (0:ℝ)..c, |spin (threshold o c s)-spin o|) = 0 := by
    calc
      _ = ∫ s in (0:ℝ)..c, (0:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc.1
        intro s hs
        simp [threshold,hs.2.le]
      _ = _ := by simp
  have hr : (∫ s in c..1, |spin (threshold o c s)-spin o|) = 2*(1-c) := by
    calc
      _ = ∫ s in c..1, (2:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc.2
        intro s hs
        cases o <;> norm_num [threshold,not_le.mpr hs.1,spin]
      _ = _ := by simp; ring
  rw [hl,hr,zero_add] at hp
  exact hp.symm

theorem threshold_distance_opposite (o : Bool) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..1, |spin (threshold o c s)-spin (!o)|) = 2*c := by
  have hi := bounded_interval_integrable (fun s => |spin (threshold o c s)-spin (!o)|)
    (real_abs_measurable _ ((measurable_spin_comp _ (threshold_measurable o c)).sub measurable_const)) 2
    (fun s => spin_distance_bound _ _)
  have hp := intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c 1)
  have hl : (∫ s in (0:ℝ)..c, |spin (threshold o c s)-spin (!o)|) = 2*c := by
    calc
      _ = ∫ s in (0:ℝ)..c, (2:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc.1
        intro s hs
        cases o <;> norm_num [threshold,hs.2.le,spin]
      _ = _ := by simp; ring
  have hr : (∫ s in c..1, |spin (threshold o c s)-spin (!o)|) = 0 := by
    calc
      _ = ∫ s in c..1, (0:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc.2
        intro s hs
        simp [threshold,not_le.mpr hs.1]
      _ = _ := by simp
  rw [hl,hr,add_zero] at hp
  exact hp.symm

/-- The exact distance to the nearer of the two global canonical phases. -/
theorem nearest_phase_distance (o : Bool) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    min (distance (anti (threshold o c)) (canonical true))
      (distance (anti (threshold o c)) (canonical false)) = 2*min c (1-c) := by
  have hs := threshold_distance_same o c hc
  have ho := threshold_distance_opposite o c hc
  rw [← anti_phase_distance _ (threshold_measurable o c) o] at hs
  rw [← anti_phase_distance _ (threshold_measurable o c) (!o)] at ho
  cases o <;> simp only [Bool.not_false,Bool.not_true] at hs ho
  · rw [hs,ho]
    exact (mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)).symm
  · rw [hs,ho,min_comm]
    exact (mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)).symm

/-- The actual nearest canonical phase is controlled by twice the absolute
actual mean of the antiperiodic threshold. -/
theorem nearest_phase_le_twice_abs_mean (o : Bool) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    min (distance (anti (threshold o c)) (canonical true))
      (distance (anti (threshold o c)) (canonical false)) ≤
      2*|Q4.Candidate.ComparisonEnergy.mean unit (anti (threshold o c))| := by
  rw [nearest_phase_distance o c hc,antiperiodic_threshold_mean o c hc]
  have hmin : min c (1-c) ≤ 2*c*(1-c) := by
    by_cases h : c ≤ 1-c
    · rw [min_eq_left h]; nlinarith [hc.1,hc.2]
    · rw [min_eq_right (le_of_not_ge h)]; nlinarith [hc.1,hc.2]
  have habs : |-2*spin o*c*(1-c)| = 2*c*(1-c) := by
    rw [abs_mul,abs_mul,abs_mul]
    cases o <;> simp [spin,abs_of_nonneg hc.1,abs_of_nonneg (sub_nonneg.mpr hc.2)]
  rw [habs]
  linarith

/-- An actual choice among the two phases attains the mean-controlled bound. -/
theorem exists_phase_le_twice_abs_mean (o : Bool) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    ∃ phase : Bool, distance (anti (threshold o c)) (canonical phase) ≤
      2*|Q4.Candidate.ComparisonEnergy.mean unit (anti (threshold o c))| := by
  have h := nearest_phase_le_twice_abs_mean o c hc
  by_cases hd : distance (anti (threshold o c)) (canonical true) ≤
      distance (anti (threshold o c)) (canonical false)
  · exact ⟨true,by simpa only [min_eq_left hd] using h⟩
  · exact ⟨false,by simpa only [min_eq_right (le_of_not_ge hd)] using h⟩

end Q4.Candidate.AntiperiodicThreshold

#print axioms Q4.Candidate.AntiperiodicThreshold.diagonal_density
#print axioms Q4.Candidate.AntiperiodicThreshold.antiperiodic_threshold_mean
#print axioms Q4.Candidate.AntiperiodicThreshold.anti_phase_distance
#print axioms Q4.Candidate.AntiperiodicThreshold.nearest_phase_distance
#print axioms Q4.Candidate.AntiperiodicThreshold.nearest_phase_le_twice_abs_mean

#print axioms Q4.Candidate.AntiperiodicThreshold.exists_phase_le_twice_abs_mean
