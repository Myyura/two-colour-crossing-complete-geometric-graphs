import Q4.Candidate.AntiperiodicThreshold
import Q4.Candidate.SliceStability
import Mathlib.MeasureTheory.Integral.Average

/-! Actual finite-window row selection and two-threshold approximation for a
measurable diagonal Boolean function. -/
open MeasureTheory Set
namespace Q4.Candidate.ThresholdHalfSelection
open Q4.Candidate.UnitIntervalMeasure Q4.Candidate.AlternationKernel
open Q4.Candidate.DiagonalHalves Q4.Candidate.AntiperiodicThreshold
open Q4.Candidate.SliceStability Q4.Candidate.ComparisonEnergy


/-- A genuine first-moment choice inside any positive subinterval of the unit
interval, using its actual Lebesgue mass and nonnegative total integral. -/
theorem select_interval (D : ℝ → ℝ) (hi : Integrable D unit)
    (hn : ∀ x, 0 ≤ D x) (a b C : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (havg : (∫ x, D x ∂unit) ≤ (b-a)*C) :
    ∃ v ∈ Icc a b, D v ≤ C := by
  have hsub : Ioc a b ⊆ Ioc (0:ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_le_of_lt ha hx.1,le_trans hx.2 hb⟩
  have he : unit.restrict (Ioc a b) = volume.restrict (Ioc a b) := by
    exact Measure.restrict_restrict_of_subset hsub
  have hDi : IntegrableOn D (Ioc a b) volume := by
    change Integrable D (volume.restrict (Ioc a b))
    rw [← he]
    exact hi.integrableOn
  obtain ⟨v,hv,hDv⟩ := exists_le_setAverage
    (by simpa [Real.volume_Ioc] using hab : volume (Ioc a b) ≠ 0)
    (by simp [Real.volume_Ioc] : volume (Ioc a b) ≠ ⊤) hDi
  refine ⟨v,⟨hv.1.le,hv.2⟩,hDv.trans ?_⟩
  rw [setAverage_eq,smul_eq_mul,Real.volume_real_Ioc,max_eq_left (sub_pos.mpr hab).le]
  have hmono : (∫ x in Ioc a b, D x) ≤ ∫ x, D x ∂unit := by
    rw [←he]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall hn)
  apply (inv_mul_le_iff₀ (sub_pos.mpr hab)).mpr
  linarith

noncomputable def diagonalFunction (b : ℝ → Bool) (p : Point) : Bool := b (p.1+p.2)

theorem diagonalFunction_measurable (b : ℝ → Bool) (hb : Measurable b) :
    Measurable (diagonalFunction b) := hb.comp (measurable_fst.add measurable_snd)

/-- Selection uses the actual row deficits derived from the energy identity.
The bound is stated polynomially in t, avoiding any approximate real arithmetic. -/
theorem select_row (f : Point → Bool) (hf : Measurable f) (t a : ℝ)
    (ht : 0 < t) (ha : 0 ≤ a) (ha1 : a+t ≤ 1)
    (hE : energy unit f ≤ 1/12+t^4) :
    ∃ v ∈ Icc a (a+t), rowDeficit f v ≤ 16*t^3 := by
  have havg : (∫ v, rowDeficit f v ∂unit) ≤ 16*t^4 := by
    rw [integral_rowDeficit f hf]
    exact (deficit_bounds unit f hf (t^4) hE).2.2.1
  apply select_interval (rowDeficit f) (rowDeficit_integrable f hf)
    (fun x => (rowDeficit_bounds f hf x).1) a (a+t) (16*t^3) ha ha1 (by linarith)
  nlinarith

theorem envelope_of_deficit_bound (f : Point → Bool) (hf : Measurable f)
    (v t : ℝ) (ht : 0 ≤ t) (hD : rowDeficit f v ≤ 16*t^3) :
    rowEnvelope f v ≤ 11*t := by
  have hn := (rowDeficit_bounds f hf v).1
  have hp : (rowEnvelope f v)^3 = 64*rowDeficit f v := by
    unfold rowEnvelope
    rw [mul_pow,←Real.rpow_mul_natCast hn (1/3:ℝ) 3]
    norm_num
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity : 0 ≤ 11*t)
  nlinarith [pow_nonneg ht 3]


theorem bounded_interval_upper (g : ℝ → ℝ) (hg : Measurable g)
    (hb : ∀ s, 0 ≤ g s ∧ g s ≤ 2) (a b : ℝ) (hab : a ≤ b) :
    (∫ s in a..b, g s) ≤ 2*(b-a) := by
  have hi := bounded_interval_integrable g hg 2 (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb s).1]; exact (hb s).2)
  have h := intervalIntegral.integral_mono_on hab (hi a b)
    (intervalIntegrable_const (c := (2:ℝ))) (fun s _ => (hb s).2)
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using h

/-- Restricting a row beginning at v to the lower unit half loses at most 2v. -/
theorem lower_interval_transfer (g : ℝ → ℝ) (hg : Measurable g)
    (hb : ∀ s, 0 ≤ g s ∧ g s ≤ 2) (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..1, g s) ≤ (∫ s in v..(v+1), g s)+2*v := by
  have hi := bounded_interval_integrable g hg 2 (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb s).1]; exact (hb s).2)
  have h0 := intervalIntegral.integral_add_adjacent_intervals (hi 0 v) (hi v 1)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi v 1) (hi 1 (v+1))
  have hp := intervalIntegral.integral_nonneg_of_forall (μ := volume) (show 1 ≤ v+1 by linarith [hv.1])
    (fun s => (hb s).1)
  have hbound := bounded_interval_upper g hg hb 0 v hv.1
  linarith

/-- Restricting a row beginning at v to the upper unit half loses at most 2(1-v). -/
theorem upper_interval_transfer (g : ℝ → ℝ) (hg : Measurable g)
    (hb : ∀ s, 0 ≤ g s ∧ g s ≤ 2) (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
    (∫ s in (1:ℝ)..2, g s) ≤ (∫ s in v..(v+1), g s)+2*(1-v) := by
  have hi := bounded_interval_integrable g hg 2 (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb s).1]; exact (hb s).2)
  have h0 := intervalIntegral.integral_add_adjacent_intervals (hi v 1) (hi 1 (v+1))
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi 1 (v+1)) (hi (v+1) 2)
  have hp := intervalIntegral.integral_nonneg_of_forall (μ := volume) hv.2 (fun s => (hb s).1)
  have hbound := bounded_interval_upper g hg hb (v+1) 2 (by linarith [hv.2])
  linarith

noncomputable def clip (c : ℝ) : ℝ := max 0 (min 1 c)

theorem clip_mem (c : ℝ) : clip c ∈ Icc (0:ℝ) 1 := by
  unfold clip
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem threshold_clip (o : Bool) (c x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
    threshold o (clip c) x = threshold o c x := by
  have hle : x ≤ clip c ↔ x ≤ c := by
    simp [clip,le_max_iff,not_le.mpr hx.1,hx.2.le]
  simp only [threshold,hle]

theorem sign_of_bool (h : ℝ → Bool) (x : ℝ) :
    Q4.Candidate.ThresholdApproximation.sign {x | h x = true} x = spin (h x) := by
  cases hx : h x <;> simp [spin,Q4.Candidate.ThresholdApproximation.sign,hx]

theorem thresholdError_spin (h : ℝ → Bool) (o : Bool) (c : ℝ) :
    thresholdError h o c = ∫ x in (0:ℝ)..1, |spin (h x)-spin (threshold o c x)| := by
  unfold thresholdError
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  change (∫ x, _ ∂unit) = ∫ x, _ ∂unit
  simp_rw [sign_of_bool,←threshold_spin]

noncomputable def lineError (b : ℝ → Bool) (o : Bool) (c : ℝ) (s : ℝ) : ℝ :=
  |spin (b s)-spin (threshold o c s)|

theorem lineError_measurable (b : ℝ → Bool) (hb : Measurable b) (o : Bool) (c : ℝ) :
    Measurable (lineError b o c) := real_abs_measurable _
      ((measurable_spin_comp _ hb).sub (measurable_spin_comp _ (threshold_measurable o c)))

theorem lineError_bounds (b : ℝ → Bool) (o : Bool) (c s : ℝ) :
    0 ≤ lineError b o c s ∧ lineError b o c s ≤ 2 := by
  refine ⟨abs_nonneg _,?_⟩
  simpa only [lineError,Real.norm_eq_abs,abs_abs] using spin_distance_bound (b s) (threshold o c s)

/-- Row threshold error after its actual coordinate translation. -/
theorem shifted_row_error (b : ℝ → Bool) (o : Bool) (c v : ℝ) :
    thresholdError (fun x => b (x+v)) o c =
      ∫ s in v..(v+1), lineError b o (c+v) s := by
  rw [thresholdError_spin]
  have ht := intervalIntegral.integral_comp_add_right (lineError b o (c+v)) v
    (a := (0:ℝ)) (b := (1:ℝ))
  simp only [zero_add,add_comm 1 v] at ht
  rw [←ht]
  apply intervalIntegral.integral_congr
  intro s _
  simp [lineError,threshold]

/-- Actual lower-half threshold extension, including clipping its cut to [0,1]. -/
theorem lower_threshold_transfer (b : ℝ → Bool) (hb : Measurable b) (o : Bool)
    (c v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..1, lineError b o (clip (c+v)) s) ≤
      thresholdError (fun x => b (x+v)) o c + 2*v := by
  have he : (∫ s in (0:ℝ)..1, lineError b o (clip (c+v)) s) =
      ∫ s in (0:ℝ)..1, lineError b o (c+v) s := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro s hs
    dsimp only [lineError]
    rw [threshold_clip o (c+v) s hs]
  rw [he,shifted_row_error]
  exact lower_interval_transfer _ (lineError_measurable b hb o (c+v))
    (lineError_bounds b o (c+v)) v hv

/-- Actual upper-half threshold extension after shifting the domain by one. -/
theorem upper_threshold_transfer (b : ℝ → Bool) (hb : Measurable b) (o : Bool)
    (c v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..1, lineError (fun x => b (x+1)) o (clip (c+v-1)) s) ≤
      thresholdError (fun x => b (x+v)) o c + 2*(1-v) := by
  have he : (∫ s in (0:ℝ)..1, lineError (fun x => b (x+1)) o (clip (c+v-1)) s) =
      ∫ s in (1:ℝ)..2, lineError b o (c+v) s := by
    have ht := intervalIntegral.integral_comp_add_right (lineError b o (c+v)) 1
      (a := (0:ℝ)) (b := (1:ℝ))
    norm_num only at ht
    rw [←ht]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro s hs
    dsimp only [lineError]
    rw [threshold_clip o (c+v-1) s hs]
    have hle : s ≤ c+v-1 ↔ s+1 ≤ c+v := by constructor <;> intro h <;> linarith
    simp only [threshold,hle]
  rw [he,shifted_row_error]
  exact upper_interval_transfer _ (lineError_measurable b hb o (c+v))
    (lineError_bounds b o (c+v)) v hv


/-- The lower half is approximated by an actual clipped threshold chosen on an
actual row in [t,2t], rather than by a threshold supplied as an input. -/
theorem lower_half_exists (b : ℝ → Bool) (hb : Measurable b) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1/8)
    (hE : energy unit (diagonalFunction b) ≤ 1/12+t^4) :
    ∃ o : Bool, ∃ c ∈ Icc (0:ℝ) 1,
      (∫ s in (0:ℝ)..1, lineError b o c s) ≤ 15*t := by
  have hf := diagonalFunction_measurable b hb
  obtain ⟨v,hv,hD⟩ := select_row (diagonalFunction b) hf t t ht ht.le (by linarith) hE
  obtain ⟨o,c,hc,he⟩ := row_threshold_exists (diagonalFunction b) hf v
  have henv := envelope_of_deficit_bound (diagonalFunction b) hf v t ht.le hD
  have htrans := lower_threshold_transfer b hb o c v ⟨by linarith [hv.1],by linarith [hv.2]⟩
  refine ⟨o,clip (c+v),clip_mem _,?_⟩
  change thresholdError (fun x => b (x+v)) o c ≤ _ at he
  linarith [hv.2]

/-- The upper half is approximated using an actual row in [1-2t,1-t]. -/
theorem upper_half_exists (b : ℝ → Bool) (hb : Measurable b) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1/8)
    (hE : energy unit (diagonalFunction b) ≤ 1/12+t^4) :
    ∃ o : Bool, ∃ c ∈ Icc (0:ℝ) 1,
      (∫ s in (0:ℝ)..1, lineError (fun x => b (x+1)) o c s) ≤ 15*t := by
  have hf := diagonalFunction_measurable b hb
  obtain ⟨v,hv,hD⟩ := select_row (diagonalFunction b) hf t (1-2*t) ht
    (by linarith) (by linarith) hE
  obtain ⟨o,c,hc,he⟩ := row_threshold_exists (diagonalFunction b) hf v
  have henv := envelope_of_deficit_bound (diagonalFunction b) hf v t ht.le hD
  have htrans := upper_threshold_transfer b hb o c v ⟨by linarith [hv.1],by linarith [hv.2]⟩
  refine ⟨o,clip (c+v-1),clip_mem _,?_⟩
  change thresholdError (fun x => b (x+v)) o c ≤ _ at he
  linarith [hv.1]

/-- The actual square distance is bounded by the sum of the two unweighted
half distances. The triangular density is proved, not assumed. -/
theorem diagonal_halves_distance_le (b b0 b1 : ℝ → Bool)
    (hb : Measurable b) (h0 : Measurable b0) (h1 : Measurable b1) :
    distance (diagonalFunction b) (diagonal b0 b1) ≤
      (∫ s in (0:ℝ)..1, |spin (b s)-spin (b0 s)|)+
      (∫ s in (0:ℝ)..1, |spin (b (s+1))-spin (b1 s)|) := by
  let g : ℝ → ℝ := fun s => |spin (b s)-spin (joined b0 b1 s)|
  let g0 : ℝ → ℝ := fun s => |spin (b s)-spin (b0 s)|
  let g1 : ℝ → ℝ := fun s => |spin (b (s+1))-spin (b1 s)|
  have hg : Measurable g := real_abs_measurable _ ((measurable_spin_comp _ hb).sub
    (measurable_spin_comp _ (joined_measurable b0 b1 h0 h1)))
  have hg0 : Measurable g0 := real_abs_measurable _ ((measurable_spin_comp _ hb).sub
    (measurable_spin_comp _ h0))
  have hg1 : Measurable g1 := real_abs_measurable _ ((measurable_spin_comp _
    (hb.comp (measurable_id.add measurable_const))).sub (measurable_spin_comp _ h1))
  have hb0 (s : ℝ) : ‖g0 s‖ ≤ 2 := spin_distance_bound _ _
  have hb1 (s : ℝ) : ‖g1 s‖ ≤ 2 := spin_distance_bound _ _
  have hd := joined_square_integral g g0 g1 hg hg0 hg1 2 (by norm_num)
    (fun s => spin_distance_bound _ _) hb0 hb1
    (by intro s hs; simp [g,g0,joined,hs.2])
    (by intro s hs; simp [g,g1,joined,show ¬s+1<1 by linarith [hs.1]])
  change (∫ p : Point, g (p.1+p.2) ∂unit.prod unit) ≤ _
  rw [hd]
  have hi0 := bounded_interval_integrable g0 hg0 2 hb0 0 1
  have hi1 := bounded_interval_integrable g1 hg1 2 hb1 0 1
  have hw0 := weighted_interval_integrable (fun s => s) g0 continuous_id hg0 2 hb0 0 1
  have hw1 := weighted_interval_integrable (fun s => 1-s) g1
    (continuous_const.sub continuous_id) hg1 2 hb1 0 1
  have he := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (hw0.add hw1) (hi0.add hi1) (fun s hs => by
      dsimp only [Pi.add_apply,g0,g1]
      nlinarith [abs_nonneg (spin (b s)-spin (b0 s)),
        abs_nonneg (spin (b (s+1))-spin (b1 s)),hs.1,hs.2])
  rw [intervalIntegral.integral_add hi0 hi1] at he
  exact he

/-- Actual two threshold halves with total two-dimensional error at most 30t. -/
theorem two_threshold_halves (b : ℝ → Bool) (hb : Measurable b) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1/8)
    (hE : energy unit (diagonalFunction b) ≤ 1/12+t^4) :
    ∃ o0 o1 : Bool, ∃ c0 ∈ Icc (0:ℝ) 1, ∃ c1 ∈ Icc (0:ℝ) 1,
      distance (diagonalFunction b) (diagonal (threshold o0 c0) (threshold o1 c1)) ≤ 30*t := by
  obtain ⟨o0,c0,hc0,he0⟩ := lower_half_exists b hb t ht ht1 hE
  obtain ⟨o1,c1,hc1,he1⟩ := upper_half_exists b hb t ht ht1 hE
  refine ⟨o0,o1,c0,hc0,c1,hc1,?_⟩
  have hd := diagonal_halves_distance_le b (threshold o0 c0) (threshold o1 c1) hb
    (threshold_measurable o0 c0) (threshold_measurable o1 c1)
  dsimp only [lineError] at he0 he1
  linarith

/-- The manuscript's exact fourth-root parameterization. -/
theorem two_threshold_halves_rpow (b : ℝ → Bool) (hb : Measurable b) (α : ℝ)
    (hα : 0 < α) (ht : α^(1/4:ℝ) ≤ 1/8)
    (hE : energy unit (diagonalFunction b) ≤ 1/12+α) :
    ∃ o0 o1 : Bool, ∃ c0 ∈ Icc (0:ℝ) 1, ∃ c1 ∈ Icc (0:ℝ) 1,
      distance (diagonalFunction b) (diagonal (threshold o0 c0) (threshold o1 c1)) ≤
        30*α^(1/4:ℝ) := by
  have hp : (α^(1/4:ℝ))^4 = α := by
    rw [←Real.rpow_mul_natCast hα.le (1/4:ℝ) 4]
    norm_num
  exact two_threshold_halves b hb (α^(1/4:ℝ)) (Real.rpow_pos_of_pos hα _) ht (by simpa only [hp] using hE)

end Q4.Candidate.ThresholdHalfSelection

#print axioms Q4.Candidate.ThresholdHalfSelection.select_interval
#print axioms Q4.Candidate.ThresholdHalfSelection.select_row
#print axioms Q4.Candidate.ThresholdHalfSelection.lower_threshold_transfer
#print axioms Q4.Candidate.ThresholdHalfSelection.upper_threshold_transfer
#print axioms Q4.Candidate.ThresholdHalfSelection.lower_half_exists
#print axioms Q4.Candidate.ThresholdHalfSelection.upper_half_exists
#print axioms Q4.Candidate.ThresholdHalfSelection.diagonal_halves_distance_le
#print axioms Q4.Candidate.ThresholdHalfSelection.two_threshold_halves
#print axioms Q4.Candidate.ThresholdHalfSelection.two_threshold_halves_rpow
