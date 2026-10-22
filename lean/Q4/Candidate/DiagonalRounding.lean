import Q4.Candidate.BoxDerivative
import Q4.Candidate.SmoothingApproximation
import Q4.Candidate.EnergyLipschitz

/-! Actual boundary area and Boolean rounding of the diagonal box mean.
The diagonal function is defined by a measurable integral, and the boundary
area is computed from Lebesgue measure, not supplied as an assumption. -/
open MeasureTheory Set

namespace Q4.Candidate.DiagonalRounding
open Q4.Candidate.UnitIntervalMeasure Q4.Candidate.AlternationKernel
open Q4.Candidate.ComparisonEnergy Q4.Candidate.BoxDerivative
open Q4.Candidate.SmoothingApproximation Q4.Candidate.DiagonalCoordinates
open Q4.Candidate.DiagonalAverage Q4.Candidate.SquareTranslation

abbrev Point := ℝ × ℝ

noncomputable def diagonalMean (f : Point → Bool) (h : ℝ) : ℝ → ℝ :=
  lineMean (smoothed f h) h

theorem diagonalMean_measurable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Measurable (diagonalMean f h) := lineMean_measurable _ (smoothed_measurable f hf h) h

theorem diagonalMean_abs_le_one (f : Point → Bool) (h s : ℝ) :
    |diagonalMean f h s| ≤ 1 :=
  lineMean_abs_le_one _ h s (fun p _ => smoothed_abs_le_one f h p)

theorem interior_subset_square (h : ℝ) (hh : 0 ≤ h) :
    interior h ⊆ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
  intro p hp
  constructor <;> constructor <;>
    linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2]

/-- Restriction to the inner square is genuine Lebesgue measure. -/
theorem unit_square_restrict_interior (h : ℝ) (hh : 0 ≤ h) :
    (unit.prod unit).restrict (interior h) = volume.restrict (interior h) := by
  rw [unit_eq_closed_interval,Measure.prod_restrict,←Measure.volume_eq_prod,
    Measure.restrict_restrict (show MeasurableSet (interior h) from measurableSet_Icc.prod measurableSet_Icc),
    inter_eq_left.mpr (interior_subset_square h hh)]

/-- The exact interior area, including h≥1/2 where the interval is empty
or null. The max comes from the actual Lebesgue interval measure. -/
theorem interior_area (h : ℝ) (hh : 0 ≤ h) :
    (unit.prod unit).real (interior h) = (max (1-2*h) 0)^2 := by
  have he := congrArg (fun μ : Measure Point => μ.real Set.univ) (unit_square_restrict_interior h hh)
  simp only [measureReal_restrict_apply MeasurableSet.univ,univ_inter] at he
  rw [he,DiagonalCoordinates.interior,Measure.volume_eq_prod,measureReal_prod_prod,Real.volume_real_Icc]
  rw [show 1-h-h = 1-2*h by ring]
  ring

/-- The discarded boundary strip has probability/Lebesgue area at most 4h. -/
theorem boundary_area_le (h : ℝ) (hh : 0 ≤ h) :
    (unit.prod unit).real (interior h)ᶜ ≤ 4*h := by
  rw [measureReal_compl (show MeasurableSet (interior h) from measurableSet_Icc.prod measurableSet_Icc),probReal_univ,interior_area h hh]
  by_cases hs : 0 ≤ 1-2*h
  · rw [max_eq_left hs]
    nlinarith [sq_nonneg h]
  · rw [max_eq_right (le_of_not_ge hs)]
    nlinarith

theorem diagonal_error_integrable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Integrable (fun p : Point => |smoothed f h p-diagonalMean f h (p.1+p.2)|) (unit.prod unit) := by
  apply Integrable.of_bound ((smoothed_measurable f hf h).sub
    ((diagonalMean_measurable f hf h).comp (measurable_fst.add measurable_snd))).norm.aestronglyMeasurable 2
  filter_upwards [] with p
  simp only [Real.norm_eq_abs,abs_abs,Pi.sub_apply,Function.comp_apply,Pi.add_apply]
  have ht := abs_sub (smoothed f h p) (diagonalMean f h (p.1+p.2))
  linarith [smoothed_abs_le_one f h p,diagonalMean_abs_le_one f h (p.1+p.2)]

theorem diagonal_error_global (f : Point → Bool) (hf : Measurable f) (h : ℝ)
    (hh : 0 < h) (hE : energy unit f ≤ 1/12+h^6) :
    (∫ p : Point, |smoothed f h p-diagonalMean f h (p.1+p.2)| ∂unit.prod unit) ≤ 10*h := by
  have hi := diagonal_error_integrable f hf h
  rw [←integral_add_compl (s := interior h) (show MeasurableSet (interior h) from measurableSet_Icc.prod measurableSet_Icc) hi]
  have hint : (∫ p in interior h, |smoothed f h p-diagonalMean f h (p.1+p.2)| ∂unit.prod unit) ≤ 2*h := by
    rw [unit_square_restrict_interior h hh.le]
    exact box_diagonal_poincare f hf h hh hE
  have hboundary : (∫ p in (interior h)ᶜ, |smoothed f h p-diagonalMean f h (p.1+p.2)| ∂unit.prod unit) ≤ 8*h := by
    calc
      _ ≤ ∫ _p in (interior h)ᶜ, (2:ℝ) ∂unit.prod unit := by
        apply integral_mono hi.integrableOn (integrable_const _)
        intro p
        have ht := abs_sub (smoothed f h p) (diagonalMean f h (p.1+p.2))
        linarith [smoothed_abs_le_one f h p,diagonalMean_abs_le_one f h (p.1+p.2)]
      _ = 2*(unit.prod unit).real (interior h)ᶜ := by simp [mul_comm]
      _ ≤ _ := by linarith [boundary_area_le h hh.le]
  linarith

theorem spin_smoothing_error (f : Point → Bool) (hf : Measurable f) (h : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hE : energy unit f ≤ 1/12+h^6) :
    (∫ p : Point, |spin (f p)-smoothed f h p| ∂unit.prod unit) ≤ 52*h := by
  have he : (∫ p : Point, |spin (f p)-smoothed f h p| ∂unit.prod unit) =
      ∫ p : Point, |zeroSquare f p-smoothed f h p| ∂unit.prod unit := by
    apply integral_congr_ae
    have hu : ∀ᵐ p ∂unit.prod unit, p ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1 := by
      rw [unit,Measure.prod_restrict,←Measure.volume_eq_prod]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hu] with p hp
    rw [zeroSquare,indicator_of_mem hp]
  rw [he,unit,Measure.prod_restrict,←Measure.volume_eq_prod]
  have hi := ((zeroSquare_integrable f hf).sub (smoothed_integrable f hf h)).abs
  exact (integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun p => abs_nonneg (zeroSquare f p-smoothed f h p))) hi).trans
      (smoothing_error_52 f hf h hh hh1 hE)

theorem spin_diagonal_error_integrable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Integrable (fun p : Point => |spin (f p)-diagonalMean f h (p.1+p.2)|) (unit.prod unit) := by
  apply Integrable.of_bound ((measurable_spin_comp f hf).sub
    ((diagonalMean_measurable f hf h).comp (measurable_fst.add measurable_snd))).norm.aestronglyMeasurable 2
  filter_upwards [] with p
  simp only [Real.norm_eq_abs,abs_abs,Pi.sub_apply,Function.comp_apply,Pi.add_apply]
  have hs : |spin (f p)| = 1 := spin_norm (f p)
  linarith [abs_sub (spin (f p)) (diagonalMean f h (p.1+p.2)),diagonalMean_abs_le_one f h (p.1+p.2)]

/-- Genuine global diagonal approximation, before Boolean rounding. -/
theorem spin_diagonal_error (f : Point → Bool) (hf : Measurable f) (h : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hE : energy unit f ≤ 1/12+h^6) :
    (∫ p : Point, |spin (f p)-diagonalMean f h (p.1+p.2)| ∂unit.prod unit) ≤ 62*h := by
  have hspin : Integrable (fun p => spin (f p)) (unit.prod unit) :=
    bounded_integrable _ _ (measurable_spin_comp f hf) (fun p => (spin_norm (f p)).le)
  have hsmooth : Integrable (smoothed f h) (unit.prod unit) :=
    bounded_integrable _ _ (smoothed_measurable f hf h) (fun p => smoothed_abs_le_one f h p)
  have ha := (hspin.sub hsmooth).abs
  have hb := diagonal_error_integrable f hf h
  calc
    _ ≤ ∫ p : Point, |spin (f p)-smoothed f h p|+|smoothed f h p-diagonalMean f h (p.1+p.2)| ∂unit.prod unit := by
      apply integral_mono (spin_diagonal_error_integrable f hf h) (ha.add hb)
      intro p
      exact abs_sub_le _ _ _
    _ = (∫ p : Point, |spin (f p)-smoothed f h p| ∂unit.prod unit)+
        ∫ p : Point, |smoothed f h p-diagonalMean f h (p.1+p.2)| ∂unit.prod unit := integral_add ha hb
    _ ≤ _ := by linarith [spin_smoothing_error f hf h hh.le hh1 hE,diagonal_error_global f hf h hh hE]

noncomputable def roundedProfile (f : Point → Bool) (h s : ℝ) : Bool :=
  if 0 ≤ diagonalMean f h s then true else false
noncomputable def rounded (f : Point → Bool) (h : ℝ) (p : Point) : Bool :=
  roundedProfile f h (p.1+p.2)

theorem roundedProfile_measurable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Measurable (roundedProfile f h) :=
  Measurable.ite (measurableSet_le measurable_const (diagonalMean_measurable f hf h))
    measurable_const measurable_const

theorem rounded_measurable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Measurable (rounded f h) :=
  (roundedProfile_measurable f hf h).comp (measurable_fst.add measurable_snd)

/-- Pointwise nearest-sign rounding, with the tie at zero assigned true. -/
theorem rounding_bound (b : Bool) (t : ℝ) :
    |spin b-spin (if 0 ≤ t then true else false)| ≤ 2*|spin b-t| := by
  cases b <;> by_cases ht : 0 ≤ t
  · simp only [ite_eq_left ht,spin,Bool.false_eq_true,ite_false,ite_true]
    rw [abs_of_nonpos (by linarith : -1-t ≤ 0)]
    norm_num
    linarith
  · simp [ht,spin]
  · simp [ht,spin]
  · simp only [ite_eq_right ht,spin,ite_true,Bool.false_eq_true,ite_false]
    rw [abs_of_nonneg (by linarith : 0 ≤ 1-t)]
    norm_num
    linarith

/-- The actual rounded coloring depends only on u+v and is within 128h
in spin L1 distance (the proved intermediate bound is the stronger 124h). -/
theorem rounded_distance (f : Point → Bool) (hf : Measurable f) (h : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hE : energy unit f ≤ 1/12+h^6) :
    EnergyLipschitz.distance unit f (rounded f h) ≤ 128*h := by
  have hi := spin_diagonal_error_integrable f hf h
  calc
    _ ≤ ∫ p : Point, 2*|spin (f p)-diagonalMean f h (p.1+p.2)| ∂unit.prod unit := by
      apply integral_mono (EnergyLipschitz.pointDistance_integrable unit f (rounded f h)
        hf (rounded_measurable f hf h)) (hi.const_mul 2)
      intro p
      exact rounding_bound (f p) (diagonalMean f h (p.1+p.2))
    _ = 2*(∫ p : Point, |spin (f p)-diagonalMean f h (p.1+p.2)| ∂unit.prod unit) := integral_const_mul _ _
    _ ≤ _ := by linarith [spin_diagonal_error f hf h hh hh1 hE]

/-- Actual energy transfer to the constructed diagonal Boolean coloring.
The constant 129 is stronger than the candidate's conservative 257. -/
theorem rounded_energy (f : Point → Bool) (hf : Measurable f) (h : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hE : energy unit f ≤ 1/12+h^6) :
    energy unit (rounded f h) ≤ 1/12+129*h := by
  have hp := EnergyLipschitz.energy_lipschitz unit f (rounded f h) hf (rounded_measurable f hf h)
  have hd := rounded_distance f hf h hh hh1 hE
  have h6 : h^6 ≤ h := by
    have h5 : h^5 ≤ 1 := pow_le_one₀ hh.le hh1
    calc
      h^6 = h*h^5 := by ring
      _ ≤ h*1 := mul_le_mul_of_nonneg_left h5 hh.le
      _ = h := mul_one _
  linarith [(abs_le.mp hp).1]

/-- Constructive-by-definition measurable one-variable profile, assembled
with both the actual approximation and actual energy estimates. -/
theorem exists_diagonal_rounding (f : Point → Bool) (hf : Measurable f) (h : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hE : energy unit f ≤ 1/12+h^6) :
    ∃ b : ℝ → Bool, Measurable b ∧
      EnergyLipschitz.distance unit f (fun p => b (p.1+p.2)) ≤ 128*h ∧
      energy unit (fun p => b (p.1+p.2)) ≤ 1/12+257*h := by
  refine ⟨roundedProfile f h,roundedProfile_measurable f hf h,rounded_distance f hf h hh hh1 hE,?_⟩
  have he := rounded_energy f hf h hh hh1 hE
  change energy unit (rounded f h) ≤ 1/12+257*h
  linarith

end Q4.Candidate.DiagonalRounding

#print axioms Q4.Candidate.DiagonalRounding.interior_area
#print axioms Q4.Candidate.DiagonalRounding.boundary_area_le
#print axioms Q4.Candidate.DiagonalRounding.spin_diagonal_error
#print axioms Q4.Candidate.DiagonalRounding.roundedProfile_measurable
#print axioms Q4.Candidate.DiagonalRounding.rounded_distance

#print axioms Q4.Candidate.DiagonalRounding.rounded_energy
#print axioms Q4.Candidate.DiagonalRounding.exists_diagonal_rounding
