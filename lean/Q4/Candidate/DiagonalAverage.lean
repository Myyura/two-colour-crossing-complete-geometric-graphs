import Q4.Candidate.DiagonalCoordinates

/-! The genuine measurable mean on each diagonal segment of the interior
square. Empty and zero-length segments have value zero. The norm bound has
no lower bound on the length of a nonempty segment.
-/

open MeasureTheory Set

namespace Q4.Candidate.DiagonalAverage

open Q4.Candidate.DiagonalCoordinates

theorem fiber_integral_indicator (G : Point → ℝ) (h s : ℝ) :
    (∫ u, (interior h).indicator G (u,s-u)) =
      ∫ u in Icc (lower h s) (upper h s), G (u,s-u) := by
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with u
  classical
  by_cases hu : u ∈ Icc (lower h s) (upper h s)
  · rw [indicator_of_mem hu,indicator_of_mem ((fiber_membership h s u).mpr hu)]
  · rw [indicator_of_notMem hu,indicator_of_notMem (mt (fiber_membership h s u).mp hu)]

noncomputable def lineMean (G : Point → ℝ) (h s : ℝ) : ℝ :=
  (upper h s-lower h s)⁻¹ * ∫ u in Icc (lower h s) (upper h s), G (u,s-u)

theorem lineMean_measurable (G : Point → ℝ) (hG : Measurable G) (h : ℝ) :
    Measurable (lineMean G h) := by
  have hQ : MeasurableSet (interior h) := measurableSet_Icc.prod measurableSet_Icc
  have hj : Measurable (fun p : Point => (interior h).indicator G (diagonalEquiv p)) :=
    (hG.indicator hQ).comp diagonalEquiv.measurable
  have hi : Measurable (fun s => ∫ u in Icc (lower h s) (upper h s), G (u,s-u)) := by
    have hh : Measurable (fun s : ℝ => ∫ u : ℝ, (interior h).indicator G (diagonalEquiv (s,u))) :=
      hj.stronglyMeasurable.integral_prod_right'.measurable
    simpa only [diagonalEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, fiber_integral_indicator] using hh
  have hl : Measurable (lower h) := measurable_const.max (measurable_id.sub_const (1-h))
  have hu : Measurable (upper h) := measurable_const.min (measurable_id.sub_const h)
  exact (hu.sub hl).inv.mul hi

theorem lineMean_zero_of_empty (G : Point → ℝ) (h s : ℝ)
    (hs : upper h s ≤ lower h s) : lineMean G h s = 0 := by
  have hz : volume (Icc (lower h s) (upper h s)) = 0 := by
    simp [Real.volume_Icc, sub_nonpos.mpr hs]
  unfold lineMean
  rw [setIntegral_measure_zero _ hz, mul_zero]

theorem lineMean_abs_le_one (G : Point → ℝ) (h s : ℝ)
    (hG : ∀ p ∈ interior h, |G p| ≤ 1) : |lineMean G h s| ≤ 1 := by
  by_cases hs : lower h s < upper h s
  · have hi : |∫ u in Icc (lower h s) (upper h s), G (u,s-u)| ≤ upper h s-lower h s := by
      have hb := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (lower h s) (upper h s)))
        (f := fun u => G (u,s-u)) (C := 1) (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
          simpa only [Real.norm_eq_abs] using hG (u,s-u) ((fiber_membership h s u).mpr hu))
      simpa [Real.norm_eq_abs, Real.volume_real_Icc, hs.le] using hb
    unfold lineMean
    rw [abs_mul, abs_of_pos (inv_pos.mpr (sub_pos.mpr hs))]
    calc
      _ ≤ (upper h s-lower h s)⁻¹ * (upper h s-lower h s) :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (sub_nonneg.mpr hs.le))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr hs))
  · rw [lineMean_zero_of_empty G h s (le_of_not_gt hs)]
    norm_num

/-- Poincaré on the actual fiber, with the interval length bounded by one.
Only the absolutely continuous line restriction remains an application input. -/
theorem lineMean_poincare (G : Point → ℝ) (h s : ℝ) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval (fun u => G (u,s-u)) (lower h s) (upper h s)) :
    (∫ u in Icc (lower h s) (upper h s), |G (u,s-u)-lineMean G h s|) ≤
      ∫ u in Icc (lower h s) (upper h s), |deriv (fun t => G (t,s-t)) u| := by
  by_cases hs : lower h s < upper h s
  · have hb := Q4.Candidate.IntervalPoincare.interval_poincare hs hac
    change (∫ u in Icc (lower h s) (upper h s), |G (u,s-u)-lineMean G h s|) ≤
      (upper h s-lower h s)*(∫ u in (lower h s)..(upper h s), |deriv (fun t => G (t,s-t)) u|) at hb
    have he : (∫ u in (lower h s)..(upper h s), |deriv (fun t => G (t,s-t)) u|) =
        ∫ u in Icc (lower h s) (upper h s), |deriv (fun t => G (t,s-t)) u| := by
      rw [intervalIntegral.integral_of_le hs.le]
      exact setIntegral_congr_set Ioc_ae_eq_Icc
    rw [he] at hb
    exact hb.trans (mul_le_of_le_one_left (integral_nonneg (fun u => abs_nonneg _))
      (fiber_length_bound h s hh))
  · have hz : volume (Icc (lower h s) (upper h s)) = 0 := by
      simp [Real.volume_Icc, sub_nonpos.mpr (le_of_not_gt hs)]
    rw [setIntegral_measure_zero _ hz, setIntegral_measure_zero _ hz]

theorem fiber_integral_integrable (G : Point → ℝ) (h : ℝ)
    (hG : IntegrableOn G (interior h)) :
    Integrable (fun s => ∫ u in Icc (lower h s) (upper h s), G (u,s-u)) := by
  have hi := hG.integrable_indicator (measurableSet_Icc.prod measurableSet_Icc)
  have hj := (diagonal_preserving.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hp : Integrable (fun p : Point => (interior h).indicator G (diagonalEquiv p))
      ((volume : Measure ℝ).prod volume) := hj
  have hh := hp.integral_prod_left
  simpa only [diagonalEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, fiber_integral_indicator] using hh

/-- Integrated diagonal Poincaré with the genuine measurable fiber mean.
The AC and actual derivative-identification hypotheses are explicit; the box
derivative module must instantiate them before this implies smoothing stability. -/
theorem diagonal_poincare (G K : Point → ℝ) (h : ℝ) (hh : 0 ≤ h)
    (hG : Measurable G) (hbound : ∀ p ∈ interior h, |G p| ≤ 1)
    (hK : IntegrableOn K (interior h))
    (hac : ∀ᵐ s : ℝ, AbsolutelyContinuousOnInterval (fun u => G (u,s-u))
      (lower h s) (upper h s))
    (hder : ∀ᵐ s : ℝ, (fun u => deriv (fun t => G (t,s-t)) u) =ᵐ[
      volume.restrict (Icc (lower h s) (upper h s))] (fun u => K (u,s-u))) :
    (∫ p in interior h, |G p-lineMean G h (p.1+p.2)|) ≤ ∫ p in interior h, |K p| := by
  have hm := (lineMean_measurable G hG h).comp (measurable_fst.add measurable_snd)
  have hE : Measurable (fun p : Point => |G p-lineMean G h (p.1+p.2)|) := (hG.sub hm).norm
  have hi : IntegrableOn (fun p : Point => |G p-lineMean G h (p.1+p.2)|) (interior h) := by
    apply IntegrableOn.of_bound (by
      change volume (Icc h (1-h) ×ˢ Icc h (1-h)) < ⊤
      exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top)
      hE.aestronglyMeasurable 2
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    rw [Real.norm_eq_abs, abs_abs]
    linarith [abs_sub (G p) (lineMean G h (p.1+p.2)), hbound p hp,
      lineMean_abs_le_one G h (p.1+p.2) hbound]
  rw [interior_diagonal_integral _ h hi, interior_diagonal_integral _ h hK.abs]
  apply integral_mono_ae (fiber_integral_integrable _ h hi) (fiber_integral_integrable _ h hK.abs)
  filter_upwards [hac,hder] with s hs hd
  have hb := lineMean_poincare G h s hh hs
  have he : (∫ u in Icc (lower h s) (upper h s), |deriv (fun t => G (t,s-t)) u|) =
      ∫ u in Icc (lower h s) (upper h s), |K (u,s-u)| := by
    apply integral_congr_ae
    filter_upwards [hd] with u hu
    rw [hu]
  rw [he] at hb
  simpa only [add_sub_cancel] using hb

end Q4.Candidate.DiagonalAverage

#print axioms Q4.Candidate.DiagonalAverage.lineMean_measurable
#print axioms Q4.Candidate.DiagonalAverage.lineMean_zero_of_empty
#print axioms Q4.Candidate.DiagonalAverage.lineMean_abs_le_one
#print axioms Q4.Candidate.DiagonalAverage.lineMean_poincare
#print axioms Q4.Candidate.DiagonalAverage.fiber_integral_integrable
#print axioms Q4.Candidate.DiagonalAverage.diagonal_poincare
