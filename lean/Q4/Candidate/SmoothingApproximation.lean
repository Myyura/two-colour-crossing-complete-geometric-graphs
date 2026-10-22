import Q4.Candidate.BoxAverage
import Q4.Candidate.SquareTranslation

/-! Actual uniform-box smoothing of the zero-extended coloring. This closes
the L1 approximation step on p.6; directional derivative and diagonal-line
approximation are separate obligations.
-/

open MeasureTheory Set

namespace Q4.Candidate.SmoothingApproximation

open Q4.Candidate.BoxAverage Q4.Candidate.SquareTranslation
open Q4.Candidate.ComparisonEnergy Q4.Candidate.UnitIntervalMeasure

abbrev Point := ℝ × ℝ

noncomputable def smoothed (f : Point → Bool) (h : ℝ) : Point → ℝ :=
  average (boxMeasure h) (zeroSquare f)

theorem smoothed_integrable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Integrable (smoothed f h) :=
  average_integrable (boxMeasure h) (zeroSquare f)
    (zeroSquare_measurable f hf) (zeroSquare_integrable f hf)

theorem smoothed_measurable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Measurable (smoothed f h) := by
  have hm : Measurable (fun p : Point × Point => zeroSquare f (p.2+p.1)) :=
    (zeroSquare_measurable f hf).comp (measurable_snd.add measurable_fst)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem zeroSquare_abs_le_one (f : Point → Bool) (p : Point) : |zeroSquare f p| ≤ 1 := by
  classical
  by_cases hp : p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1
  · simp only [zeroSquare, indicator_of_mem hp]
    simpa only [Real.norm_eq_abs] using le_of_eq (Q4.Candidate.AlternationKernel.spin_norm (f p))
  · simp [zeroSquare, hp]

theorem smoothed_abs_le_one (f : Point → Bool) (h : ℝ) (p : Point) :
    |smoothed f h p| ≤ 1 := by
  rw [←Real.norm_eq_abs]
  unfold smoothed average
  apply le_trans (norm_integral_le_of_norm_le_const (C := 1) ?_) (by simp)
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using zeroSquare_abs_le_one f (z+p))

theorem smoothing_error (f : Point → Bool) (hf : Measurable f) (ε h : ℝ) (hh : 0 ≤ h)
    (hE : energy unit f ≤ 1/12+ε) :
    (∫ p : Point, |zeroSquare f p-smoothed f h p|) ≤ 44*ε^(1/3 : ℝ)+8*h := by
  apply averaging_error_of_translation_bound (boxMeasure h) (zeroSquare f)
    (zeroSquare_measurable f hf) (zeroSquare_integrable f hf)
  filter_upwards [boxMeasure_supported h hh] with z hz
  have ht := SquareTranslation.translation_bound f hf ε z hE
  have ht' : (∫ p : Point, |zeroSquare f p-zeroSquare f (z+p)|) ≤
      44*ε^(1/3 : ℝ)+4*(|z.1|+|z.2|) := by
    simpa only [add_comm, abs_sub_comm] using ht
  linarith [hz.1,hz.2]

/-- The manuscript's 52h bound, parameterized by the genuine scale h with
energy excess at most h^6. No translation or averaging estimates are inputs. -/
theorem smoothing_error_52 (f : Point → Bool) (hf : Measurable f) (h : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hE : energy unit f ≤ 1/12+h^6) :
    (∫ p : Point, |zeroSquare f p-smoothed f h p|) ≤ 52*h := by
  have he := smoothing_error f hf (h^6) h hh hE
  have hp : (h^6)^(1/3 : ℝ) = h^2 := by
    rw [←Real.rpow_natCast_mul hh 6 (1/3 : ℝ)]
    norm_num
  rw [hp] at he
  nlinarith

end Q4.Candidate.SmoothingApproximation

#print axioms Q4.Candidate.SmoothingApproximation.smoothed_integrable
#print axioms Q4.Candidate.SmoothingApproximation.smoothed_measurable
#print axioms Q4.Candidate.SmoothingApproximation.smoothed_abs_le_one
#print axioms Q4.Candidate.SmoothingApproximation.smoothing_error
#print axioms Q4.Candidate.SmoothingApproximation.smoothing_error_52
