import Q4.Candidate.ThresholdApproximation
import Mathlib.MeasureTheory.Group.Integral

/-!
Actual Lebesgue translation bounds for zero-extended thresholds. These are
the bounded-variation input to the smoothing step of candidate Theorem 2.1.
No smoothing or two-dimensional stability conclusion is assumed here.
-/

open MeasureTheory Set
open scoped symmDiff

namespace Q4.Candidate.ThresholdTranslation

noncomputable def interval (a b : ℝ) : ℝ → ℝ :=
  (Ioc a b).indicator (fun _ => 1)

theorem interval_integrable (a b : ℝ) : Integrable (interval a b) := by
  exact (integrableOn_const (by simp [Real.volume_Ioc])).integrable_indicator measurableSet_Ioc

theorem interval_translate (a b d x : ℝ) :
    interval a b (x+d) = interval (a-d) (b-d) x := by
  classical
  simp only [interval, indicator_apply, mem_Ioc]
  congr 1
  apply propext
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem interval_difference_integral (a b c d : ℝ) :
    (∫ x, |interval a b x - interval c d x|) =
      volume.real (Ioc a b ∆ Ioc c d) := by
  classical
  have he : (fun x => |interval a b x - interval c d x|) =
      (Ioc a b ∆ Ioc c d).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hp : x ∈ Ioc a b <;> by_cases hq : x ∈ Ioc c d <;>
      norm_num [interval, indicator_apply, mem_symmDiff, hp, hq]
  rw [he, integral_indicator (measurableSet_Ioc.symmDiff measurableSet_Ioc), integral_const]
  simp

theorem interval_translation_bound (a b d : ℝ) :
    (∫ x, |interval a b (x+d) - interval a b x|) ≤ 2*|d| := by
  simp_rw [interval_translate]
  rw [interval_difference_integral]
  have hs : Ioc (a-d) (b-d) ∆ Ioc a b ⊆
      Icc (min (a-d) a) (max (a-d) a) ∪
        Icc (min (b-d) b) (max (b-d) b) := by
    intro x hx
    simp only [mem_symmDiff, mem_Ioc] at hx
    simp only [mem_union, mem_Icc, min_le_iff, le_max_iff]
    rcases hx with ⟨hx, hn⟩ | ⟨hx, hn⟩
    · by_cases ha : a < x
      · right
        have hb : b < x := by simpa only [ha, true_and, not_le] using hn
        exact ⟨Or.inr hb.le, Or.inl hx.2⟩
      · left
        exact ⟨Or.inl hx.1.le, Or.inr (le_of_not_gt ha)⟩
    · by_cases ha : a-d < x
      · right
        have hb : b-d < x := by simpa only [ha, true_and, not_le] using hn
        exact ⟨Or.inl hb.le, Or.inr hx.2⟩
      · left
        exact ⟨Or.inr hx.1.le, Or.inl (le_of_not_gt ha)⟩
  calc
    volume.real (Ioc (a-d) (b-d) ∆ Ioc a b)
      ≤ volume.real (Icc (min (a-d) a) (max (a-d) a) ∪
          Icc (min (b-d) b) (max (b-d) b)) := measureReal_mono hs
            (measure_union_lt_top (by simp [Real.volume_Icc]) (by simp [Real.volume_Icc])).ne
    _ ≤ volume.real (Icc (min (a-d) a) (max (a-d) a)) +
          volume.real (Icc (min (b-d) b) (max (b-d) b)) := measureReal_union_le _ _
    _ = 2*|d| := by
      rw [Real.volume_real_Icc, Real.volume_real_Icc]
      by_cases hd : 0 ≤ d
      · rw [min_eq_left (by linarith : a-d ≤ a), max_eq_right (by linarith : a-d ≤ a),
          min_eq_left (by linarith : b-d ≤ b), max_eq_right (by linarith : b-d ≤ b),
          abs_of_nonneg hd, max_eq_left (by linarith), max_eq_left (by linarith)]
        ring
      · have hd' : d ≤ 0 := le_of_not_ge hd
        rw [min_eq_right (by linarith : a ≤ a-d), max_eq_left (by linarith : a ≤ a-d),
          min_eq_right (by linarith : b ≤ b-d), max_eq_left (by linarith : b ≤ b-d),
          abs_of_nonpos hd', max_eq_left (by linarith), max_eq_left (by linarith)]
        ring

/-- For 0≤c≤1 this is precisely the threshold +1 up to c, -1 thereafter,
extended by zero off (0,1]. Negating it covers the other orientation. -/
noncomputable def threshold (c : ℝ) (x : ℝ) : ℝ :=
  interval 0 c x - interval c 1 x

theorem threshold_integrable (c : ℝ) : Integrable (threshold c) :=
  (interval_integrable 0 c).sub (interval_integrable c 1)

theorem threshold_translation_bound (c d : ℝ) :
    (∫ x, |threshold c (x+d) - threshold c x|) ≤ 4*|d| := by
  have hi (a b : ℝ) : Integrable (fun x => |interval a b (x+d) - interval a b x|) := by
    simp_rw [interval_translate]
    exact ((interval_integrable (a-d) (b-d)).sub (interval_integrable a b)).abs
  have ht : Integrable (fun x => |threshold c (x+d) - threshold c x|) := by
    unfold threshold
    simp_rw [interval_translate]
    simpa only [zero_sub, Pi.sub_apply] using
      (((interval_integrable (-d) (c-d)).sub (interval_integrable (c-d) (1-d))).sub
        ((interval_integrable 0 c).sub (interval_integrable c 1))).abs
  calc
    (∫ x, |threshold c (x+d) - threshold c x|)
      ≤ ∫ x, |interval 0 c (x+d) - interval 0 c x| +
          |interval c 1 (x+d) - interval c 1 x| := by
        apply integral_mono ht ((hi 0 c).add (hi c 1))
        intro x
        calc
          _ = |(interval 0 c (x+d) - interval 0 c x) -
                (interval c 1 (x+d) - interval c 1 x)| := by
                  unfold threshold
                  dsimp only
                  rw [show interval 0 c (x+d) - interval c 1 (x+d) -
                    (interval 0 c x-interval c 1 x) =
                    (interval 0 c (x+d)-interval 0 c x) -
                    (interval c 1 (x+d)-interval c 1 x) by ring]
          _ ≤ _ := abs_sub _ _
    _ = (∫ x, |interval 0 c (x+d) - interval 0 c x|) +
          (∫ x, |interval c 1 (x+d) - interval c 1 x|) := integral_add (hi 0 c) (hi c 1)
    _ ≤ 4*|d| := by linarith [interval_translation_bound 0 c d,
      interval_translation_bound c 1 d]

theorem translation_transfer (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (d : ℝ) :
    (∫ x, |f (x+d)-f x|) ≤ 2*(∫ x, |f x-g x|) + (∫ x, |g (x+d)-g x|) := by
  have hf' := hf.comp_add_right d
  have hg' := hg.comp_add_right d
  have ha : Integrable (fun x => |f (x+d)-g (x+d)|) := (hf'.sub hg').abs
  have hb : Integrable (fun x => |g (x+d)-g x|) := (hg'.sub hg).abs
  have hc : Integrable (fun x => |g x-f x|) := (hg.sub hf).abs
  have hab : Integrable (fun x => |f (x+d)-g (x+d)| + |g (x+d)-g x|) := ha.add hb
  calc
    (∫ x, |f (x+d)-f x|)
      ≤ ∫ x, (|f (x+d)-g (x+d)| + |g (x+d)-g x|) + |g x-f x| := by
        apply integral_mono (hf'.sub hf).abs
          ((ha.add hb).add hc)
        intro x
        dsimp only [Pi.add_apply, Pi.sub_apply]
        have h1 := abs_sub_le (f (x+d)) (g (x+d)) (f x)
        have h2 := abs_sub_le (g (x+d)) (g x) (f x)
        linarith
    _ = _ := by
      rw [integral_add hab hc,
        integral_add ha hb,
        integral_add_right_eq_self (fun x => |f x-g x|) d]
      simp_rw [abs_sub_comm (g _) (f _)]
      ring

noncomputable def oriented (o : Bool) (c : ℝ) : ℝ → ℝ :=
  if o then threshold c else fun x => -threshold c x

theorem oriented_integrable (o : Bool) (c : ℝ) : Integrable (oriented o c) := by
  cases o <;> simp only [oriented, Bool.false_eq_true, ite_false, ite_true]
  · exact (threshold_integrable c).neg
  · exact threshold_integrable c

theorem oriented_translation_bound (o : Bool) (c d : ℝ) :
    (∫ x, |oriented o c (x+d)-oriented o c x|) ≤ 4*|d| := by
  cases o
  · simpa only [oriented, Bool.false_eq_true, ite_false, neg_sub_neg, abs_sub_comm]
      using threshold_translation_bound c d
  · exact threshold_translation_bound c d

noncomputable def zeroExtend (f : ℝ → ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) 1).indicator f

theorem zeroExtend_integrable (f : ℝ → ℝ)
    (hf : Integrable f Q4.Candidate.UnitIntervalMeasure.unit) :
    Integrable (zeroExtend f) := by
  change IntegrableOn f (Ioc (0 : ℝ) 1) at hf
  exact hf.integrable_indicator measurableSet_Ioc

theorem zeroExtend_distance (f g : ℝ → ℝ) :
    (∫ x, |zeroExtend f x-zeroExtend g x|) =
      ∫ x, |f x-g x| ∂Q4.Candidate.UnitIntervalMeasure.unit := by
  classical
  have he : (fun x => |zeroExtend f x-zeroExtend g x|) =
      (Ioc (0 : ℝ) 1).indicator (fun x => |f x-g x|) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;> simp [zeroExtend, hx]
  rw [he, integral_indicator measurableSet_Ioc]
  rfl

theorem zeroExtend_threshold (o : Bool) (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) :
    zeroExtend (Q4.Candidate.ThresholdApproximation.sign
      (if o then Iic c else Ioi c)) = oriented o c := by
  classical
  funext x
  rcases hc with ⟨hc0,hc1⟩
  cases o <;> simp only [oriented, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    by_cases hx0 : 0 < x <;> by_cases hx1 : x ≤ 1 <;> by_cases hxc : x ≤ c <;>
      simp_all [zeroExtend, Q4.Candidate.ThresholdApproximation.sign, threshold,
        interval, mem_Ioc, mem_Iic, mem_Ioi] <;> linarith

/-- The exact one-dimensional translation estimate used before smoothing.
The approximation error is the actual restricted-Lebesgue L1 distance. -/
theorem zeroExtend_translation_bound (f : ℝ → ℝ)
    (hf : Integrable f Q4.Candidate.UnitIntervalMeasure.unit)
    (o : Bool) (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (d : ℝ) :
    (∫ x, |zeroExtend f (x+d)-zeroExtend f x|) ≤
      2*(∫ x, |f x-Q4.Candidate.ThresholdApproximation.sign
        (if o then Iic c else Ioi c) x| ∂Q4.Candidate.UnitIntervalMeasure.unit) + 4*|d| := by
  have ht := translation_transfer (zeroExtend f) (oriented o c)
    (zeroExtend_integrable f hf) (oriented_integrable o c) d
  rw [← zeroExtend_threshold o c hc, zeroExtend_distance] at ht
  have hb := oriented_translation_bound o c d
  rw [zeroExtend_threshold o c hc] at ht
  linarith

end Q4.Candidate.ThresholdTranslation

#print axioms Q4.Candidate.ThresholdTranslation.interval_translation_bound
#print axioms Q4.Candidate.ThresholdTranslation.threshold_translation_bound
#print axioms Q4.Candidate.ThresholdTranslation.translation_transfer
#print axioms Q4.Candidate.ThresholdTranslation.zeroExtend_threshold
#print axioms Q4.Candidate.ThresholdTranslation.zeroExtend_translation_bound
