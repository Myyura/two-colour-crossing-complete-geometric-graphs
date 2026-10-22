import Q4.Candidate.ThresholdTranslation
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine probability averaging and its L1 error, for the smoothing step
of candidate Theorem 2.1. The averaging function is defined by an integral;
its integrability and the transfer of translation estimates are proved.
-/

open MeasureTheory Set

namespace Q4.Candidate.BoxAverage

abbrev Point := ℝ × ℝ

instance point_volume_leftInvariant : (volume : Measure Point).IsAddLeftInvariant := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddLeftInvariant
  infer_instance

noncomputable def average (ν : Measure Point) (f : Point → ℝ) (x : Point) : ℝ :=
  ∫ z, f (z+x) ∂ν

theorem translated_joint_integrable (ν : Measure Point) [IsProbabilityMeasure ν]
    (f : Point → ℝ) (hf : Measurable f) (hi : Integrable f) :
    Integrable (fun p : Point × Point => f (p.1+p.2)) (ν.prod volume) := by
  apply (integrable_prod_iff (hf.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun z => hi.comp_add_left z), ?_⟩
  change Integrable (fun z : Point => ∫ x : Point, ‖f (z+x)‖) ν
  simp_rw [integral_add_left_eq_self (fun x => ‖f x‖)]
  exact integrable_const _

theorem average_integrable (ν : Measure Point) [IsProbabilityMeasure ν]
    (f : Point → ℝ) (hf : Measurable f) (hi : Integrable f) :
    Integrable (average ν f) :=
  (translated_joint_integrable ν f hf hi).integral_prod_right

theorem averaging_error (ν : Measure Point) [IsProbabilityMeasure ν]
    (f : Point → ℝ) (hf : Measurable f) (hi : Integrable f) :
    (∫ x, |f x-average ν f x|) ≤ ∫ z, ∫ x, |f x-f (z+x)| ∂volume ∂ν := by
  have hj := translated_joint_integrable ν f hf hi
  have hd : Integrable (fun p : Point × Point => f p.2-f (p.1+p.2)) (ν.prod volume) :=
    (hi.comp_snd ν).sub hj
  have habs : Integrable (fun p : Point × Point => |f p.2-f (p.1+p.2)|) (ν.prod volume) := hd.abs
  calc
    (∫ x, |f x-average ν f x|) ≤ ∫ x, ∫ z, |f x-f (z+x)| ∂ν ∂volume := by
      apply integral_mono_ae (hi.sub (average_integrable ν f hf hi)).abs habs.integral_prod_right
      filter_upwards [hj.prod_left_ae] with x hx
      have he : f x-average ν f x = ∫ z, f x-f (z+x) ∂ν := by
        rw [integral_sub (integrable_const _) hx]
        simp [average]
      simp only [Pi.sub_apply]
      rw [he]
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => f x-f (z+x))
    _ = _ := integral_integral_swap habs.swap

theorem averaging_error_of_translation_bound (ν : Measure Point) [IsProbabilityMeasure ν]
    (f : Point → ℝ) (hf : Measurable f) (hi : Integrable f) (L : ℝ)
    (hbound : ∀ᵐ z ∂ν, (∫ x, |f x-f (z+x)|) ≤ L) :
    (∫ x, |f x-average ν f x|) ≤ L := by
  have hd := (hi.comp_snd ν).sub (translated_joint_integrable ν f hf hi)
  calc
    _ ≤ ∫ z, ∫ x, |f x-f (z+x)| ∂volume ∂ν := averaging_error ν f hf hi
    _ ≤ ∫ _z, L ∂ν := integral_mono_ae hd.abs.integral_prod_left (integrable_const _) hbound
    _ = L := by simp

def boxMap (h : ℝ) (p : Point) : Point := (h*(2*p.1-1), h*(2*p.2-1))

theorem boxMap_measurable (h : ℝ) : Measurable (boxMap h) :=
  ((measurable_const.mul measurable_fst).sub measurable_const |>.const_mul h).prodMk
    ((measurable_const.mul measurable_snd).sub measurable_const |>.const_mul h)

/-- The actual product uniform distribution, obtained by affine transport of
the unit square. It remains well-defined at h=0. -/
noncomputable def boxMeasure (h : ℝ) : Measure Point :=
  (Q4.Candidate.UnitIntervalMeasure.unit.prod Q4.Candidate.UnitIntervalMeasure.unit).map (boxMap h)

instance boxMeasure_probability (h : ℝ) : IsProbabilityMeasure (boxMeasure h) := by
  unfold boxMeasure
  infer_instance

theorem boxMeasure_supported (h : ℝ) (hh : 0 ≤ h) :
    ∀ᵐ z ∂boxMeasure h, |z.1| ≤ h ∧ |z.2| ≤ h := by
  unfold boxMeasure
  have hm : MeasurableSet {z : Point | |z.1| ≤ h ∧ |z.2| ≤ h} :=
    (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).measurableSet.inter
      (isClosed_le (continuous_abs.comp continuous_snd) continuous_const).measurableSet
  apply (ae_map_iff (boxMap_measurable h).aemeasurable
    hm).mpr
  have hu : ∀ᵐ x ∂Q4.Candidate.UnitIntervalMeasure.unit, x ∈ Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hp : ∀ᵐ p ∂Q4.Candidate.UnitIntervalMeasure.unit.prod
      Q4.Candidate.UnitIntervalMeasure.unit, p.1 ∈ Ioc (0 : ℝ) 1 ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
    filter_upwards [hu] with x hx
    filter_upwards [hu] with y hy
    exact ⟨hx,hy⟩
  filter_upwards [hp] with p hp
  have hb (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) : |h*(2*x-1)| ≤ h := by
    rw [abs_le]
    constructor <;> nlinarith [hx.1,hx.2]
  exact ⟨hb p.1 hp.1,hb p.2 hp.2⟩

theorem translation_triangle (f : Point → ℝ) (hi : Integrable f) (z w : Point) :
    (∫ x, |f x-f ((z+w)+x)|) ≤
      (∫ x, |f x-f (z+x)|) + (∫ x, |f x-f (w+x)|) := by
  have ha : Integrable (fun x => |f x-f (z+x)|) := (hi.sub (hi.comp_add_left z)).abs
  have hb : Integrable (fun x => |f (z+x)-f (w+(z+x))|) := by
    simpa only [Function.comp_apply, Pi.sub_apply] using
      ((hi.sub (hi.comp_add_left w)).abs.comp_add_left z)
  have he (x : Point) : (z+w)+x = w+(z+x) := by abel
  calc
    _ ≤ ∫ x, |f x-f (z+x)| + |f (z+x)-f (w+(z+x))| := by
      apply integral_mono (hi.sub (hi.comp_add_left (z+w))).abs (ha.add hb)
      intro x
      dsimp only [Pi.sub_apply, Pi.add_apply]
      rw [he]
      exact abs_sub_le _ _ _
    _ = _ := by
      rw [integral_add ha hb,
        integral_add_left_eq_self (fun x => |f x-f (w+x)|) z]

/-- The actual uniform box smoothing error from the two coordinate estimates.
This is the step 44 ε^(1/3)+8h before substituting h=ε^(1/6). -/
theorem box_averaging_error (f : Point → ℝ) (hf : Measurable f) (hi : Integrable f)
    (A h : ℝ) (hh : 0 ≤ h)
    (hx : ∀ d : ℝ, (∫ x, |f x-f ((d,0)+x)|) ≤ A+4*|d|)
    (hy : ∀ d : ℝ, (∫ x, |f x-f ((0,d)+x)|) ≤ A+4*|d|) :
    (∫ x, |f x-average (boxMeasure h) f x|) ≤ 2*A+8*h := by
  apply averaging_error_of_translation_bound (boxMeasure h) f hf hi
  filter_upwards [boxMeasure_supported h hh] with z hz
  have ht := translation_triangle f hi (z.1,0) (0,z.2)
  have he : (z.1,0)+(0,z.2) = z := by ext <;> simp
  rw [he] at ht
  linarith [hx z.1,hy z.2,hz.1,hz.2]

end Q4.Candidate.BoxAverage

#print axioms Q4.Candidate.BoxAverage.translated_joint_integrable
#print axioms Q4.Candidate.BoxAverage.average_integrable
#print axioms Q4.Candidate.BoxAverage.averaging_error
#print axioms Q4.Candidate.BoxAverage.averaging_error_of_translation_bound
#print axioms Q4.Candidate.BoxAverage.boxMeasure_supported
#print axioms Q4.Candidate.BoxAverage.translation_triangle
#print axioms Q4.Candidate.BoxAverage.box_averaging_error
