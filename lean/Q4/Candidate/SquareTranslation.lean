import Q4.Candidate.SliceStability
import Q4.Candidate.ThresholdTranslation

/-! Actual coordinate translations of the zero-extended square coloring. -/
open MeasureTheory MeasureTheory.Measure Set

namespace Q4.Candidate.SquareTranslation
open Q4.Candidate.UnitIntervalMeasure
open Q4.Candidate.AlternationKernel
open Q4.Candidate.ComparisonEnergy
open Q4.Candidate.SliceStability
open Q4.Candidate.ThresholdTranslation

local instance : (volume : Measure Point).IsAddRightInvariant := by
  change ((volume : Measure ℝ).prod volume).IsAddRightInvariant
  infer_instance

noncomputable def zeroSquare (f : Point → Bool) : Point → ℝ :=
  ((Ioc (0:ℝ) 1) ×ˢ (Ioc (0:ℝ) 1)).indicator (fun p => spin (f p))

theorem zeroSquare_measurable (f : Point → Bool) (hf : Measurable f) :
    Measurable (zeroSquare f) :=
  (measurable_spin_comp f hf).indicator (measurableSet_Ioc.prod measurableSet_Ioc)

theorem zeroSquare_integrable (f : Point → Bool) (hf : Measurable f) :
    Integrable (zeroSquare f) := by
  have hi : Integrable (fun p => spin (f p)) (unit.prod unit) :=
    bounded_integrable _ _ (measurable_spin_comp f hf) (fun p => le_of_eq (spin_norm (f p)))
  rw [unit,Measure.prod_restrict,←Measure.volume_eq_prod] at hi
  exact (show IntegrableOn (fun p => spin (f p))
    ((Ioc (0:ℝ) 1) ×ˢ (Ioc (0:ℝ) 1)) volume from hi).integrable_indicator
      (measurableSet_Ioc.prod measurableSet_Ioc)

theorem zeroSquare_row (f : Point → Bool) (u v : ℝ) :
    zeroSquare f (u,v) = if v ∈ Ioc (0:ℝ) 1 then
      zeroExtend (fun x => spin (f (x,v))) u else 0 := by
  classical
  by_cases hu : u ∈ Ioc (0:ℝ) 1 <;> by_cases hv : v ∈ Ioc (0:ℝ) 1 <;>
    simp [zeroSquare,zeroExtend,hu,hv]
theorem zeroSquare_col (f : Point → Bool) (u v : ℝ) :
    zeroSquare f (u,v) = if u ∈ Ioc (0:ℝ) 1 then
      zeroExtend (fun y => spin (f (u,y))) v else 0 := by
  classical
  by_cases hu : u ∈ Ioc (0:ℝ) 1 <;> by_cases hv : v ∈ Ioc (0:ℝ) 1 <;>
    simp [zeroSquare,zeroExtend,hu,hv]

theorem sign_bool (h : ℝ → Bool) (x : ℝ) :
    Q4.Candidate.ThresholdApproximation.sign {x | h x = true} x = spin (h x) := by
  cases hx : h x <;> simp [Q4.Candidate.ThresholdApproximation.sign,spin,hx]

theorem row_slice_translation (f : Point → Bool) (hf : Measurable f) (v d : ℝ) :
    (∫ u, |zeroExtend (fun x => spin (f (x,v))) (u+d) -
      zeroExtend (fun x => spin (f (x,v))) u|) ≤ 2*rowEnvelope f v + 4*|d| := by
  have hfi : Integrable (fun x => spin (f (x,v))) unit :=
    bounded_integrable _ _ (measurable_spin_comp _ (hf.comp (measurable_id.prodMk measurable_const)))
      (fun x => le_of_eq (spin_norm (f (x,v))))
  obtain ⟨o,t,ht,he⟩ := row_threshold_exists f hf v
  have hb := zeroExtend_translation_bound (fun x => spin (f (x,v))) hfi o t ht d
  unfold thresholdError at he
  simp_rw [sign_bool] at he
  linarith

theorem col_slice_translation (f : Point → Bool) (hf : Measurable f) (u d : ℝ) :
    (∫ v, |zeroExtend (fun y => spin (f (u,y))) (v+d) -
      zeroExtend (fun y => spin (f (u,y))) v|) ≤ 2*colEnvelope f u + 4*|d| := by
  have hfi : Integrable (fun y => spin (f (u,y))) unit :=
    bounded_integrable _ _ (measurable_spin_comp _ (hf.comp (measurable_const.prodMk measurable_id)))
      (fun y => le_of_eq (spin_norm (f (u,y))))
  obtain ⟨o,t,ht,he⟩ := col_threshold_exists f hf u
  have hb := zeroExtend_translation_bound (fun y => spin (f (u,y))) hfi o t ht d
  unfold thresholdError at he
  simp_rw [sign_bool] at he
  linarith

/-- The full-plane translation bound in the first coordinate, including the
boundary of the zero-extended square. -/
theorem row_translation_bound (f : Point → Bool) (hf : Measurable f) (α d : ℝ)
    (hE : energy unit f ≤ 1/12+α) :
    (∫ p : Point, |zeroSquare f (p.1+d,p.2)-zeroSquare f p|) ≤
      22*α^(1/3 : ℝ)+4*|d| := by
  have hi := zeroSquare_integrable f hf
  have hd : Integrable (fun p : Point => |zeroSquare f (p.1+d,p.2)-zeroSquare f p|) := by
    simpa only [Prod.add_def,add_zero,zero_add,Pi.sub_apply] using ((hi.comp_add_right (d,0)).sub hi).abs
  have hdp : Integrable (fun p : Point => |zeroSquare f (p.1+d,p.2)-zeroSquare f p|)
      (volume.prod volume) := by rwa [←Measure.volume_eq_prod]
  obtain ⟨_,hEi,hEa,_⟩ := row_average_stability f hf α hE
  have hbound : Integrable (fun v => 2*rowEnvelope f v+4*|d|) unit :=
    (hEi.const_mul 2).add (integrable_const _)
  have hbound0 : Integrable ((Ioc (0:ℝ) 1).indicator (fun v => 2*rowEnvelope f v+4*|d|)) :=
    (show IntegrableOn _ (Ioc (0:ℝ) 1) volume from hbound).integrable_indicator measurableSet_Ioc
  rw [Measure.volume_eq_prod,integral_prod_symm _ hdp]
  calc
    _ ≤ ∫ v, (Ioc (0:ℝ) 1).indicator (fun v => 2*rowEnvelope f v+4*|d|) v := by
      apply integral_mono hdp.integral_prod_right hbound0
      intro v
      by_cases hv : v ∈ Ioc (0:ℝ) 1
      · simpa only [zeroSquare_row,hv,ite_true,indicator_of_mem hv] using row_slice_translation f hf v d
      · simp [zeroSquare_row,hv]
    _ = 2*(∫ v, rowEnvelope f v ∂unit)+4*|d| := by
      rw [integral_indicator measurableSet_Ioc]
      change (∫ v, 2*rowEnvelope f v+4*|d| ∂unit) = _
      rw [integral_add (hEi.const_mul 2) (integrable_const _),integral_const_mul]
      simp
    _ ≤ _ := by linarith

/-- The symmetric full-plane bound in the second coordinate. -/
theorem col_translation_bound (f : Point → Bool) (hf : Measurable f) (α d : ℝ)
    (hE : energy unit f ≤ 1/12+α) :
    (∫ p : Point, |zeroSquare f (p.1,p.2+d)-zeroSquare f p|) ≤
      22*α^(1/3 : ℝ)+4*|d| := by
  have hi := zeroSquare_integrable f hf
  have hd : Integrable (fun p : Point => |zeroSquare f (p.1,p.2+d)-zeroSquare f p|) := by
    simpa only [Prod.add_def,add_zero,zero_add,Pi.sub_apply] using ((hi.comp_add_right (0,d)).sub hi).abs
  have hdp : Integrable (fun p : Point => |zeroSquare f (p.1,p.2+d)-zeroSquare f p|)
      (volume.prod volume) := by rwa [←Measure.volume_eq_prod]
  obtain ⟨_,hEi,hEa,_⟩ := col_average_stability f hf α hE
  have hbound : Integrable (fun u => 2*colEnvelope f u+4*|d|) unit :=
    (hEi.const_mul 2).add (integrable_const _)
  have hbound0 : Integrable ((Ioc (0:ℝ) 1).indicator (fun u => 2*colEnvelope f u+4*|d|)) :=
    (show IntegrableOn _ (Ioc (0:ℝ) 1) volume from hbound).integrable_indicator measurableSet_Ioc
  rw [Measure.volume_eq_prod,integral_prod _ hdp]
  calc
    _ ≤ ∫ u, (Ioc (0:ℝ) 1).indicator (fun u => 2*colEnvelope f u+4*|d|) u := by
      apply integral_mono hdp.integral_prod_left hbound0
      intro u
      by_cases hu : u ∈ Ioc (0:ℝ) 1
      · simpa only [zeroSquare_col,hu,ite_true,indicator_of_mem hu] using col_slice_translation f hf u d
      · simp [zeroSquare_col,hu]
    _ = 2*(∫ u, colEnvelope f u ∂unit)+4*|d| := by
      rw [integral_indicator measurableSet_Ioc]
      change (∫ u, 2*colEnvelope f u+4*|d| ∂unit) = _
      rw [integral_add (hEi.const_mul 2) (integrable_const _),integral_const_mul]
      simp
    _ ≤ _ := by linarith

/-- Combining coordinate translations gives the genuine two-dimensional
translation estimate needed by probability box averaging. -/
theorem translation_bound (f : Point → Bool) (hf : Measurable f) (α : ℝ) (z : Point)
    (hE : energy unit f ≤ 1/12+α) :
    (∫ p : Point, |zeroSquare f (p+z)-zeroSquare f p|) ≤
      44*α^(1/3 : ℝ)+4*(|z.1|+|z.2|) := by
  have hi := zeroSquare_integrable f hf
  let R : Point → ℝ := fun p => |zeroSquare f (p.1+z.1,p.2)-zeroSquare f p|
  let C : Point → ℝ := fun p => |zeroSquare f (p.1,p.2+z.2)-zeroSquare f p|
  have hR : Integrable R := by simpa only [R,Prod.add_def,add_zero,zero_add,Pi.sub_apply] using ((hi.comp_add_right (z.1,0)).sub hi).abs
  have hC : Integrable C := by simpa only [C,Prod.add_def,add_zero,zero_add,Pi.sub_apply] using ((hi.comp_add_right (0,z.2)).sub hi).abs
  calc
    _ ≤ ∫ p : Point, R (p+(0,z.2)) + C p := by
      apply integral_mono ((hi.comp_add_right z).sub hi).abs
        ((hR.comp_add_right (0,z.2)).add hC)
      intro p
      simpa only [R,C,Prod.add_def,Prod.fst,Prod.snd,add_zero,zero_add,Pi.add_apply,Pi.sub_apply] using abs_sub_le (zeroSquare f (p+z))
        (zeroSquare f (p.1,p.2+z.2)) (zeroSquare f p)
    _ = (∫ p, R p)+(∫ p, C p) := by
      rw [integral_add (hR.comp_add_right (0,z.2)) hC,integral_add_right_eq_self]
    _ ≤ _ := by
      have hr := row_translation_bound f hf α z.1 hE
      have hc := col_translation_bound f hf α z.2 hE
      change (∫ p : Point, |zeroSquare f (p.1+z.1,p.2)-zeroSquare f p|)+
        (∫ p : Point, |zeroSquare f (p.1,p.2+z.2)-zeroSquare f p|) ≤ _
      linarith

end Q4.Candidate.SquareTranslation

#print axioms Q4.Candidate.SquareTranslation.zeroSquare_integrable
#print axioms Q4.Candidate.SquareTranslation.row_slice_translation
#print axioms Q4.Candidate.SquareTranslation.col_slice_translation
#print axioms Q4.Candidate.SquareTranslation.row_translation_bound
#print axioms Q4.Candidate.SquareTranslation.col_translation_bound

#print axioms Q4.Candidate.SquareTranslation.translation_bound
