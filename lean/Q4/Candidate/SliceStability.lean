import Q4.Candidate.ComparisonEnergy
import Q4.Candidate.OneDimensionalStability
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Actual slice deficits and a measurable threshold-error envelope. The theorem
chooses a threshold separately in every slice, without assuming a measurable
selection of threshold locations. The envelope itself is measurable and its
integral has the manuscript's quantitative bound.
-/
open MeasureTheory MeasureTheory.Measure Set

namespace Q4.Candidate.SliceStability
open Q4.Candidate.UnitIntervalMeasure
open Q4.Candidate.AlternationKernel
open Q4.Candidate.ComparisonEnergy
open Q4.Candidate.OneDimensionalStability

noncomputable def rowDeficit (f : Point → Bool) (v : ℝ) : ℝ :=
  deficit (fun u => f (u,v))
noncomputable def colDeficit (f : Point → Bool) (u : ℝ) : ℝ :=
  deficit (fun v => f (u,v))
noncomputable def rowEnvelope (f : Point → Bool) (v : ℝ) : ℝ :=
  4 * (rowDeficit f v)^(1/3 : ℝ)
noncomputable def colEnvelope (f : Point → Bool) (u : ℝ) : ℝ :=
  4 * (colDeficit f u)^(1/3 : ℝ)

theorem rowDeficit_measurable (f : Point → Bool) (hf : Measurable f) :
    Measurable (rowDeficit f) := by
  change Measurable (fun v => (1/3 : ℝ) - ∫ u, (rowOp unit f (u,v))^2 ∂unit)
  exact measurable_const.sub
    (((rowOp_measurable unit f hf).pow_const 2).stronglyMeasurable.integral_prod_left'.measurable)
theorem colDeficit_measurable (f : Point → Bool) (hf : Measurable f) :
    Measurable (colDeficit f) := by
  change Measurable (fun u => (1/3 : ℝ) - ∫ v, (colOp unit f (u,v))^2 ∂unit)
  exact measurable_const.sub
    (((colOp_measurable unit f hf).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)

theorem rowDeficit_integrable (f : Point → Bool) (hf : Measurable f) :
    Integrable (rowDeficit f) unit :=
  (integrable_const (1/3 : ℝ)).sub (rowSq_integrable unit f hf).integral_prod_right
theorem colDeficit_integrable (f : Point → Bool) (hf : Measurable f) :
    Integrable (colDeficit f) unit :=
  (integrable_const (1/3 : ℝ)).sub (colSq_integrable unit f hf).integral_prod_left

theorem rowDeficit_bounds (f : Point → Bool) (hf : Measurable f) (v : ℝ) :
    0 ≤ rowDeficit f v ∧ rowDeficit f v ≤ 1/3 := by
  refine ⟨deficit_nonneg _ (hf.comp (measurable_id.prodMk measurable_const)),?_⟩
  have hn : 0 ≤ normSq unit (fun u => f (u,v)) := integral_nonneg (fun u => sq_nonneg _)
  dsimp [rowDeficit,deficit]
  linarith
theorem colDeficit_bounds (f : Point → Bool) (hf : Measurable f) (u : ℝ) :
    0 ≤ colDeficit f u ∧ colDeficit f u ≤ 1/3 := by
  refine ⟨deficit_nonneg _ (hf.comp (measurable_const.prodMk measurable_id)),?_⟩
  have hn : 0 ≤ normSq unit (fun v => f (u,v)) := integral_nonneg (fun v => sq_nonneg _)
  dsimp [colDeficit,deficit]
  linarith

/-- Fubini identifies the actual average row deficit with the 2D norm deficit. -/
theorem integral_rowDeficit (f : Point → Bool) (hf : Measurable f) :
    (∫ v, rowDeficit f v ∂unit) = 1/3 - rowNormSq unit f := by
  change (∫ v, (1/3 : ℝ) - ∫ u, (rowOp unit f (u,v))^2 ∂unit ∂unit) = _
  rw [integral_sub (integrable_const _) (rowSq_integrable unit f hf).integral_prod_right,
    ←integral_prod_symm _ (rowSq_integrable unit f hf)]
  simp [rowNormSq]
theorem integral_colDeficit (f : Point → Bool) (hf : Measurable f) :
    (∫ u, colDeficit f u ∂unit) = 1/3 - colNormSq unit f := by
  change (∫ u, (1/3 : ℝ) - ∫ v, (colOp unit f (u,v))^2 ∂unit ∂unit) = _
  rw [integral_sub (integrable_const _) (colSq_integrable unit f hf).integral_prod_left,
    ←integral_prod _ (colSq_integrable unit f hf)]
  simp [colNormSq]

/-- Cubic Jensen inequality from the nonnegative polynomial
(g-a)²(g+2a), with a the actual average. -/
theorem integral_cube_ge_cube_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → ℝ)
    (hg : Integrable g μ) (hg3 : Integrable (fun x => (g x)^3) μ)
    (hn : ∀ x, 0 ≤ g x) : (∫ x, g x ∂μ)^3 ≤ ∫ x, (g x)^3 ∂μ := by
  let a := ∫ x, g x ∂μ
  have ha : 0 ≤ a := integral_nonneg hn
  have hlin : Integrable (fun x => 3 * a^2 * g x - 2 * a^3) μ :=
    (hg.const_mul (3*a^2)).sub (integrable_const _)
  have hp (x : α) : 3 * a^2 * g x - 2 * a^3 ≤ (g x)^3 := by
    have hpol := mul_nonneg (sq_nonneg (g x-a)) (show 0 ≤ g x+2*a by linarith [hn x])
    nlinarith
  calc
    _ = ∫ x, 3 * a^2 * g x - 2 * a^3 ∂μ := by
      rw [integral_sub (hg.const_mul _) (integrable_const _),integral_const_mul]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      change a^3 = 3*a^2*a-2*a^3
      ring
    _ ≤ _ := integral_mono hlin hg3 hp

/-- A measurable cube-root envelope with average-deficit ≤16α has mean ≤11α^(1/3).
All integrability facts are proved from the stated bounded measurable deficit. -/
theorem average_envelope_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (D : α → ℝ) (hD : Measurable D)
    (hb : ∀ x, 0 ≤ D x ∧ D x ≤ 1) (α₀ : ℝ) (havg : (∫ x, D x ∂μ) ≤ 16 * α₀) :
    Measurable (fun x => 4*(D x)^(1/3 : ℝ)) ∧
      Integrable (fun x => 4*(D x)^(1/3 : ℝ)) μ ∧
      (∫ x, 4*(D x)^(1/3 : ℝ) ∂μ) ≤ 11*α₀^(1/3 : ℝ) := by
  let g : α → ℝ := fun x => (D x)^(1/3 : ℝ)
  have hgm : Measurable g := (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/3)).measurable.comp hD
  have hgn (x : α) : 0 ≤ g x := Real.rpow_nonneg (hb x).1 _
  have hgb (x : α) : g x ≤ 1 := Real.rpow_le_one (hb x).1 (hb x).2 (by norm_num)
  have hgi : Integrable g μ := bounded_integrable μ g hgm (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hgn x)]; exact hgb x)
  have hDi : Integrable D μ := bounded_integrable μ D hD (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]; exact (hb x).2)
  have hpow (x : α) : (g x)^3 = D x := by
    dsimp [g]
    rw [←Real.rpow_mul_natCast (hb x).1 (1/3 : ℝ) 3]
    norm_num
  have hgi3 : Integrable (fun x => (g x)^3) μ :=
    hDi.congr (Filter.Eventually.of_forall (fun x => (hpow x).symm))
  have hj := integral_cube_ge_cube_integral μ g hgi hgi3 hgn
  have hpeq : (∫ x, (g x)^3 ∂μ) = ∫ x, D x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hpow)
  rw [hpeq] at hj
  have hα : 0 ≤ α₀ := by
    have hnD : 0 ≤ ∫ x, D x ∂μ := integral_nonneg (fun x => (hb x).1)
    linarith
  refine ⟨measurable_const.mul hgm,hgi.const_mul 4,?_⟩
  rw [integral_const_mul]
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hα _))
  have hright : (11*α₀^(1/3 : ℝ))^3 = 1331*α₀ := by
    rw [mul_pow,←Real.rpow_mul_natCast hα (1/3 : ℝ) 3]
    norm_num
  rw [hright,mul_pow]
  change 4^3 * (∫ x, g x ∂μ)^3 ≤ 1331*α₀
  nlinarith

noncomputable def thresholdError (h : ℝ → Bool) (o : Bool) (t : ℝ) : ℝ :=
  ∫ x, |Q4.Candidate.ThresholdApproximation.sign {x | h x = true} x -
    Q4.Candidate.ThresholdApproximation.sign (if o then Iic t else Ioi t) x| ∂unit

/-- Every actual row has a genuine attained threshold bounded by its measurable
error envelope. No measurable selection of the thresholds is claimed. -/
theorem row_threshold_exists (f : Point → Bool) (hf : Measurable f) (v : ℝ) :
    ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      thresholdError (fun u => f (u,v)) o t ≤ rowEnvelope f v :=
  (one_dimensional_stability (fun u => f (u,v))
    (hf.comp (measurable_id.prodMk measurable_const))).2

theorem col_threshold_exists (f : Point → Bool) (hf : Measurable f) (u : ℝ) :
    ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      thresholdError (fun v => f (u,v)) o t ≤ colEnvelope f u :=
  (one_dimensional_stability (fun v => f (u,v))
    (hf.comp (measurable_const.prodMk measurable_id))).2

/-- Actual average row-threshold error bound, expressed through a measurable
integrable envelope and pointwise attained threshold witnesses. -/
theorem row_average_stability (f : Point → Bool) (hf : Measurable f) (α : ℝ)
    (hE : energy unit f ≤ 1/12 + α) :
    Measurable (rowEnvelope f) ∧ Integrable (rowEnvelope f) unit ∧
      (∫ v, rowEnvelope f v ∂unit) ≤ 11*α^(1/3 : ℝ) ∧
      ∀ v : ℝ, ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
        thresholdError (fun u => f (u,v)) o t ≤ rowEnvelope f v := by
  have havg : (∫ v, rowDeficit f v ∂unit) ≤ 16*α := by
    rw [integral_rowDeficit f hf]
    exact (deficit_bounds unit f hf α hE).2.2.1
  have hb (v : ℝ) : 0 ≤ rowDeficit f v ∧ rowDeficit f v ≤ 1 :=
    ⟨(rowDeficit_bounds f hf v).1, by linarith [(rowDeficit_bounds f hf v).2]⟩
  obtain ⟨hm,hi,he⟩ := average_envelope_bound unit (rowDeficit f)
    (rowDeficit_measurable f hf) hb α havg
  exact ⟨hm,hi,he,row_threshold_exists f hf⟩

theorem col_average_stability (f : Point → Bool) (hf : Measurable f) (α : ℝ)
    (hE : energy unit f ≤ 1/12 + α) :
    Measurable (colEnvelope f) ∧ Integrable (colEnvelope f) unit ∧
      (∫ u, colEnvelope f u ∂unit) ≤ 11*α^(1/3 : ℝ) ∧
      ∀ u : ℝ, ∃ o : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
        thresholdError (fun v => f (u,v)) o t ≤ colEnvelope f u := by
  have havg : (∫ u, colDeficit f u ∂unit) ≤ 16*α := by
    rw [integral_colDeficit f hf]
    exact (deficit_bounds unit f hf α hE).2.2.2
  have hb (u : ℝ) : 0 ≤ colDeficit f u ∧ colDeficit f u ≤ 1 :=
    ⟨(colDeficit_bounds f hf u).1, by linarith [(colDeficit_bounds f hf u).2]⟩
  obtain ⟨hm,hi,he⟩ := average_envelope_bound unit (colDeficit f)
    (colDeficit_measurable f hf) hb α havg
  exact ⟨hm,hi,he,col_threshold_exists f hf⟩

end Q4.Candidate.SliceStability

#print axioms Q4.Candidate.SliceStability.integral_rowDeficit
#print axioms Q4.Candidate.SliceStability.integral_colDeficit
#print axioms Q4.Candidate.SliceStability.integral_cube_ge_cube_integral
#print axioms Q4.Candidate.SliceStability.average_envelope_bound

#print axioms Q4.Candidate.SliceStability.row_threshold_exists
#print axioms Q4.Candidate.SliceStability.col_threshold_exists
#print axioms Q4.Candidate.SliceStability.row_average_stability
#print axioms Q4.Candidate.SliceStability.col_average_stability
