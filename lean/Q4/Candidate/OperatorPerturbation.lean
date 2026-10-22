import Q4.Candidate.EnergyLipschitz

/-! L1 perturbation of the actual row-minus-column comparison operator.
No operator contraction is assumed: the kernel bound, Fubini, and the
Boolean difference bound give all constants below. -/

open MeasureTheory

namespace Q4.Candidate.OperatorPerturbation
open Q4.Candidate.ComparisonEnergy Q4.Candidate.AlternationKernel
open Q4.Candidate.EnergyLipschitz

theorem transform_difference_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → Bool) (hf : Measurable f) (hg : Measurable g) (x : ℝ) :
    |transform μ f x-transform μ g x| ≤ ∫ y, |spin (f y)-spin (g y)| ∂μ := by
  have hi (f : ℝ → Bool) (hf : Measurable f) : Integrable (kernel f x) μ :=
    bounded_integrable _ _ ((kernel_measurable f hf).comp (measurable_const.prodMk measurable_id))
      (fun y => le_of_eq (kernel_norm f x y))
  unfold transform
  rw [←integral_sub (hi f hf) (hi g hg)]
  calc
    _ ≤ ∫ y, |kernel f x y-kernel g x y| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := μ) (fun y => kernel f x y-kernel g x y)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [kernel,kernel,←mul_sub,abs_mul]
      have hc : |AlternationKernel.cmp x y| = 1 := cmp_norm x y
      rw [hc,one_mul]

theorem row_difference_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) (p : Point) :
    |rowOp μ f p-rowOp μ g p| ≤ ∫ s, pointDistance f g (s,p.2) ∂μ :=
  transform_difference_le μ _ _ (hf.comp (measurable_id.prodMk measurable_const))
    (hg.comp (measurable_id.prodMk measurable_const)) p.1

theorem col_difference_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) (p : Point) :
    |colOp μ f p-colOp μ g p| ≤ ∫ t, pointDistance f g (p.1,t) ∂μ :=
  transform_difference_le μ _ _ (hf.comp (measurable_const.prodMk measurable_id))
    (hg.comp (measurable_const.prodMk measurable_id)) p.2

theorem bounded_difference_square (a b : ℝ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    (a-b)^2 ≤ 2*|a-b| := by
  have h : |a-b| ≤ 2 := by
    calc |a-b| ≤ |a|+|b| := abs_sub _ _
         _ ≤ 2 := by
           rw [Real.norm_eq_abs] at ha hb
           linarith
  nlinarith [abs_nonneg (a-b),sq_abs (a-b)]

theorem squared_difference_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : Point → ℝ) (ha : Measurable a) (hb : Measurable b)
    (ha1 : ∀ p, ‖a p‖ ≤ 1) (hb1 : ∀ p, ‖b p‖ ≤ 1) :
    Integrable (fun p => (a p-b p)^2) (μ.prod μ) := by
  apply Integrable.of_bound ((ha.sub hb).pow_const 2).aestronglyMeasurable 4
  filter_upwards [] with p
  dsimp only [Pi.sub_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hs := bounded_difference_square (a p) (b p) (ha1 p) (hb1 p)
  have hab := norm_sub_le (a p) (b p)
  simp only [Real.norm_eq_abs] at hab
  have h1 := ha1 p
  have h2 := hb1 p
  simp only [Real.norm_eq_abs] at h1 h2
  linarith

theorem row_square_perturbation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) :
    (∫ p, (rowOp μ f p-rowOp μ g p)^2 ∂μ.prod μ) ≤ 2*distance μ f g := by
  have hd := pointDistance_integrable μ f g hf hg
  have hi : Integrable (fun p : Point => ∫ s, pointDistance f g (s,p.2) ∂μ) (μ.prod μ) :=
    hd.integral_prod_right.comp_snd μ
  calc
    _ ≤ ∫ p : Point, 2*(∫ s, pointDistance f g (s,p.2) ∂μ) ∂μ.prod μ := by
      apply integral_mono
        (squared_difference_integrable μ _ _ (rowOp_measurable μ f hf) (rowOp_measurable μ g hg)
          (rowOp_norm_le μ f) (rowOp_norm_le μ g)) (hi.const_mul 2)
      intro p
      exact (bounded_difference_square _ _ (rowOp_norm_le μ f p) (rowOp_norm_le μ g p)).trans
        (mul_le_mul_of_nonneg_left (row_difference_le μ f g hf hg p) (by norm_num))
    _ = 2*distance μ f g := by
      rw [integral_const_mul,integral_fun_snd (fun v => ∫ s, pointDistance f g (s,v) ∂μ)]
      simp only [probReal_univ,one_smul]
      rw [←integral_prod_symm _ hd]
      rfl

theorem col_square_perturbation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) :
    (∫ p, (colOp μ f p-colOp μ g p)^2 ∂μ.prod μ) ≤ 2*distance μ f g := by
  have hd := pointDistance_integrable μ f g hf hg
  have hi : Integrable (fun p : Point => ∫ t, pointDistance f g (p.1,t) ∂μ) (μ.prod μ) :=
    hd.integral_prod_left.comp_fst μ
  calc
    _ ≤ ∫ p : Point, 2*(∫ t, pointDistance f g (p.1,t) ∂μ) ∂μ.prod μ := by
      apply integral_mono
        (squared_difference_integrable μ _ _ (colOp_measurable μ f hf) (colOp_measurable μ g hg)
          (colOp_norm_le μ f) (colOp_norm_le μ g)) (hi.const_mul 2)
      intro p
      exact (bounded_difference_square _ _ (colOp_norm_le μ f p) (colOp_norm_le μ g p)).trans
        (mul_le_mul_of_nonneg_left (col_difference_le μ f g hf hg p) (by norm_num))
    _ = 2*distance μ f g := by
      rw [integral_const_mul,integral_fun_fst (fun u => ∫ t, pointDistance f g (u,t) ∂μ)]
      simp only [probReal_univ,one_smul]
      rw [←integral_prod _ hd]
      rfl

theorem differenceSq_perturbation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) :
    differenceSq μ g ≤ 2*differenceSq μ f+16*distance μ f g := by
  have hD := squared_difference_integrable μ _ _ (rowOp_measurable μ f hf) (colOp_measurable μ f hf)
    (rowOp_norm_le μ f) (colOp_norm_le μ f)
  have hR := squared_difference_integrable μ _ _ (rowOp_measurable μ f hf) (rowOp_measurable μ g hg)
    (rowOp_norm_le μ f) (rowOp_norm_le μ g)
  have hC := squared_difference_integrable μ _ _ (colOp_measurable μ f hf) (colOp_measurable μ g hg)
    (colOp_norm_le μ f) (colOp_norm_le μ g)
  have hRC : Integrable (fun p => (rowOp μ f p-rowOp μ g p)^2+
      (colOp μ f p-colOp μ g p)^2) (μ.prod μ) := hR.add hC
  calc
    _ ≤ ∫ p, 2*(rowOp μ f p-colOp μ f p)^2 +
        4*((rowOp μ f p-rowOp μ g p)^2+(colOp μ f p-colOp μ g p)^2) ∂μ.prod μ := by
      apply integral_mono
        (squared_difference_integrable μ _ _ (rowOp_measurable μ g hg) (colOp_measurable μ g hg)
          (rowOp_norm_le μ g) (colOp_norm_le μ g))
        ((hD.const_mul 2).add (hRC.const_mul 4))
      intro p
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg (2*(rowOp μ f p-colOp μ f p) - (rowOp μ g p-colOp μ g p)),
        sq_nonneg ((rowOp μ f p-rowOp μ g p)+(colOp μ f p-colOp μ g p))]
    _ = 2*differenceSq μ f + 4*((∫ p, (rowOp μ f p-rowOp μ g p)^2 ∂μ.prod μ) +
        (∫ p, (colOp μ f p-colOp μ g p)^2 ∂μ.prod μ)) := by
      rw [integral_add (hD.const_mul 2) (hRC.const_mul 4),integral_const_mul,
        integral_const_mul,integral_add hR hC]
      rfl
    _ ≤ _ := by linarith [row_square_perturbation μ f g hf hg,col_square_perturbation μ f g hf hg]

theorem near_optimal_perturbation (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) (α : ℝ)
    (hE : energy μ f ≤ 1/12+α) :
    differenceSq μ g ≤ 32*α+16*distance μ f g := by
  have hd := (deficit_bounds μ f hf α hE).2.1
  linarith [differenceSq_perturbation μ f g hf hg]

end Q4.Candidate.OperatorPerturbation

#print axioms Q4.Candidate.OperatorPerturbation.transform_difference_le
#print axioms Q4.Candidate.OperatorPerturbation.row_square_perturbation
#print axioms Q4.Candidate.OperatorPerturbation.col_square_perturbation
#print axioms Q4.Candidate.OperatorPerturbation.differenceSq_perturbation
#print axioms Q4.Candidate.OperatorPerturbation.near_optimal_perturbation
