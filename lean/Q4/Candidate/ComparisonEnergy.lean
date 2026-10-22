import Q4.Candidate.AlternationKernel

/-!
The actual comparison-kernel energy and its two-dimensional deficit identity.
All energies and operators are defined by integrals, not by the identity being
proved. The base measure is an atomless probability measure on the real line.
-/
open MeasureTheory MeasureTheory.Measure Set

namespace Q4.Candidate.ComparisonEnergy

open Q4.Candidate.AlternationKernel

abbrev Point := ℝ × ℝ
abbrev Quad := Point × Point

noncomputable def energyIndicator (f : Point → Bool) (q : Quad) : ℝ :=
  if q.1.1 < q.2.1 ∧ q.1.2 < q.2.2 ∧ f q.1 = f q.2 then 1 else 0
noncomputable def energy (μ : Measure ℝ) (f : Point → Bool) : ℝ :=
  ∫ q, energyIndicator f q ∂(μ.prod μ).prod (μ.prod μ)
noncomputable def mean (μ : Measure ℝ) (f : Point → Bool) : ℝ :=
  ∫ p, spin (f p) ∂μ.prod μ
noncomputable def rowOp (μ : Measure ℝ) (f : Point → Bool) (p : Point) : ℝ :=
  ∫ s, AlternationKernel.cmp p.1 s * spin (f (s,p.2)) ∂μ
noncomputable def colOp (μ : Measure ℝ) (f : Point → Bool) (p : Point) : ℝ :=
  ∫ t, AlternationKernel.cmp p.2 t * spin (f (p.1,t)) ∂μ
noncomputable def inner (μ : Measure ℝ) (f : Point → Bool) : ℝ :=
  ∫ p, rowOp μ f p * colOp μ f p ∂μ.prod μ
noncomputable def pairProduct (f : Point → Bool) (q : Quad) : ℝ :=
  spin (f q.1) * spin (f q.2)
noncomputable def orientationProduct (q : Quad) : ℝ :=
  AlternationKernel.cmp q.1.1 q.2.1 * AlternationKernel.cmp q.1.2 q.2.2
noncomputable def crossKernel (f : Point → Bool) (q : Quad) : ℝ :=
  (AlternationKernel.cmp q.1.1 q.2.1 * spin (f (q.2.1,q.1.2))) *
  (AlternationKernel.cmp q.1.2 q.2.2 * spin (f (q.1.1,q.2.2)))

/-- Swap the first coordinates while leaving the second coordinates in place. -/
def rowSwap : Quad ≃ᵐ Quad :=
  MeasurableEquiv.prodAssoc.symm.trans
    (((MeasurableEquiv.prodAssoc.trans AlternationKernel.reverse).trans
      MeasurableEquiv.prodAssoc.symm).prodCongr (MeasurableEquiv.refl ℝ) |>.trans
      MeasurableEquiv.prodAssoc)

@[simp] theorem rowSwap_apply (q : Quad) :
    rowSwap q = ((q.2.1,q.1.2),(q.1.1,q.2.2)) := rfl

theorem rowSwap_preserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving rowSwap ((μ.prod μ).prod (μ.prod μ)) ((μ.prod μ).prod (μ.prod μ)) := by
  have h3 := (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ μ μ)).comp
      ((reverse_preserving μ).comp (measurePreserving_prodAssoc μ μ μ))
  exact (measurePreserving_prodAssoc (μ.prod μ) μ μ).comp
    ((h3.prod (MeasurePreserving.id μ)).comp
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (measurePreserving_prodAssoc (μ.prod μ) μ μ)))

theorem cmp_measurable : Measurable (fun p : Point => AlternationKernel.cmp p.1 p.2) := by
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
    measurable_const measurable_const

theorem energyIndicator_measurable (f : Point → Bool) (hf : Measurable f) :
    Measurable (energyIndicator f) := by
  exact Measurable.ite
    ((measurableSet_lt measurable_fst.fst measurable_snd.fst).inter
      ((measurableSet_lt measurable_fst.snd measurable_snd.snd).inter
        (measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd))))
    measurable_const measurable_const

theorem pairProduct_measurable (f : Point → Bool) (hf : Measurable f) :
    Measurable (pairProduct f) :=
  (measurable_spin_comp _ (hf.comp measurable_fst)).mul
    (measurable_spin_comp _ (hf.comp measurable_snd))
theorem orientationProduct_measurable : Measurable orientationProduct :=
  (cmp_measurable.comp (measurable_fst.fst.prodMk measurable_snd.fst)).mul
    (cmp_measurable.comp (measurable_fst.snd.prodMk measurable_snd.snd))
theorem crossKernel_measurable (f : Point → Bool) (hf : Measurable f) :
    Measurable (crossKernel f) :=
  ((cmp_measurable.comp (measurable_fst.fst.prodMk measurable_snd.fst)).mul
    (measurable_spin_comp _ (hf.comp (measurable_snd.fst.prodMk measurable_fst.snd)))).mul
  ((cmp_measurable.comp (measurable_fst.snd.prodMk measurable_snd.snd)).mul
    (measurable_spin_comp _ (hf.comp (measurable_fst.fst.prodMk measurable_snd.snd))))

theorem energyIndicator_norm_le (f : Point → Bool) (q : Quad) :
    ‖energyIndicator f q‖ ≤ 1 := by unfold energyIndicator; split <;> norm_num
theorem pairProduct_norm (f : Point → Bool) (q : Quad) : ‖pairProduct f q‖ = 1 := by
  simp only [pairProduct,norm_mul,spin_norm,mul_one]
theorem orientationProduct_norm (q : Quad) : ‖orientationProduct q‖ = 1 := by
  simp only [orientationProduct,norm_mul,cmp_norm,mul_one]
theorem crossKernel_norm (f : Point → Bool) (q : Quad) : ‖crossKernel f q‖ = 1 := by
  simp only [crossKernel,norm_mul,cmp_norm,spin_norm,mul_one]

theorem bounded_integrable {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (g : α → ℝ) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ 1) : Integrable g ν :=
  Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)

theorem energyIndicator_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    Integrable (energyIndicator f) ((μ.prod μ).prod (μ.prod μ)) :=
  bounded_integrable _ _ (energyIndicator_measurable f hf) (energyIndicator_norm_le f)
theorem pairProduct_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    Integrable (pairProduct f) ((μ.prod μ).prod (μ.prod μ)) :=
  bounded_integrable _ _ (pairProduct_measurable f hf) (fun q => le_of_eq (pairProduct_norm f q))
theorem orientationProduct_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable orientationProduct ((μ.prod μ).prod (μ.prod μ)) :=
  bounded_integrable _ _ orientationProduct_measurable (fun q => le_of_eq (orientationProduct_norm q))
theorem crossKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    Integrable (crossKernel f) ((μ.prod μ).prod (μ.prod μ)) :=
  bounded_integrable _ _ (crossKernel_measurable f hf) (fun q => le_of_eq (crossKernel_norm f q))
theorem weightedProduct_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    Integrable (fun q => orientationProduct q * pairProduct f q) ((μ.prod μ).prod (μ.prod μ)) :=
  bounded_integrable _ _ (orientationProduct_measurable.mul (pairProduct_measurable f hf))
    (fun q => by simp only [norm_mul,orientationProduct_norm,pairProduct_norm,mul_one,le_refl])

/-- The two opposite ordered comparison events are genuine event indicators. -/
theorem pointwise_energy (f : Point → Bool) (q : Quad)
    (hu : q.1.1 ≠ q.2.1) (hv : q.1.2 ≠ q.2.2) :
    4 * (energyIndicator f q + energyIndicator f q.swap) =
      1 + pairProduct f q + orientationProduct q +
        orientationProduct q * pairProduct f q := by
  rcases lt_or_gt_of_ne hu with hu | hu <;>
    rcases lt_or_gt_of_ne hv with hv | hv
  all_goals
    have hun := not_lt_of_ge (le_of_lt hu)
    have hvn := not_lt_of_ge (le_of_lt hv)
    cases h1 : f q.1 <;> cases h2 : f q.2 <;>
      norm_num [energyIndicator,pairProduct,orientationProduct,AlternationKernel.cmp,spin,hu,hv,hun,hvn,h1,h2]

theorem cmp_reverse (a b : ℝ) (hab : a ≠ b) : AlternationKernel.cmp b a = -AlternationKernel.cmp a b := by
  rcases lt_or_gt_of_ne hab with h | h <;>
    simp [AlternationKernel.cmp,h,not_lt_of_ge (le_of_lt h)]

theorem orientationProduct_rowSwap (q : Quad) (hu : q.1.1 ≠ q.2.1) :
    orientationProduct (rowSwap q) = -orientationProduct q := by
  simp only [orientationProduct,rowSwap_apply,cmp_reverse _ _ hu]
  ring

theorem weighted_rowSwap (f : Point → Bool) (q : Quad) (hu : q.1.1 ≠ q.2.1) :
    orientationProduct (rowSwap q) * pairProduct f (rowSwap q) = -crossKernel f q := by
  simp only [orientationProduct,pairProduct,rowSwap_apply,cmp_reverse _ _ hu,crossKernel]
  ring

/-- Distinctness in both coordinate directions holds outside an actual null set. -/
theorem ae_coordinate_distinct (μ : Measure ℝ) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ q : Quad ∂(μ.prod μ).prod (μ.prod μ), q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 := by
  apply (ae_prod_iff_ae_ae
    ((measurableSet_eq_fun measurable_fst.fst measurable_snd.fst).compl.inter
      (measurableSet_eq_fun measurable_fst.snd measurable_snd.snd).compl)).2
  filter_upwards [] with p
  change ∀ᵐ y : Point ∂μ.prod μ, p.1 ≠ y.1 ∧ p.2 ≠ y.2
  apply (ae_prod_iff_ae_ae
    ((measurableSet_eq_fun measurable_const measurable_fst).compl.inter
      (measurableSet_eq_fun measurable_const measurable_snd).compl)).2
  filter_upwards [ae_ne μ p.1] with s hs
  filter_upwards [ae_ne μ p.2] with t ht
  exact ⟨Ne.symm hs,Ne.symm ht⟩

/-- Fubini expands the actual row/column operator inner product. -/
theorem inner_eq_cross_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    inner μ f = ∫ q, crossKernel f q ∂(μ.prod μ).prod (μ.prod μ) := by
  rw [integral_prod _ (crossKernel_integrable μ f hf)]
  apply integral_congr_ae
  filter_upwards [] with p
  exact (integral_prod_mul
    (fun s => AlternationKernel.cmp p.1 s * spin (f (s,p.2)))
    (fun t => AlternationKernel.cmp p.2 t * spin (f (p.1,t)))).symm

theorem integral_pairProduct (μ : Measure ℝ) [SFinite μ] (f : Point → Bool) :
    (∫ q, pairProduct f q ∂(μ.prod μ).prod (μ.prod μ)) = (mean μ f)^2 := by
  have he := integral_prod_mul (μ := μ.prod μ) (ν := μ.prod μ)
    (fun p => spin (f p)) (fun p => spin (f p))
  change (∫ q, spin (f q.1) * spin (f q.2) ∂(μ.prod μ).prod (μ.prod μ)) = (mean μ f)^2
  rw [he]
  change mean μ f * mean μ f = (mean μ f)^2
  ring

theorem integral_orientationProduct (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    (∫ q, orientationProduct q ∂(μ.prod μ).prod (μ.prod μ)) = 0 := by
  have he : (∫ q, orientationProduct q ∂(μ.prod μ).prod (μ.prod μ)) =
      ∫ q, -orientationProduct q ∂(μ.prod μ).prod (μ.prod μ) := by
    calc
      _ = ∫ q, orientationProduct (rowSwap q) ∂(μ.prod μ).prod (μ.prod μ) :=
        ((rowSwap_preserving μ).integral_comp' orientationProduct).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_coordinate_distinct μ] with q hq
        exact orientationProduct_rowSwap q hq.1
  rw [integral_neg] at he
  linarith

theorem integral_weightedProduct (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (f : Point → Bool) (hf : Measurable f) :
    (∫ q, orientationProduct q * pairProduct f q ∂(μ.prod μ).prod (μ.prod μ)) =
      -inner μ f := by
  calc
    _ = ∫ q, orientationProduct (rowSwap q) * pairProduct f (rowSwap q)
        ∂(μ.prod μ).prod (μ.prod μ) :=
      ((rowSwap_preserving μ).integral_comp' (fun q => orientationProduct q * pairProduct f q)).symm
    _ = ∫ q, -crossKernel f q ∂(μ.prod μ).prod (μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [ae_coordinate_distinct μ] with q hq
      exact weighted_rowSwap f q hq.1
    _ = -inner μ f := by rw [integral_neg,←inner_eq_cross_integral μ f hf]

/-- Equation (2.4), with the actual ordered comparison energy on the left. -/
theorem energy_identity (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (f : Point → Bool) (hf : Measurable f) :
    energy μ f = (1 + (mean μ f)^2 - inner μ f) / 8 := by
  have hE := energyIndicator_integrable μ f hf
  have hEs : Integrable (fun q : Quad => energyIndicator f q.swap)
      ((μ.prod μ).prod (μ.prod μ)) := hE.swap
  have hP := pairProduct_integrable μ f hf
  have hO := orientationProduct_integrable μ
  have hOP := weightedProduct_integrable μ f hf
  have h1P : Integrable (fun q => 1 + pairProduct f q)
      ((μ.prod μ).prod (μ.prod μ)) := (integrable_const 1).add hP
  have h1PO : Integrable (fun q => 1 + pairProduct f q + orientationProduct q)
      ((μ.prod μ).prod (μ.prod μ)) := h1P.add hO
  have he : (∫ q, 4 * (energyIndicator f q + energyIndicator f q.swap)
      ∂(μ.prod μ).prod (μ.prod μ)) =
      ∫ q, 1 + pairProduct f q + orientationProduct q + orientationProduct q * pairProduct f q
      ∂(μ.prod μ).prod (μ.prod μ) := by
    apply integral_congr_ae
    filter_upwards [ae_coordinate_distinct μ] with q hq
    exact pointwise_energy f q hq.1 hq.2
  rw [integral_const_mul,integral_add hE hEs,integral_prod_swap,
    integral_add h1PO hOP,integral_add h1P hO,
    integral_add (integrable_const 1) hP,
    integral_pairProduct,integral_orientationProduct,integral_weightedProduct μ f hf] at he
  have hc : (∫ _q : Quad, (1 : ℝ) ∂(μ.prod μ).prod (μ.prod μ)) = 1 := by simp
  rw [hc,add_zero] at he
  change 4 * (energy μ f + energy μ f) = 1 + (mean μ f)^2 + -inner μ f at he
  linarith

noncomputable def rowNormSq (μ : Measure ℝ) (f : Point → Bool) : ℝ :=
  ∫ p, (rowOp μ f p)^2 ∂μ.prod μ
noncomputable def colNormSq (μ : Measure ℝ) (f : Point → Bool) : ℝ :=
  ∫ p, (colOp μ f p)^2 ∂μ.prod μ
noncomputable def differenceSq (μ : Measure ℝ) (f : Point → Bool) : ℝ :=
  ∫ p, (rowOp μ f p - colOp μ f p)^2 ∂μ.prod μ

theorem rowOp_measurable (μ : Measure ℝ) [SFinite μ]
    (f : Point → Bool) (hf : Measurable f) : Measurable (rowOp μ f) := by
  have hk : Measurable (fun q : Point × ℝ =>
      AlternationKernel.cmp q.1.1 q.2 * spin (f (q.2,q.1.2))) :=
    (cmp_measurable.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (measurable_spin_comp _ (hf.comp (measurable_snd.prodMk measurable_fst.snd)))
  exact hk.stronglyMeasurable.integral_prod_right'.measurable

theorem colOp_measurable (μ : Measure ℝ) [SFinite μ]
    (f : Point → Bool) (hf : Measurable f) : Measurable (colOp μ f) := by
  have hk : Measurable (fun q : Point × ℝ =>
      AlternationKernel.cmp q.1.2 q.2 * spin (f (q.1.1,q.2))) :=
    (cmp_measurable.comp (measurable_fst.snd.prodMk measurable_snd)).mul
      (measurable_spin_comp _ (hf.comp (measurable_fst.fst.prodMk measurable_snd)))
  exact hk.stronglyMeasurable.integral_prod_right'.measurable

theorem rowOp_norm_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : Point → Bool) (p : Point) : ‖rowOp μ f p‖ ≤ 1 := by
  apply le_trans (norm_integral_le_of_norm_le_const (C := 1) ?_) (by simp)
  filter_upwards [] with s
  simp only [norm_mul,cmp_norm,spin_norm,mul_one,le_refl]

theorem colOp_norm_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : Point → Bool) (p : Point) : ‖colOp μ f p‖ ≤ 1 := by
  apply le_trans (norm_integral_le_of_norm_le_const (C := 1) ?_) (by simp)
  filter_upwards [] with t
  simp only [norm_mul,cmp_norm,spin_norm,mul_one,le_refl]

theorem rowSq_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    Integrable (fun p => (rowOp μ f p)^2) (μ.prod μ) := by
  apply bounded_integrable _ _ ((rowOp_measurable μ f hf).pow_const 2)
  intro p
  rw [norm_pow]
  have h := rowOp_norm_le μ f p
  have hn := norm_nonneg (rowOp μ f p)
  nlinarith

theorem colSq_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    Integrable (fun p => (colOp μ f p)^2) (μ.prod μ) := by
  apply bounded_integrable _ _ ((colOp_measurable μ f hf).pow_const 2)
  intro p
  rw [norm_pow]
  have h := colOp_norm_le μ f p
  have hn := norm_nonneg (colOp μ f p)
  nlinarith

theorem inner_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    Integrable (fun p => rowOp μ f p * colOp μ f p) (μ.prod μ) := by
  apply bounded_integrable _ _ ((rowOp_measurable μ f hf).mul (colOp_measurable μ f hf))
  intro p
  change ‖rowOp μ f p * colOp μ f p‖ ≤ 1
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖colOp μ f p‖ := mul_le_mul_of_nonneg_right (rowOp_norm_le μ f p) (norm_nonneg _)
    _ ≤ 1 := by simpa using colOp_norm_le μ f p

/-- Exact Hilbert-space polarization, proved for the actual squared integrals. -/
theorem difference_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : Point → Bool) (hf : Measurable f) :
    differenceSq μ f = rowNormSq μ f + colNormSq μ f - 2 * inner μ f := by
  have hR := rowSq_integrable μ f hf
  have hC := colSq_integrable μ f hf
  have hI := inner_integrable μ f hf
  have hRC : Integrable (fun p => (rowOp μ f p)^2 + (colOp μ f p)^2) (μ.prod μ) := hR.add hC
  calc
    _ = ∫ p, (rowOp μ f p)^2 + (colOp μ f p)^2 -
        2 * (rowOp μ f p * colOp μ f p) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      ring
    _ = rowNormSq μ f + colNormSq μ f - 2 * inner μ f := by
      rw [integral_sub hRC (hI.const_mul 2),integral_add hR hC,integral_const_mul]
      rfl

/-- The full exact nonnegative-deficit decomposition from candidate §2.4. -/
theorem deficit_identity (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (f : Point → Bool) (hf : Measurable f) :
    8 * (energy μ f - 1 / 12) = (mean μ f)^2 + differenceSq μ f / 2 +
      (1 / 3 - rowNormSq μ f) / 2 + (1 / 3 - colNormSq μ f) / 2 := by
  rw [energy_identity μ f hf,difference_identity μ f hf]
  ring

theorem rowNormSq_le_third (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (f : Point → Bool) (hf : Measurable f) : rowNormSq μ f ≤ 1 / 3 := by
  have hR := rowSq_integrable μ f hf
  unfold rowNormSq
  rw [integral_prod_symm _ hR]
  have hpoint (v : ℝ) : (∫ u, (rowOp μ f (u,v))^2 ∂μ) ≤ 1 / 3 := by
    change AlternationKernel.normSq μ (fun u => f (u,v)) ≤ 1 / 3
    rw [kernel_identity μ (fun u => f (u,v)) (hf.comp (measurable_id.prodMk measurable_const))]
    have hn : 0 ≤ Q4.Candidate.AlternatingTriples.tripleMass μ (fun u => f (u,v)) :=
      measureReal_nonneg
    linarith
  calc
    _ ≤ ∫ _v : ℝ, (1 / 3 : ℝ) ∂μ :=
      integral_mono hR.integral_prod_right (integrable_const _) hpoint
    _ = 1 / 3 := by simp

theorem colNormSq_le_third (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (f : Point → Bool) (hf : Measurable f) : colNormSq μ f ≤ 1 / 3 := by
  have hC := colSq_integrable μ f hf
  unfold colNormSq
  rw [integral_prod _ hC]
  have hpoint (u : ℝ) : (∫ v, (colOp μ f (u,v))^2 ∂μ) ≤ 1 / 3 := by
    change AlternationKernel.normSq μ (fun v => f (u,v)) ≤ 1 / 3
    rw [kernel_identity μ (fun v => f (u,v)) (hf.comp (measurable_const.prodMk measurable_id))]
    have hn : 0 ≤ Q4.Candidate.AlternatingTriples.tripleMass μ (fun v => f (u,v)) :=
      measureReal_nonneg
    linarith
  calc
    _ ≤ ∫ _u : ℝ, (1 / 3 : ℝ) ∂μ :=
      integral_mono hC.integral_prod_left (integrable_const _) hpoint
    _ = 1 / 3 := by simp

/-- The exact sharp lower bound follows, without a stability assumption. -/
theorem energy_ge_twelfth (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (f : Point → Bool) (hf : Measurable f) : 1 / 12 ≤ energy μ f := by
  have he := deficit_identity μ f hf
  have hR := rowNormSq_le_third μ f hf
  have hC := colNormSq_le_third μ f hf
  have hD : 0 ≤ differenceSq μ f := integral_nonneg (fun p => sq_nonneg _)
  nlinarith [sq_nonneg (mean μ f)]

/-- Each nonnegative term of the exact deficit identity is controlled by
an actual energy excess. These are the quantitative inputs to smoothing. -/
theorem deficit_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (f : Point → Bool) (hf : Measurable f) (α : ℝ)
    (hE : energy μ f ≤ 1 / 12 + α) :
    (mean μ f)^2 ≤ 8 * α ∧ differenceSq μ f ≤ 16 * α ∧
      1 / 3 - rowNormSq μ f ≤ 16 * α ∧ 1 / 3 - colNormSq μ f ≤ 16 * α := by
  have he := deficit_identity μ f hf
  have hR := rowNormSq_le_third μ f hf
  have hC := colNormSq_le_third μ f hf
  have hD : 0 ≤ differenceSq μ f := integral_nonneg (fun p => sq_nonneg _)
  have hM := sq_nonneg (mean μ f)
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end Q4.Candidate.ComparisonEnergy

#print axioms Q4.Candidate.ComparisonEnergy.inner_eq_cross_integral
#print axioms Q4.Candidate.ComparisonEnergy.energy_identity

#print axioms Q4.Candidate.ComparisonEnergy.difference_identity
#print axioms Q4.Candidate.ComparisonEnergy.deficit_identity
#print axioms Q4.Candidate.ComparisonEnergy.rowNormSq_le_third
#print axioms Q4.Candidate.ComparisonEnergy.colNormSq_le_third
#print axioms Q4.Candidate.ComparisonEnergy.energy_ge_twelfth

#print axioms Q4.Candidate.ComparisonEnergy.deficit_bounds
