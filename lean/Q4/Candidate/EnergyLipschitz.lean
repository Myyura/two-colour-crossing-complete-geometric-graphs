import Q4.Candidate.ComparisonEnergy

/-! Actual L1 perturbation of the Boolean comparison energy. The constant
one here is deliberately weaker than (2.6), but is sufficient for the
manuscript's conservative intermediate excess 257h. It is not asserted to
be the sharper weighted version.
-/

open MeasureTheory

namespace Q4.Candidate.EnergyLipschitz

open Q4.Candidate.ComparisonEnergy Q4.Candidate.AlternationKernel

noncomputable def pointDistance (f g : Point → Bool) (p : Point) : ℝ :=
  |spin (f p)-spin (g p)|
noncomputable def distance (μ : Measure ℝ) (f g : Point → Bool) : ℝ :=
  ∫ p, pointDistance f g p ∂μ.prod μ

theorem pointDistance_measurable (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) :
    Measurable (pointDistance f g) := (measurable_spin_comp f hf |>.sub (measurable_spin_comp g hg)).norm

theorem pointDistance_bounds (f g : Point → Bool) (p : Point) :
    0 ≤ pointDistance f g p ∧ pointDistance f g p ≤ 2 := by
  cases hf : f p <;> cases hg : g p <;> norm_num [pointDistance,spin,hf,hg]

theorem pointDistance_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) :
    Integrable (pointDistance f g) (μ.prod μ) := by
  apply Integrable.of_bound (pointDistance_measurable f g hf hg).aestronglyMeasurable 2
  exact ae_of_all _ (fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pointDistance_bounds f g p).1]
    exact (pointDistance_bounds f g p).2)

theorem indicator_difference_bound (f g : Point → Bool) (q : Quad) :
    |energyIndicator f q-energyIndicator g q| ≤
      (pointDistance f g q.1+pointDistance f g q.2)/2 := by
  by_cases hu : q.1.1 < q.2.1 <;> by_cases hv : q.1.2 < q.2.2 <;>
    cases hf1 : f q.1 <;> cases hf2 : f q.2 <;>
    cases hg1 : g q.1 <;> cases hg2 : g q.2 <;>
    norm_num [energyIndicator,pointDistance,spin,hu,hv,hf1,hf2,hg1,hg2]

theorem energy_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) :
    |energy μ f-energy μ g| ≤ distance μ f g := by
  let ν := μ.prod μ
  have hd := pointDistance_integrable μ f g hf hg
  have h1 : Integrable (fun q : Quad => pointDistance f g q.1) (ν.prod ν) := hd.comp_fst ν
  have h2 : Integrable (fun q : Quad => pointDistance f g q.2) (ν.prod ν) := hd.comp_snd ν
  have hsum : Integrable (fun q : Quad => pointDistance f g q.1+pointDistance f g q.2) (ν.prod ν) :=
    h1.add h2
  unfold energy
  rw [←integral_sub (energyIndicator_integrable μ f hf) (energyIndicator_integrable μ g hg)]
  calc
    _ ≤ ∫ q, |energyIndicator f q-energyIndicator g q| ∂ν.prod ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := ν.prod ν) (fun q => energyIndicator f q-energyIndicator g q)
    _ ≤ ∫ q, (pointDistance f g q.1+pointDistance f g q.2)/2 ∂ν.prod ν := by
      apply integral_mono ((energyIndicator_integrable μ f hf).sub (energyIndicator_integrable μ g hg)).abs
        (hsum.div_const 2)
      exact indicator_difference_bound f g
    _ = distance μ f g := by
      rw [integral_div,integral_add h1 h2,integral_fun_fst,integral_fun_snd]
      simp [ν,distance]

theorem mean_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Point → Bool) (hf : Measurable f) (hg : Measurable g) :
    |mean μ f-mean μ g| ≤ distance μ f g := by
  have hi (f : Point → Bool) (hf : Measurable f) : Integrable (fun p => spin (f p)) (μ.prod μ) :=
    bounded_integrable _ _ (measurable_spin_comp f hf) (fun p => le_of_eq (spin_norm (f p)))
  unfold mean
  rw [←integral_sub (hi f hf) (hi g hg)]
  simpa only [Real.norm_eq_abs, distance, pointDistance] using
    norm_integral_le_integral_norm (μ := μ.prod μ)
      (fun p => spin (f p)-spin (g p))

theorem distance_nonneg (μ : Measure ℝ) (f g : Point → Bool) :
    0 ≤ distance μ f g := integral_nonneg (fun p => (pointDistance_bounds f g p).1)

theorem distance_symm (μ : Measure ℝ) (f g : Point → Bool) :
    distance μ f g = distance μ g f := by
  apply integral_congr_ae
  exact ae_of_all _ (fun p => abs_sub_comm _ _)

theorem distance_triangle (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f g k : Point → Bool) (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    distance μ f k ≤ distance μ f g + distance μ g k := by
  rw [distance, distance, distance, ←integral_add
    (pointDistance_integrable μ f g hf hg) (pointDistance_integrable μ g k hg hk)]
  apply integral_mono (pointDistance_integrable μ f k hf hk)
    ((pointDistance_integrable μ f g hf hg).add (pointDistance_integrable μ g k hg hk))
  intro p
  exact abs_sub_le _ _ _

end Q4.Candidate.EnergyLipschitz

#print axioms Q4.Candidate.EnergyLipschitz.indicator_difference_bound
#print axioms Q4.Candidate.EnergyLipschitz.energy_lipschitz
#print axioms Q4.Candidate.EnergyLipschitz.mean_lipschitz
