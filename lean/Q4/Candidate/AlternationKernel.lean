import Q4.Candidate.AlternatingTriples
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.NormNum

/-!
Actual integral-kernel accounting for candidate Lemma 2.2.
The Boolean sign function is measured with an actual finite measure. The
alternation event is exactly `AlternatingTriples.alternating`.
-/

open MeasureTheory MeasureTheory.Measure Set

namespace Q4.Candidate.AlternationKernel

abbrev Triple := ℝ × ℝ × ℝ

def spin (b : Bool) : ℝ := if b then 1 else -1
noncomputable def cmp (x y : ℝ) : ℝ := if x < y then 1 else -1
noncomputable def kernel (h : ℝ → Bool) (x y : ℝ) : ℝ := cmp x y * spin (h y)
noncomputable def tripleKernel (h : ℝ → Bool) (p : Triple) : ℝ :=
  kernel h p.1 p.2.1 * kernel h p.1 p.2.2
noncomputable def transform (μ : Measure ℝ) (h : ℝ → Bool) (x : ℝ) : ℝ :=
  ∫ y, kernel h x y ∂μ
noncomputable def normSq (μ : Measure ℝ) (h : ℝ → Bool) : ℝ :=
  ∫ x, (transform μ h x)^2 ∂μ
noncomputable def altIndicator (h : ℝ → Bool) : Triple → ℝ :=
  (Q4.Candidate.AlternatingTriples.alternating h).indicator (fun _ => 1)

theorem spin_norm (b : Bool) : ‖spin b‖ = 1 := by cases b <;> norm_num [spin]
theorem cmp_norm (x y : ℝ) : ‖cmp x y‖ = 1 := by
  unfold cmp
  split <;> norm_num
theorem kernel_norm (h : ℝ → Bool) (x y : ℝ) : ‖kernel h x y‖ = 1 := by
  rw [kernel,norm_mul,cmp_norm,spin_norm,mul_one]
theorem tripleKernel_norm (h : ℝ → Bool) (p : Triple) : ‖tripleKernel h p‖ = 1 := by
  rw [tripleKernel,norm_mul,kernel_norm,kernel_norm,mul_one]

theorem measurable_spin_comp {α : Type*} [MeasurableSpace α]
    (f : α → Bool) (hf : Measurable f) : Measurable (fun x => spin (f x)) := by
  unfold spin
  exact Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const measurable_const

theorem kernel_measurable (h : ℝ → Bool) (hh : Measurable h) :
    Measurable (fun p : ℝ × ℝ => kernel h p.1 p.2) := by
  unfold kernel cmp
  exact (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const).mul
    (measurable_spin_comp _ (hh.comp measurable_snd))

theorem tripleKernel_measurable (h : ℝ → Bool) (hh : Measurable h) :
    Measurable (tripleKernel h) := by
  have hk := kernel_measurable h hh
  exact (hk.comp (measurable_fst.prodMk measurable_snd.fst)).mul
    (hk.comp (measurable_fst.prodMk measurable_snd.snd))

theorem tripleKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ℝ → Bool) (hh : Measurable h) :
    Integrable (tripleKernel h) (μ.prod (μ.prod μ)) := by
  exact Integrable.of_bound (tripleKernel_measurable h hh).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun p => le_of_eq (tripleKernel_norm h p)))

/-- Exact Fubini expansion of the actual squared antisymmetric-kernel norm. -/
theorem normSq_eq_triple_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ℝ → Bool) (hh : Measurable h) :
    normSq μ h = ∫ p, tripleKernel h p ∂μ.prod (μ.prod μ) := by
  rw [integral_prod _ (tripleKernel_integrable μ h hh)]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ y, kernel h x y ∂μ)^2 =
    ∫ p : ℝ × ℝ, kernel h x p.1 * kernel h x p.2 ∂μ.prod μ
  rw [integral_prod_mul]
  ring

theorem alternating_measurable (h : ℝ → Bool) (hh : Measurable h) :
    MeasurableSet (Q4.Candidate.AlternatingTriples.alternating h) := by
  exact (measurableSet_lt measurable_fst measurable_snd.fst).inter
    ((measurableSet_lt measurable_snd.fst measurable_snd.snd).inter
      ((measurableSet_eq_fun (hh.comp measurable_fst) (hh.comp measurable_snd.snd)).inter
        (measurableSet_eq_fun (hh.comp measurable_fst) (hh.comp measurable_snd.fst)).compl))

theorem altIndicator_measurable (h : ℝ → Bool) (hh : Measurable h) :
    Measurable (altIndicator h) :=
  measurable_const.indicator (alternating_measurable h hh)

theorem altIndicator_norm_le (h : ℝ → Bool) (p : Triple) : ‖altIndicator h p‖ ≤ 1 := by
  classical
  by_cases hp : p ∈ Q4.Candidate.AlternatingTriples.alternating h <;>
    simp [altIndicator,Set.indicator,hp]

theorem altIndicator_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ℝ → Bool) (hh : Measurable h) :
    Integrable (altIndicator h) (μ.prod (μ.prod μ)) := by
  exact Integrable.of_bound (altIndicator_measurable h hh).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (altIndicator_norm_le h))

theorem integral_altIndicator (μ : Measure ℝ) (h : ℝ → Bool) (hh : Measurable h) :
    (∫ p, altIndicator h p ∂μ.prod (μ.prod μ)) =
      Q4.Candidate.AlternatingTriples.tripleMass μ h := by
  exact integral_indicator_one (alternating_measurable h hh)

/-- The six coordinate permutations are genuine measurable equivalences. -/
def swap12 : Triple ≃ᵐ Triple :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℝ)).trans
      MeasurableEquiv.prodAssoc)
def swap23 : Triple ≃ᵐ Triple :=
  (MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm
def cycle : Triple ≃ᵐ Triple := swap12.trans swap23
def cycle2 : Triple ≃ᵐ Triple := cycle.trans cycle
def reverse : Triple ≃ᵐ Triple := (swap12.trans swap23).trans swap12

@[simp] theorem swap12_apply (p : Triple) : swap12 p = (p.2.1,p.1,p.2.2) := rfl
@[simp] theorem swap23_apply (p : Triple) : swap23 p = (p.1,p.2.2,p.2.1) := rfl
@[simp] theorem cycle_apply (p : Triple) : cycle p = (p.2.1,p.2.2,p.1) := rfl
@[simp] theorem cycle2_apply (p : Triple) : cycle2 p = (p.2.2,p.1,p.2.1) := rfl
@[simp] theorem reverse_apply (p : Triple) : reverse p = (p.2.2,p.2.1,p.1) := rfl

theorem swap12_preserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving swap12 (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) := by
  exact (measurePreserving_prodAssoc μ μ μ).comp
    ((measurePreserving_swap.prod (MeasurePreserving.id μ)).comp
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ μ μ)))
theorem swap23_preserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving swap23 (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) := by
  exact (MeasurePreserving.id μ).prod measurePreserving_swap
theorem cycle_preserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving cycle (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) :=
  (swap23_preserving μ).comp (swap12_preserving μ)
theorem cycle2_preserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving cycle2 (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) :=
  (cycle_preserving μ).comp (cycle_preserving μ)
theorem reverse_preserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving reverse (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) :=
  (swap12_preserving μ).comp (cycle_preserving μ)

/-- At a distinct triple, three cyclic kernel products count precisely the
six ordered alternation events, with coefficient four. -/
theorem cyclic_identity (h : ℝ → Bool) (a b c : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tripleKernel h (a,b,c) + tripleKernel h (b,c,a) + tripleKernel h (c,a,b) +
      4 * (altIndicator h (a,b,c) + altIndicator h (b,a,c) +
        altIndicator h (a,c,b) + altIndicator h (b,c,a) +
        altIndicator h (c,a,b) + altIndicator h (c,b,a)) = 1 := by
  classical
  rcases lt_or_gt_of_ne hab with hab | hab <;>
    rcases lt_or_gt_of_ne hac with hac | hac <;>
    rcases lt_or_gt_of_ne hbc with hbc | hbc
  all_goals first | (exfalso; linarith) |
    (have habn := not_lt_of_ge (le_of_lt hab)
     have hacn := not_lt_of_ge (le_of_lt hac)
     have hbcn := not_lt_of_ge (le_of_lt hbc)
     cases ha : h a <;> cases hb : h b <;> cases hc : h c <;>
      simp [ha,hb,hc,hab,hac,hbc,habn,hacn,hbcn,tripleKernel,kernel,cmp,spin,altIndicator,
        Q4.Candidate.AlternatingTriples.alternating,Set.indicator] <;> norm_num)

/-- Actual atomlessness removes all three diagonals of product measure. -/
theorem ae_distinct (μ : Measure ℝ) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ p : Triple ∂μ.prod (μ.prod μ),
      p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by
  apply (ae_prod_iff_ae_ae
    ((measurableSet_eq_fun measurable_fst measurable_snd.fst).compl.inter
      ((measurableSet_eq_fun measurable_fst measurable_snd.snd).compl.inter
        (measurableSet_eq_fun measurable_snd.fst measurable_snd.snd).compl))).2
  filter_upwards [] with a
  apply (ae_prod_iff_ae_ae
    ((measurableSet_eq_fun measurable_const measurable_fst).compl.inter
      ((measurableSet_eq_fun measurable_const measurable_snd).compl.inter
        (measurableSet_eq_fun measurable_fst measurable_snd).compl))).2
  filter_upwards [ae_ne μ a] with b hba
  filter_upwards [ae_ne μ a, ae_ne μ b] with c hca hcb
  exact ⟨Ne.symm hba,Ne.symm hca,Ne.symm hcb⟩

/-- Exact antisymmetric-kernel identity for every atomless probability measure.
No sorting formula, Fubini identity, or alternation mass is an input hypothesis. -/
theorem kernel_identity (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (h : ℝ → Bool) (hh : Measurable h) :
    normSq μ h = 1 / 3 - 8 * Q4.Candidate.AlternatingTriples.tripleMass μ h := by
  have hK := tripleKernel_integrable μ h hh
  have hK1 : Integrable (fun p => tripleKernel h (cycle p)) (μ.prod (μ.prod μ)) :=
    ((cycle_preserving μ).integrable_comp hK.aestronglyMeasurable).2 hK
  have hK2 : Integrable (fun p => tripleKernel h (cycle2 p)) (μ.prod (μ.prod μ)) :=
    ((cycle2_preserving μ).integrable_comp hK.aestronglyMeasurable).2 hK
  have hA := altIndicator_integrable μ h hh
  have hA12 : Integrable (fun p => altIndicator h (swap12 p)) (μ.prod (μ.prod μ)) :=
    ((swap12_preserving μ).integrable_comp hA.aestronglyMeasurable).2 hA
  have hA23 : Integrable (fun p => altIndicator h (swap23 p)) (μ.prod (μ.prod μ)) :=
    ((swap23_preserving μ).integrable_comp hA.aestronglyMeasurable).2 hA
  have hA1 : Integrable (fun p => altIndicator h (cycle p)) (μ.prod (μ.prod μ)) :=
    ((cycle_preserving μ).integrable_comp hA.aestronglyMeasurable).2 hA
  have hA2 : Integrable (fun p => altIndicator h (cycle2 p)) (μ.prod (μ.prod μ)) :=
    ((cycle2_preserving μ).integrable_comp hA.aestronglyMeasurable).2 hA
  have hAR : Integrable (fun p => altIndicator h (reverse p)) (μ.prod (μ.prod μ)) :=
    ((reverse_preserving μ).integrable_comp hA.aestronglyMeasurable).2 hA
  have hK01 : Integrable (fun p => tripleKernel h p + tripleKernel h (cycle p))
      (μ.prod (μ.prod μ)) := hK.add hK1
  have hK012 : Integrable (fun p => tripleKernel h p + tripleKernel h (cycle p) +
      tripleKernel h (cycle2 p)) (μ.prod (μ.prod μ)) := hK01.add hK2
  have hAS2 : Integrable (fun p => altIndicator h p + altIndicator h (swap12 p))
      (μ.prod (μ.prod μ)) := hA.add hA12
  have hAS3 : Integrable (fun p => altIndicator h p + altIndicator h (swap12 p) + altIndicator h (swap23 p))
      (μ.prod (μ.prod μ)) := hAS2.add hA23
  have hAS4 : Integrable (fun p => altIndicator h p + altIndicator h (swap12 p) + altIndicator h (swap23 p) + altIndicator h (cycle p))
      (μ.prod (μ.prod μ)) := hAS3.add hA1
  have hAS5 : Integrable (fun p => altIndicator h p + altIndicator h (swap12 p) + altIndicator h (swap23 p) + altIndicator h (cycle p) + altIndicator h (cycle2 p))
      (μ.prod (μ.prod μ)) := hAS4.add hA2
  have hAS6 : Integrable (fun p => altIndicator h p + altIndicator h (swap12 p) + altIndicator h (swap23 p) + altIndicator h (cycle p) + altIndicator h (cycle2 p) + altIndicator h (reverse p))
      (μ.prod (μ.prod μ)) := hAS5.add hAR
  have hKI : (∫ p, tripleKernel h p + tripleKernel h (cycle p) +
      tripleKernel h (cycle2 p) ∂μ.prod (μ.prod μ)) = 3 * normSq μ h := by
    rw [integral_add hK01 hK2,integral_add hK hK1,
      (cycle_preserving μ).integral_comp', (cycle2_preserving μ).integral_comp',
      ← normSq_eq_triple_integral μ h hh]
    ring
  have hAI : (∫ p, altIndicator h p + altIndicator h (swap12 p) +
      altIndicator h (swap23 p) + altIndicator h (cycle p) +
      altIndicator h (cycle2 p) + altIndicator h (reverse p) ∂μ.prod (μ.prod μ)) =
      6 * Q4.Candidate.AlternatingTriples.tripleMass μ h := by
    rw [integral_add hAS5 hAR,
      integral_add hAS4 hA2,
      integral_add hAS3 hA1,
      integral_add hAS2 hA23, integral_add hA hA12,
      (swap12_preserving μ).integral_comp', (swap23_preserving μ).integral_comp',
      (cycle_preserving μ).integral_comp', (cycle2_preserving μ).integral_comp',
      (reverse_preserving μ).integral_comp', integral_altIndicator μ h hh]
    ring
  have htotal : (∫ p, tripleKernel h p + tripleKernel h (cycle p) +
      tripleKernel h (cycle2 p) +
      4 * (altIndicator h p + altIndicator h (swap12 p) + altIndicator h (swap23 p) +
        altIndicator h (cycle p) + altIndicator h (cycle2 p) + altIndicator h (reverse p)) ∂μ.prod (μ.prod μ)) = 1 := by
    calc
      _ = ∫ _p : Triple, (1 : ℝ) ∂μ.prod (μ.prod μ) := by
        apply integral_congr_ae
        filter_upwards [ae_distinct μ] with p hp
        exact cyclic_identity h p.1 p.2.1 p.2.2 hp.1 hp.2.1 hp.2.2
      _ = 1 := by simp
  rw [integral_add hK012 (hAS6.const_mul 4),
      integral_const_mul, hKI, hAI] at htotal
  linarith

end Q4.Candidate.AlternationKernel

#print axioms Q4.Candidate.AlternationKernel.normSq_eq_triple_integral
#print axioms Q4.Candidate.AlternationKernel.integral_altIndicator

#print axioms Q4.Candidate.AlternationKernel.cyclic_identity
#print axioms Q4.Candidate.AlternationKernel.ae_distinct
#print axioms Q4.Candidate.AlternationKernel.kernel_identity
