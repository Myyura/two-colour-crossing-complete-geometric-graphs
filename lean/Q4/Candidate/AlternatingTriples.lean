import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Actual measure and quantile ingredients of candidate Lemma 2.2. The complete
one-dimensional threshold approximation additionally needs the norm/kernel
identity and the minimum-disagreement partition argument; those are not assumed
to have been formalized by the theorems here.
-/

open MeasureTheory Set

namespace Q4.Candidate.AlternatingTriples

def alternating (h : ℝ → Bool) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ h p.1 = h p.2.2 ∧ h p.1 ≠ h p.2.1}

noncomputable def tripleMass (μ : Measure ℝ) (h : ℝ → Bool) : ℝ :=
  (μ.prod (μ.prod μ)).real (alternating h)

/-- An actual separated three-block product is contained in the alternation
event. Arbitrary measurable sign functions are allowed; finiteness supplies all
real-measure monotonicity requirements. -/
theorem rectangle_lower {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : ℝ → Bool) (A B C : Set ℝ) (bit : Bool)
    (hAB : ∀ r ∈ A, ∀ s ∈ B, r < s)
    (hBC : ∀ s ∈ B, ∀ t ∈ C, s < t)
    (hA : ∀ r ∈ A, h r = bit)
    (hB : ∀ s ∈ B, h s = !bit)
    (hC : ∀ t ∈ C, h t = bit) :
    μ.real A * μ.real B * μ.real C ≤ tripleMass μ h := by
  have hsub : A ×ˢ (B ×ˢ C) ⊆ alternating h := by
    intro p hp
    refine ⟨hAB p.1 hp.1 p.2.1 hp.2.1,
      hBC p.2.1 hp.2.1 p.2.2 hp.2.2, ?_, ?_⟩
    · exact (hA _ hp.1).trans (hC _ hp.2.2).symm
    · rw [hA _ hp.1, hB _ hp.2.1]
      cases bit <;> decide
  have hm := measureReal_mono (μ := μ.prod (μ.prod μ)) hsub
  simpa only [measureReal_prod_prod, tripleMass, mul_assoc] using hm

/-- The positive-mass quantile used in Lemma 2.2 exists by continuity of the
actual interval integral. No abstract quantile/existence axiom is used. -/
theorem integral_quantile {μ : Measure ℝ} [NullSingletonClass μ] (g : ℝ → ℝ)
    (hg : IntervalIntegrable g μ 0 1) (z : ℝ)
    (hz : 0 ≤ z) (hz' : z ≤ ∫ x in (0 : ℝ)..1, g x ∂μ) :
    ∃ a ∈ Icc (0 : ℝ) 1, (∫ x in (0 : ℝ)..a, g x ∂μ) = z := by
  have hc : ContinuousOn (fun a => ∫ x in (0 : ℝ)..a, g x ∂μ) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      intervalIntegral.continuousOn_primitive_interval' hg (a := (0 : ℝ)) left_mem_uIcc
  have hzmem : z ∈ Icc (∫ x in (0 : ℝ)..0, g x ∂μ) (∫ x in (0 : ℝ)..1, g x ∂μ) := by
    simpa only [intervalIntegral.integral_same, mem_Icc] using And.intro hz hz'
  exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc hzmem

/-- Two quantiles can be ordered without presupposing a strictly increasing
cumulative mass. The strict target inequality rules out the reversed order. -/
theorem ordered_integral_quantiles {μ : Measure ℝ} [NullSingletonClass μ] (g : ℝ → ℝ)
    (hg : IntervalIntegrable g μ 0 1)
    (hgn : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ g x)
    (z w : ℝ) (hz : 0 ≤ z) (hzw : z < w)
    (hw : w ≤ ∫ x in (0 : ℝ)..1, g x ∂μ) :
    ∃ a ∈ Icc (0 : ℝ) 1, ∃ b ∈ Icc (0 : ℝ) 1,
      a ≤ b ∧ (∫ x in (0 : ℝ)..a, g x ∂μ) = z ∧
      (∫ x in (0 : ℝ)..b, g x ∂μ) = w := by
  obtain ⟨a, ha, hqa⟩ := integral_quantile g hg z hz (le_trans (le_of_lt hzw) hw)
  obtain ⟨b, hb, hqb⟩ := integral_quantile g hg w (le_trans hz (le_of_lt hzw)) hw
  refine ⟨a, ha, b, hb, ?_, hqa, hqb⟩
  by_contra hab
  have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
  have hga : IntervalIntegrable g μ 0 a :=
    hg.mono_set (by simpa only [uIcc_of_le ha.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      using Icc_subset_Icc (le_refl (0 : ℝ)) ha.2)
  have hm : (∫ x in (0 : ℝ)..b, g x ∂μ) ≤ ∫ x in (0 : ℝ)..a, g x ∂μ :=
    intervalIntegral.integral_mono_interval (le_refl _) hb.1 hba
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact hgn x ⟨le_of_lt hx.1, le_trans hx.2 ha.2⟩) hga
  rw [hqa, hqb] at hm
  linarith

theorem before_middle_mass {μ : Measure ℝ} [IsFiniteMeasure μ]
    (P : Set ℝ) (hP : MeasurableSet P) (a b : ℝ) (hab : a ≤ b) :
    μ.real (P ∩ Iic a) + μ.real (P ∩ Ioc a b) = μ.real (P ∩ Iic b) := by
  have hd : Disjoint (P ∩ Iic a) (P ∩ Ioc a b) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.2.1
  have he : (P ∩ Iic a) ∪ (P ∩ Ioc a b) = P ∩ Iic b := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, le_trans hx.2 hab⟩
      · exact ⟨hx.1, hx.2.2⟩
    · intro hx
      by_cases hxa : x ≤ a
      · exact Or.inl ⟨hx.1, hxa⟩
      · exact Or.inr ⟨hx.1, lt_of_not_ge hxa, hx.2⟩
  rw [← measureReal_union hd (hP.inter measurableSet_Ioc), he]

theorem before_after_mass {μ : Measure ℝ} [IsFiniteMeasure μ]
    (P : Set ℝ) (hP : MeasurableSet P) (a : ℝ) :
    μ.real (P ∩ Iic a) + μ.real (P ∩ Ioi a) = μ.real P := by
  have hd : Disjoint (P ∩ Iic a) (P ∩ Ioi a) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (show x ≤ a from hx.2)) (show a < x from hy.2)
  have he : (P ∩ Iic a) ∪ (P ∩ Ioi a) = P := by
    ext x
    constructor
    · intro hx; exact hx.elim And.left And.left
    · intro hx
      by_cases hxa : x ≤ a
      · exact Or.inl ⟨hx, hxa⟩
      · exact Or.inr ⟨hx, lt_of_not_ge hxa⟩
  rw [← measureReal_union hd (hP.inter measurableSet_Ioi), he]

theorem three_block_mass {μ : Measure ℝ} [IsFiniteMeasure μ]
    (P : Set ℝ) (hP : MeasurableSet P) (a b : ℝ) (hab : a ≤ b) :
    μ.real (P ∩ Iic a) + μ.real (P ∩ Ioc a b) + μ.real (P ∩ Ioi b) = μ.real P := by
  rw [before_middle_mass P hP a b hab, before_after_mass P hP b]

/-- The full two-case mass argument of Lemma 2.2, on the actual alternation
event. `e` is any lower bound for the two threshold orientations; the two outer
positive quantiles are explicit inputs, whose existence is handled by the
ordered-integral quantile theorem. There is no assumed triple-mass estimate. -/
theorem quantile_blocks_force_alternations {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : ℝ → Bool) (hP : MeasurableSet {x | h x = true})
    (e a b : ℝ) (he : 0 ≤ e) (hab : a ≤ b)
    (hpos : e ≤ μ.real {x | h x = true})
    (hleft : μ.real ({x | h x = true} ∩ Iic a) = e/4)
    (hright : μ.real ({x | h x = true} ∩ Ioi b) = e/4)
    (hforward : e ≤ μ.real ({x | h x = true}ᶜ ∩ Iic b) +
      μ.real ({x | h x = true} ∩ Ioi b))
    (hbackward : e ≤ μ.real ({x | h x = true} ∩ Iic a) +
      μ.real ({x | h x = true}ᶜ ∩ Ioi a)) :
    e^3 ≤ 64 * tripleMass μ h := by
  let P := {x | h x = true}
  let lp := μ.real (P ∩ Iic a)
  let mp := μ.real (P ∩ Ioc a b)
  let rp := μ.real (P ∩ Ioi b)
  let ln := μ.real (Pᶜ ∩ Iic a)
  let mn := μ.real (Pᶜ ∩ Ioc a b)
  let rn := μ.real (Pᶜ ∩ Ioi b)
  have hmp : e/2 ≤ mp := by
    have hm := three_block_mass (μ := μ) P hP a b hab
    change lp + mp + rp = _ at hm
    change lp = _ at hleft
    change rp = _ at hright
    change e ≤ μ.real P at hpos
    linarith
  have hpp : lp * mn * rp ≤ tripleMass μ h :=
    rectangle_lower h (P ∩ Iic a) (Pᶜ ∩ Ioc a b) (P ∩ Ioi b) true
      (by intro r hr s hs; exact lt_of_le_of_lt hr.2 hs.2.1)
      (by intro s hs t ht; exact lt_of_le_of_lt hs.2.2 ht.2)
      (by intro r hr; exact hr.1)
      (by intro s hs; simpa only [Bool.not_true] using Bool.eq_false_iff.mpr hs.1)
      (by intro t ht; exact ht.1)
  by_cases hmn : e/4 ≤ mn
  · change lp = _ at hleft
    change rp = _ at hright
    rw [hleft, hright] at hpp
    have hm := mul_le_mul_of_nonneg_left hmn (sq_nonneg e)
    nlinarith
  · have hln : e/2 ≤ ln := by
      have hm := before_middle_mass (μ := μ) Pᶜ hP.compl a b hab
      change ln + mn = _ at hm
      change rp = _ at hright
      linarith
    have hrn : e/2 ≤ rn := by
      have hwhole := three_block_mass (μ := μ) Pᶜ hP.compl a b hab
      have hsplit := before_after_mass (μ := μ) Pᶜ hP.compl a
      change ln + mn + rn = _ at hwhole
      change ln + _ = _ at hsplit
      change lp = _ at hleft
      linarith
    have hnn : ln * mp * rn ≤ tripleMass μ h :=
      rectangle_lower h (Pᶜ ∩ Iic a) (P ∩ Ioc a b) (Pᶜ ∩ Ioi b) false
        (by intro r hr s hs; exact lt_of_le_of_lt hr.2 hs.2.1)
        (by intro s hs t ht; exact lt_of_le_of_lt hs.2.2 ht.2)
        (by intro r hr; exact Bool.eq_false_iff.mpr hr.1)
        (by intro s hs; exact hs.1)
        (by intro t ht; exact Bool.eq_false_iff.mpr ht.1)
    have he2 : 0 ≤ e/2 := by linarith
    have hln0 : 0 ≤ ln := measureReal_nonneg
    have hmp0 : 0 ≤ mp := measureReal_nonneg
    have hm1 := mul_le_mul hln hmp he2 hln0
    have hm2 := mul_le_mul hm1 hrn he2 (mul_nonneg hln0 hmp0)
    have he3 : 0 ≤ e^3 := pow_nonneg he _
    nlinarith

theorem Iic_mass_eq_integral_one {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hzero : μ.real (Iic (0 : ℝ)) = 0) (a : ℝ) (ha : 0 ≤ a) :
    μ.real (Iic a) = ∫ x in (0 : ℝ)..a, (1 : ℝ) ∂μ := by
  have hpart := before_middle_mass (μ := μ) univ MeasurableSet.univ 0 a ha
  simp only [univ_inter, hzero, zero_add] at hpart
  rw [← hpart, intervalIntegral.integral_of_le ha, integral_const]
  simp

/-- Atomless mass inside [0,1] supplies both positive quantiles needed by the
alternation argument. This is a measure theorem, with explicit support; taking
the restricted Lebesgue measure supplies the paper's setting. -/
theorem positive_quantiles {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hzero : μ.real (Iic (0 : ℝ)) = 0) (hone : μ.real (Ioi (1 : ℝ)) = 0)
    (P : Set ℝ) (hP : MeasurableSet P) (e : ℝ) (he : 0 < e)
    (hep : e ≤ μ.real P) :
    ∃ a ∈ Icc (0 : ℝ) 1, ∃ b ∈ Icc (0 : ℝ) 1,
      a ≤ b ∧ μ.real (P ∩ Iic a) = e/4 ∧ μ.real (P ∩ Ioi b) = e/4 := by
  let ν := μ.restrict P
  have hz : ν.real (Iic (0 : ℝ)) = 0 := by
    dsimp [ν]
    rw [measureReal_restrict_apply measurableSet_Iic]
    exact le_antisymm ((measureReal_mono inter_subset_left).trans_eq hzero) measureReal_nonneg
  have ho : ν.real (Ioi (1 : ℝ)) = 0 := by
    dsimp [ν]
    rw [measureReal_restrict_apply measurableSet_Ioi]
    exact le_antisymm ((measureReal_mono inter_subset_left).trans_eq hone) measureReal_nonneg
  have htotal : ν.real univ = μ.real P := measureReal_restrict_apply_univ P
  have hright := before_after_mass (μ := ν) univ MeasurableSet.univ 1
  simp only [univ_inter, ho, add_zero, htotal] at hright
  have hint : (∫ x in (0 : ℝ)..1, (1 : ℝ) ∂ν) = μ.real P := by
    rw [← Iic_mass_eq_integral_one hz 1 (by norm_num)]
    exact hright
  have hg : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) ν 0 1 := intervalIntegrable_const
  obtain ⟨a, ha, b, hb, hab, hqa, hqb⟩ :=
    ordered_integral_quantiles (μ := ν) (fun _ => (1 : ℝ)) hg (by intros; norm_num)
      (e/4) (μ.real P-e/4) (by linarith) (by linarith) (by rw [hint]; linarith)
  have hla : ν.real (Iic a) = e/4 := by rwa [Iic_mass_eq_integral_one hz a ha.1]
  have hlb : ν.real (Iic b) = μ.real P-e/4 := by rwa [Iic_mass_eq_integral_one hz b hb.1]
  have hsplit := before_after_mass (μ := ν) univ MeasurableSet.univ b
  simp only [univ_inter, htotal, hlb] at hsplit
  have hrb : ν.real (Ioi b) = e/4 := by linarith
  refine ⟨a, ha, b, hb, hab, ?_, ?_⟩
  · simpa only [ν, measureReal_restrict_apply measurableSet_Iic, inter_comm] using hla
  · simpa only [ν, measureReal_restrict_apply measurableSet_Ioi, inter_comm] using hrb

/-- A genuine atomless measure version of the cubic alternation bound. The
inputs say precisely that all two orientations of thresholds (and the constant
negative coloring) disagree by at least e. No quantile or rectangle bound is
assumed in the conclusion. -/
theorem threshold_distance_cubic {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hzero : μ.real (Iic (0 : ℝ)) = 0) (hone : μ.real (Ioi (1 : ℝ)) = 0)
    (h : ℝ → Bool) (hP : MeasurableSet {x | h x = true}) (e : ℝ) (he : 0 ≤ e)
    (hpos : e ≤ μ.real {x | h x = true})
    (hforward : ∀ t ∈ Icc (0 : ℝ) 1,
      e ≤ μ.real ({x | h x = true}ᶜ ∩ Iic t) + μ.real ({x | h x = true} ∩ Ioi t))
    (hbackward : ∀ t ∈ Icc (0 : ℝ) 1,
      e ≤ μ.real ({x | h x = true} ∩ Iic t) + μ.real ({x | h x = true}ᶜ ∩ Ioi t)) :
    e^3 ≤ 64 * tripleMass μ h := by
  by_cases he0 : e = 0
  · subst e
    have hm : 0 ≤ tripleMass μ h := measureReal_nonneg
    nlinarith
  · obtain ⟨a, ha, b, hb, hab, hl, hr⟩ := positive_quantiles hzero hone
      {x | h x = true} hP e (lt_of_le_of_ne he (Ne.symm he0)) hpos
    exact quantile_blocks_force_alternations h hP e a b he hab hpos hl hr
      (hforward b hb) (hbackward a ha)

end Q4.Candidate.AlternatingTriples

#print axioms Q4.Candidate.AlternatingTriples.rectangle_lower
#print axioms Q4.Candidate.AlternatingTriples.integral_quantile
#print axioms Q4.Candidate.AlternatingTriples.ordered_integral_quantiles
#print axioms Q4.Candidate.AlternatingTriples.quantile_blocks_force_alternations
#print axioms Q4.Candidate.AlternatingTriples.positive_quantiles
#print axioms Q4.Candidate.AlternatingTriples.threshold_distance_cubic
