import Q4.Candidate.CanonicalField
import Q4.Candidate.DiagonalRounding
import Mathlib.Order.Interval.Set.Union

/-! Borel cell extensions of actual finite rectangular-grid colorings.
All cells are half-open Ioc intervals, so they partition the probability
square exactly. Finite normalized costs and continuous costs are connected
through their actual Lebesgue integrals. -/
open MeasureTheory Set

namespace Q4.Candidate.GridStepExtension
open Q4.Candidate.UnitIntervalMeasure Q4.Candidate.AlternationKernel
open Q4.Candidate.ComparisonEnergy

abbrev Vertex (m n : Nat) := Fin m × Fin n
abbrev Point := ℝ × ℝ

noncomputable def slice (m : Nat) (i : Fin m) : Set ℝ :=
  Ioc ((i:ℝ)/m) (((i:ℝ)+1)/m)
noncomputable def cell {m n : Nat} (v : Vertex m n) : Set Point :=
  slice m v.1 ×ˢ slice n v.2

theorem slice_measurable (m : Nat) (i : Fin m) : MeasurableSet (slice m i) := measurableSet_Ioc
theorem cell_measurable {m n : Nat} (v : Vertex m n) : MeasurableSet (cell v) :=
  (slice_measurable m v.1).prod (slice_measurable n v.2)

theorem slice_subset_unit (m : Nat) (hm : 0 < m) (i : Fin m) : slice m i ⊆ Ioc (0:ℝ) 1 := by
  intro x hx
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hi : (i:ℝ)+1 ≤ m := by exact_mod_cast i.isLt
  exact ⟨lt_of_le_of_lt (by positivity) hx.1,
    le_trans hx.2 ((div_le_one hmR).mpr hi)⟩

theorem slice_order (m : Nat) (hm : 0 < m) {i j : Fin m} (hij : i < j)
    {x y : ℝ} (hx : x ∈ slice m i) (hy : y ∈ slice m j) : x < y := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hi : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hij
  exact lt_of_le_of_lt (hx.2.trans ((div_le_div_iff_of_pos_right hmR).mpr hi)) hy.1

theorem slice_disjoint (m : Nat) (hm : 0 < m) : Pairwise (fun i j => Disjoint (slice m i) (slice m j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (lt_irrefl x) (slice_order m hm hlt hx hy)
  · exact (lt_irrefl x) (slice_order m hm hgt hy hx)

theorem slice_cover (m : Nat) (hm : 0 < m) : (⋃ i : Fin m, slice m i) = Ioc (0:ℝ) 1 := by
  apply Subset.antisymm
  · exact iUnion_subset (fun i => slice_subset_unit m hm i)
  · intro x hx
    have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    have hx' : x ∈ Ioc ((0:ℝ)/m) ((m:ℝ)/m) := by simpa [hm0] using hx
    have hh := Ioc_subset_biUnion_Ioc m (fun k : Nat => (k:ℝ)/m) (by simpa only [Nat.cast_zero] using hx')
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hh
    refine mem_iUnion.mpr ⟨⟨i,Finset.mem_range.mp hi⟩,?_⟩
    simpa only [slice,Nat.cast_add,Nat.cast_one] using hxi

theorem cell_subset_square {m n : Nat} (hm : 0 < m) (hn : 0 < n) (v : Vertex m n) :
    cell v ⊆ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1 :=
  prod_mono (slice_subset_unit m hm v.1) (slice_subset_unit n hn v.2)

theorem cell_disjoint (m n : Nat) (hm : 0 < m) (hn : 0 < n) : Pairwise (fun v w : Vertex m n => Disjoint (cell v) (cell w)) := by
  intro v w hvw
  apply disjoint_left.mpr
  intro p hp hq
  by_cases h1 : v.1 = w.1
  · have h2 : v.2 ≠ w.2 := by intro h2; exact hvw (Prod.ext h1 h2)
    exact Set.disjoint_left.mp (slice_disjoint n hn h2) hp.2 hq.2
  · exact Set.disjoint_left.mp (slice_disjoint m hm h1) hp.1 hq.1

theorem cell_cover (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    (⋃ v : Vertex m n, cell v) = Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1 := by
  ext p
  constructor
  · intro hp
    obtain ⟨v,hv⟩ := mem_iUnion.mp hp
    exact cell_subset_square hm hn v hv
  · intro hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp ((slice_cover m hm).symm ▸ hp.1)
    obtain ⟨j,hj⟩ := mem_iUnion.mp ((slice_cover n hn).symm ▸ hp.2)
    exact mem_iUnion.mpr ⟨(i,j),hi,hj⟩

theorem slice_area (m : Nat) (hm : 0 < m) (i : Fin m) :
    volume.real (slice m i) = 1/(m:ℝ) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  rw [slice,Real.volume_real_Ioc]
  have he : ((i:ℝ)+1)/(m:ℝ)-(i:ℝ)/m = 1/m := by ring
  rw [he,max_eq_left (by positivity)]

theorem cell_area {m n : Nat} (hm : 0 < m) (hn : 0 < n) (v : Vertex m n) :
    volume.real (cell v) = 1/((m:ℝ)*n) := by
  rw [cell,Measure.volume_eq_prod,measureReal_prod_prod,slice_area m hm,slice_area n hn]
  ring

theorem unit_restrict_cell {m n : Nat} (hm : 0 < m) (hn : 0 < n) (v : Vertex m n) :
    (unit.prod unit).restrict (cell v) = volume.restrict (cell v) := by
  rw [unit,Measure.prod_restrict,←Measure.volume_eq_prod,Measure.restrict_restrict (cell_measurable v),
    inter_eq_left.mpr (cell_subset_square hm hn v)]

noncomputable def coloredCells {m n : Nat} (χ : Vertex m n → Bool) : Set Point :=
  ⋃ v, if χ v = true then cell v else ∅
noncomputable def extension {m n : Nat} (χ : Vertex m n → Bool) (p : Point) : Bool :=
  by classical exact if p ∈ coloredCells χ then true else false

theorem extension_measurable {m n : Nat} (χ : Vertex m n → Bool) : Measurable (extension χ) := by
  have hm : MeasurableSet (coloredCells χ) := by
    apply MeasurableSet.iUnion
    intro v
    split <;> simp only [cell_measurable,MeasurableSet.empty]
  exact Measurable.ite hm measurable_const measurable_const

theorem extension_on_cell {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (χ : Vertex m n → Bool) (v : Vertex m n) (p : Point) (hp : p ∈ cell v) :
    extension χ p = χ v := by
  classical
  have hc : p ∈ coloredCells χ ↔ χ v = true := by
    constructor
    · intro hc
      obtain ⟨w,hw⟩ := mem_iUnion.mp hc
      by_cases hwc : χ w = true
      · simp only [ite_eq_left hwc] at hw
        have hvw : v = w := by
          by_contra hvw
          exact Set.disjoint_left.mp (cell_disjoint m n hm hn hvw) hp hw
        simpa [hvw] using hwc
      · simp [hwc] at hw
    · intro hv
      exact mem_iUnion.mpr ⟨v,by simpa [hv] using hp⟩
  cases hv : χ v <;> simp [extension,hc,hv]

/-- Exact finite cell decomposition of an integrable function. -/
theorem integral_cells (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (g : Point → ℝ) (hg : Integrable g (unit.prod unit)) :
    (∫ p, g p ∂unit.prod unit) = ∑ v : Vertex m n, ∫ p in cell v, g p := by
  have hc (v : Vertex m n) : IntegrableOn g (cell v) := by
    have hi := hg.integrableOn (s := cell v)
    unfold IntegrableOn at hi ⊢
    rwa [unit_restrict_cell hm hn v] at hi
  rw [unit,Measure.prod_restrict,←Measure.volume_eq_prod,←cell_cover m n hm hn]
  exact integral_iUnion_fintype cell_measurable (cell_disjoint m n hm hn) hc

/-- Exact integration of any actual cellwise constant function. -/
theorem integral_cell_constant (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (g : Point → ℝ) (hg : Integrable g (unit.prod unit)) (a : Vertex m n → ℝ)
    (ha : ∀ v p, p ∈ cell v → g p = a v) :
    (∫ p, g p ∂unit.prod unit) = (∑ v : Vertex m n, a v)/((m:ℝ)*n) := by
  rw [integral_cells m n hm hn g hg]
  have hc (v : Vertex m n) : (∫ p in cell v, g p) = a v/((m:ℝ)*n) := by
    rw [setIntegral_congr_fun (cell_measurable v) (ha v),integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
    change volume.real (cell v)*a v = _
    rw [cell_area hm hn v]
    ring
  simp_rw [hc]
  exact (Finset.sum_div _ _ _).symm

/-- Upper quadrature bound from actual pointwise bounds on each cell. -/
theorem integral_cells_upper (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (g : Point → ℝ) (hg : Integrable g (unit.prod unit)) (a : Vertex m n → ℝ)
    (ha : ∀ v p, p ∈ cell v → g p ≤ a v) :
    (∫ p, g p ∂unit.prod unit) ≤ (∑ v : Vertex m n, a v)/((m:ℝ)*n) := by
  rw [integral_cells m n hm hn g hg,Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  calc
    _ ≤ ∫ _p in cell v, a v := by
      rw [←unit_restrict_cell hm hn v]
      apply integral_mono_ae hg.integrableOn (integrable_const _)
      filter_upwards [ae_restrict_mem (cell_measurable v)] with p hp
      exact ha v p hp
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
      change volume.real (cell v)*a v = _
      rw [cell_area hm hn v]
      ring

theorem integral_cells_lower (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (g : Point → ℝ) (hg : Integrable g (unit.prod unit)) (a : Vertex m n → ℝ)
    (ha : ∀ v p, p ∈ cell v → a v ≤ g p) :
    (∑ v : Vertex m n, a v)/((m:ℝ)*n) ≤ ∫ p, g p ∂unit.prod unit := by
  have he := integral_cells_upper m n hm hn (fun p => -g p) hg.neg
    (fun v => -a v) (fun v p hp => neg_le_neg (ha v p hp))
  simpa only [integral_neg,Finset.sum_neg_distrib,neg_div,neg_le_neg_iff] using he

noncomputable def discreteIndicator {m n : Nat} (χ : Vertex m n → Bool) (v w : Vertex m n) : ℝ :=
  if v.1 < w.1 ∧ v.2 < w.2 ∧ χ v = χ w then 1 else 0
noncomputable def normalizedCount {m n : Nat} (χ : Vertex m n → Bool) : ℝ :=
  (∑ v : Vertex m n, ∑ w : Vertex m n, discreteIndicator χ v w)/((m:ℝ)*n)^2

theorem slice_order_weak (m : Nat) (hm : 0 < m) {i j : Fin m}
    {x y : ℝ} (hx : x ∈ slice m i) (hy : y ∈ slice m j) (hxy : x < y) : i ≤ j := by
  by_contra hn
  exact not_lt_of_gt hxy (slice_order m hm (lt_of_not_ge hn) hy hx)

theorem energy_cell_bounds {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (χ : Vertex m n → Bool) (v w : Vertex m n) (p q : Point)
    (hp : p ∈ cell v) (hq : q ∈ cell w) :
    discreteIndicator χ v w ≤ energyIndicator (extension χ) (p,q) ∧
    energyIndicator (extension χ) (p,q) ≤ discreteIndicator χ v w+
      (if v.1 = w.1 then 1 else 0)+(if v.2 = w.2 then 1 else 0) := by
  classical
  have he1 := extension_on_cell hm hn χ v p hp
  have he2 := extension_on_cell hm hn χ w q hq
  unfold energyIndicator discreteIndicator
  simp only [he1,he2]
  by_cases hdisc : v.1 < w.1 ∧ v.2 < w.2 ∧ χ v = χ w
  · have hc : p.1 < q.1 ∧ p.2 < q.2 ∧ χ v = χ w :=
      ⟨slice_order m hm hdisc.1 hp.1 hq.1,slice_order n hn hdisc.2.1 hp.2 hq.2,hdisc.2.2⟩
    simp [hdisc,hc,ne_of_lt hdisc.1,ne_of_lt hdisc.2.1]
  · by_cases hc : p.1 < q.1 ∧ p.2 < q.2 ∧ χ v = χ w
    · have hl1 := slice_order_weak m hm hp.1 hq.1 hc.1
      have hl2 := slice_order_weak n hn hp.2 hq.2 hc.2.1
      have heq : v.1 = w.1 ∨ v.2 = w.2 := by
        by_contra heq
        have hn1 : v.1 ≠ w.1 := fun h => heq (Or.inl h)
        have hn2 : v.2 ≠ w.2 := fun h => heq (Or.inr h)
        exact hdisc ⟨lt_of_le_of_ne hl1 hn1,lt_of_le_of_ne hl2 hn2,hc.2.2⟩
      rcases heq with h1 | h2
      · simp [hc,h1]
        positivity
      · simp [hc,h2]
        positivity
    · simp [hdisc,hc]
      positivity

theorem extension_kernel_integrable {m n : Nat} (χ : Vertex m n → Bool) (p : Point) :
    Integrable (fun q : Point => energyIndicator (extension χ) (p,q)) (unit.prod unit) := by
  apply bounded_integrable _ _
    ((energyIndicator_measurable _ (extension_measurable χ)).comp (measurable_const.prodMk measurable_id))
  intro q
  change ‖energyIndicator (extension χ) (p,q)‖ ≤ 1
  unfold energyIndicator
  split <;> norm_num

/-- Lower finite comparison bound: all off-row/off-column comparisons
contribute exactly their finite grid edge cost. -/
theorem extension_energy_lower (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (χ : Vertex m n → Bool) : normalizedCount χ ≤ energy unit (extension χ) := by
  have hi := energyIndicator_integrable unit (extension χ) (extension_measurable χ)
  unfold energy
  rw [integral_prod _ hi]
  have he := integral_cells_lower m n hm hn _ hi.integral_prod_left
    (fun v => (∑ w : Vertex m n, discreteIndicator χ v w)/((m:ℝ)*n)) (by
      intro v p hp
      exact integral_cells_lower m n hm hn _ (extension_kernel_integrable χ p)
        (fun w => discreteIndicator χ v w) (fun w q hq => (energy_cell_bounds hm hn χ v w p q hp hq).1))
  calc
    _ = (∑ v : Vertex m n, (∑ w : Vertex m n, discreteIndicator χ v w)/((m:ℝ)*n))/((m:ℝ)*n) := by
      rw [←Finset.sum_div]
      unfold normalizedCount
      ring
    _ ≤ _ := he

theorem row_collision_sum (m n : Nat) (v : Vertex m n) :
    (∑ w : Vertex m n, (if v.1 = w.1 then (1:ℝ) else 0)) = n := by
  classical
  rw [Fintype.sum_prod_type]
  change (∑ i : Fin m, ∑ _j : Fin n, (if v.1 = i then (1:ℝ) else 0)) = n
  have he (i : Fin m) : (∑ _j : Fin n, (if v.1 = i then (1:ℝ) else 0)) =
      if v.1 = i then (n:ℝ) else 0 := by
    by_cases hi : v.1 = i <;> simp [hi]
  simp_rw [he]
  simp

theorem col_collision_sum (m n : Nat) (v : Vertex m n) :
    (∑ w : Vertex m n, (if v.2 = w.2 then (1:ℝ) else 0)) = m := by
  classical
  rw [Fintype.sum_prod_type]
  simp

/-- Same-row and same-column pairs are the only possible additional
contributions. Their actual normalized probability is at most rho. -/
theorem extension_energy_upper (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (χ : Vertex m n → Bool) :
    energy unit (extension χ) ≤ normalizedCount χ+GridCounts.rho m n := by
  have hi := energyIndicator_integrable unit (extension χ) (extension_measurable χ)
  unfold energy
  rw [integral_prod _ hi]
  have he := integral_cells_upper m n hm hn _ hi.integral_prod_left
    (fun v => ((∑ w : Vertex m n, discreteIndicator χ v w)+(n:ℝ)+(m:ℝ))/((m:ℝ)*n)) (by
      intro v p hp
      have hh := integral_cells_upper m n hm hn _ (extension_kernel_integrable χ p)
        (fun w => discreteIndicator χ v w+(if v.1 = w.1 then 1 else 0)+(if v.2 = w.2 then 1 else 0))
        (fun w q hq => (energy_cell_bounds hm hn χ v w p q hp hq).2)
      simpa only [Finset.sum_add_distrib,row_collision_sum,col_collision_sum] using hh)
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  calc
    _ ≤ _ := he
    _ = _ := by
      rw [←Finset.sum_div]
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
      unfold normalizedCount GridCounts.rho
      field_simp
      ring

/-- The true L1 distance between two cell extensions is exactly the finite
spin disagreement sum divided by N. -/
theorem extension_distance (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (χ ψ : Vertex m n → Bool) :
    EnergyLipschitz.distance unit (extension χ) (extension ψ) =
      (∑ v : Vertex m n, |spin (χ v)-spin (ψ v)|)/((m:ℝ)*n) := by
  apply integral_cell_constant m n hm hn _
    (EnergyLipschitz.pointDistance_integrable unit (extension χ) (extension ψ)
      (extension_measurable χ) (extension_measurable ψ))
  intro v p hp
  simp only [EnergyLipschitz.pointDistance,extension_on_cell hm hn χ v p hp,
    extension_on_cell hm hn ψ v p hp]

end Q4.Candidate.GridStepExtension

#print axioms Q4.Candidate.GridStepExtension.cell_cover
#print axioms Q4.Candidate.GridStepExtension.cell_area
#print axioms Q4.Candidate.GridStepExtension.extension_measurable
#print axioms Q4.Candidate.GridStepExtension.extension_on_cell
#print axioms Q4.Candidate.GridStepExtension.integral_cell_constant
#print axioms Q4.Candidate.GridStepExtension.extension_distance

#print axioms Q4.Candidate.GridStepExtension.extension_energy_lower

#print axioms Q4.Candidate.GridStepExtension.extension_energy_upper
