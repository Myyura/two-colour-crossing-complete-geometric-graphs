import Q4.Candidate.GridStepExtension
import Q4.Candidate.TwoPhaseStability
import Q4.Candidate.CanonicalEnergy
import Q4.Candidate.GridInitialConstants

open MeasureTheory Set

namespace Q4.Candidate.GridStepBridge
open Q4.Candidate.GridStepExtension Q4.Candidate.UnitIntervalMeasure
open Q4.Candidate.AlternationKernel Q4.Candidate.ComparisonEnergy

abbrev Point := ℝ × ℝ

theorem monoCount_list_sum {α : Type*} (es : List (α×α)) (χ : α → Bool) :
    (Q4.monoCount es χ : ℝ) =
      (es.map (fun e => if χ e.1 = χ e.2 then (1:ℝ) else 0)).sum := by
  induction es with
  | nil => simp [Q4.monoCount]
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    by_cases hc : χ a = χ b <;> simp [Q4.monoCount,hc,ih]

theorem normalizedCount_eq_monoCount (m n : Nat) (χ : Vertex m n → Bool) :
    normalizedCount χ = (Q4.monoCount (GridLocalization.gridEdges m n) χ : ℝ)/((m:ℝ)*n)^2 := by
  unfold normalizedCount GridLocalization.gridEdges
  rw [monoCount_list_sum,Finset.sum_map_toList,GridCounts.orientedEdges,Finset.sum_filter]
  congr 1
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  unfold discreteIndicator
  by_cases h1 : v.1 < w.1 <;> by_cases h2 : v.2 < w.2 <;> by_cases hc : χ v = χ w <;>
    simp [h1,h2,hc]

theorem actual_energy_bounds (m n : Nat) (hm : 0 < m) (hn : 0 < n) (χ : Vertex m n → Bool) :
    (Q4.monoCount (GridLocalization.gridEdges m n) χ : ℝ)/((m:ℝ)*n)^2 ≤ energy unit (extension χ) ∧
    energy unit (extension χ) ≤ (Q4.monoCount (GridLocalization.gridEdges m n) χ : ℝ)/((m:ℝ)*n)^2+GridCounts.rho m n := by
  simpa only [normalizedCount_eq_monoCount] using
    And.intro (extension_energy_lower m n hm hn χ) (extension_energy_upper m n hm hn χ)

noncomputable def disagreement {m n : Nat} (χ ψ : Vertex m n → Bool) : Finset (Vertex m n) :=
  Finset.univ.filter (fun v => χ v ≠ ψ v)

theorem extension_distance_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (χ ψ : Vertex m n → Bool) :
    EnergyLipschitz.distance unit (extension χ) (extension ψ) =
      2*((disagreement χ ψ).card : ℝ)/((m:ℝ)*n) := by
  rw [extension_distance m n hm hn]
  have he (v : Vertex m n) : |spin (χ v)-spin (ψ v)| = if χ v ≠ ψ v then (2:ℝ) else 0 := by
    cases hc : χ v <;> cases hp : ψ v <;> norm_num [spin,hc,hp]
  simp_rw [he]
  simp [disagreement,Finset.sum_ite,Finset.sum_const,nsmul_eq_mul,mul_comm]

noncomputable def diagonalBand (t : ℝ) : Set Point := {p | |p.1+p.2-1| ≤ t}

theorem diagonalBand_measurable (t : ℝ) : MeasurableSet (diagonalBand t) :=
  measurableSet_le ((measurable_fst.add measurable_snd).sub measurable_const).norm measurable_const

theorem band_section (x t : ℝ) : {y : ℝ | |x+y-1| ≤ t} = Icc (1-x-t) (1-x+t) := by
  ext y
  simp only [mem_ofPred_eq,abs_le,mem_Icc]
  constructor <;> intro hy <;> constructor <;> linarith [hy.1,hy.2]

theorem band_section_area (x t : ℝ) (ht : 0 ≤ t) :
    unit.real {y : ℝ | |x+y-1| ≤ t} ≤ 2*t := by
  rw [band_section,unit,measureReal_restrict_apply measurableSet_Icc]
  calc
    _ ≤ volume.real (Icc (1-x-t) (1-x+t)) := measureReal_mono inter_subset_left (isCompact_Icc.measure_lt_top.ne)
    _ = _ := by rw [Real.volume_real_Icc,show 1-x+t-(1-x-t) = 2*t by ring,max_eq_left (by positivity)]

theorem diagonalBand_integral (t : ℝ) (ht : 0 ≤ t) :
    (∫ p : Point, (diagonalBand t).indicator (fun _ => (1:ℝ)) p ∂unit.prod unit) ≤ 2*t := by
  have hi : Integrable ((diagonalBand t).indicator (fun _ => (1:ℝ))) (unit.prod unit) :=
    (integrable_const (1:ℝ)).indicator (diagonalBand_measurable t)
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _x : ℝ, (2*t) ∂unit := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      intro x
      have he : (fun y : ℝ => (diagonalBand t).indicator (fun _ => (1:ℝ)) (x,y)) =
          {y : ℝ | |x+y-1| ≤ t}.indicator (fun _ => (1:ℝ)) := by
        funext y
        rfl
      change (∫ y : ℝ, (diagonalBand t).indicator (fun _ => (1:ℝ)) (x,y) ∂unit) ≤ 2*t
      rw [he,integral_indicator (by rw [band_section]; exact measurableSet_Icc),integral_const]
      simpa only [smul_eq_mul,mul_one,measureReal_restrict_apply MeasurableSet.univ,univ_inter] using band_section_area x t ht
    _ = _ := by simp

theorem cell_center_error (m : Nat) (_hm : 0 < m) (i : Fin m) (x : ℝ) (hx : x ∈ slice m i) :
    |x-GridCounts.u m i| ≤ (1/(m:ℝ))/2 := by
  have hlo : GridCounts.u m i-(1/(m:ℝ))/2 = (i:ℝ)/m := by
    unfold GridCounts.u
    ring
  have hhi : GridCounts.u m i+(1/(m:ℝ))/2 = ((i:ℝ)+1)/m := by
    unfold GridCounts.u
    ring
  rw [abs_le]
  constructor <;> linarith [hx.1,hx.2]

theorem cell_sum_error (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (v : Vertex m n) (p : Point) (hp : p ∈ cell v) :
    |(p.1+p.2)-(GridCounts.u m v.1+GridCounts.u n v.2)| ≤ GridCounts.rho m n/2 := by
  have hx := cell_center_error m hm v.1 p.1 hp.1
  have hy := cell_center_error n hn v.2 p.2 hp.2
  have he : p.1+p.2-(GridCounts.u m v.1+GridCounts.u n v.2) =
      (p.1-GridCounts.u m v.1)+(p.2-GridCounts.u n v.2) := by ring
  rw [he]
  unfold GridCounts.rho
  have ht := abs_add_le (p.1-GridCounts.u m v.1) (p.2-GridCounts.u n v.2)
  linarith

theorem canonical_cell_band (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (v : Vertex m n) (p : Point) (hp : p ∈ cell v) (b : Bool) :
    |spin (CanonicalField.phase (m:=m) (n:=n) b v)-spin (AntiperiodicThreshold.canonical (!b) p)| ≤
      2*(diagonalBand (GridCounts.rho m n/2)).indicator (fun _ => (1:ℝ)) p := by
  classical
  by_cases hband : p ∈ diagonalBand (GridCounts.rho m n/2)
  · rw [indicator_of_mem hband,mul_one]
    cases h1 : CanonicalField.phase (m:=m) (n:=n) b v <;> cases h2 : AntiperiodicThreshold.canonical (!b) p <;>
      norm_num [spin,h1,h2]
  · rw [indicator_of_notMem hband,mul_zero]
    have he := abs_le.mp (cell_sum_error m n hm hn v p hp)
    have hc : GridCounts.u m v.1+GridCounts.u n v.2 < 1 ↔ p.1+p.2 < 1 := by
      constructor
      · intro hc
        by_contra hn
        have hp1 : 1 ≤ p.1+p.2 := le_of_not_gt hn
        apply hband
        change |p.1+p.2-1| ≤ GridCounts.rho m n/2
        rw [abs_of_nonneg (by linarith)]
        linarith [he.2]
      · intro hp1
        by_contra hn
        have hc1 : 1 ≤ GridCounts.u m v.1+GridCounts.u n v.2 := le_of_not_gt hn
        apply hband
        change |p.1+p.2-1| ≤ GridCounts.rho m n/2
        rw [abs_of_nonpos (by linarith)]
        linarith [he.1]
    have hcolor : CanonicalField.phase (m:=m) (n:=n) b v = AntiperiodicThreshold.canonical (!b) p := by
      by_cases hp1 : p.1+p.2 < 1
      · have hc1 := hc.mpr hp1
        cases b <;> simp [CanonicalField.phase,CanonicalField.canonical,
          AntiperiodicThreshold.canonical,hp1,hc1]
      · have hc1 : ¬GridCounts.u m v.1+GridCounts.u n v.2 < 1 := fun h => hp1 (hc.mp h)
        cases b <;> simp [CanonicalField.phase,CanonicalField.canonical,
          AntiperiodicThreshold.canonical,hp1,hc1]
    rw [hcolor,sub_self,abs_zero]

/-- The actual extension of either cell-center canonical phase differs
from its continuous phase only in a band of area at most rho. -/
theorem canonical_extension_distance (m n : Nat) (hm : 0 < m) (hn : 0 < n) (b : Bool) :
    EnergyLipschitz.distance unit (extension (CanonicalField.phase (m:=m) (n:=n) b))
      (AntiperiodicThreshold.canonical (!b)) ≤ 2*GridCounts.rho m n := by
  let t := GridCounts.rho m n/2
  have ht : 0 ≤ t := div_nonneg (GridCounts.rho_nonneg m n) (by norm_num)
  have hi : Integrable ((diagonalBand t).indicator (fun _ => (1:ℝ))) (unit.prod unit) :=
    (integrable_const (1:ℝ)).indicator (diagonalBand_measurable t)
  calc
    _ ≤ ∫ p : Point, 2*(diagonalBand t).indicator (fun _ => (1:ℝ)) p ∂unit.prod unit := by
      apply integral_mono_ae (EnergyLipschitz.pointDistance_integrable unit _ _
        (extension_measurable _) (AntiperiodicReplacement.canonical_measurable _)) (hi.const_mul 2)
      have hu : ∀ᵐ p ∂unit.prod unit, p ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1 := by
        rw [unit,Measure.prod_restrict,←Measure.volume_eq_prod]
        exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
      filter_upwards [hu] with p hp
      obtain ⟨v,hv⟩ := mem_iUnion.mp ((cell_cover m n hm hn).symm ▸ hp)
      change |spin (extension (CanonicalField.phase (m:=m) (n:=n) b) p)-spin (AntiperiodicThreshold.canonical (!b) p)| ≤ _
      rw [extension_on_cell hm hn (CanonicalField.phase (m:=m) (n:=n) b) v p hv]
      exact canonical_cell_band m n hm hn v p hv b
    _ = 2*(∫ p : Point, (diagonalBand t).indicator (fun _ => (1:ℝ)) p ∂unit.prod unit) := integral_const_mul _ _
    _ ≤ _ := by
      have hb := diagonalBand_integral t ht
      dsimp [t] at hb
      linarith

theorem realSum_const {α : Type*} (xs : List α) (c : ℝ) :
    GridLocalization.realSum xs (fun _ => c) = (xs.length:ℝ)*c := by
  induction xs with
  | nil => simp [GridLocalization.realSum]
  | cons x xs ih => simp only [GridLocalization.realSum,List.length_cons,Nat.cast_add,Nat.cast_one,ih]; ring

/-- The comparison of a whole-objective minimizer with any fixed coloring
uses only the actual unary amplitude and all mn vertices. -/
theorem minimizer_pair_comparison (m n : Nat) (cost : Vertex m n → Bool → ℝ)
    (α : ℝ) (hα : 0 ≤ α)
    (hu : ∀ v, |cost v true-cost v false| ≤ α*((m:ℝ)*n))
    (χ ψ : Vertex m n → Bool)
    (hmin : GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost χ ≤
      GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost ψ) :
    (Q4.monoCount (GridLocalization.gridEdges m n) χ : ℝ) ≤
      (Q4.monoCount (GridLocalization.gridEdges m n) ψ : ℝ)+α*((m:ℝ)*n)^2 := by
  have hpoint (v : Vertex m n) : cost v (ψ v)-cost v (χ v) ≤ α*((m:ℝ)*n) := by
    have hb := abs_le.mp (hu v)
    cases hc : χ v <;> cases hp : ψ v
    · simpa using mul_nonneg hα (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
    · exact hb.2
    · linarith [hb.1]
    · simpa using mul_nonneg hα (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
  have hs := GridLocalization.realSum_le (GridLocalization.gridVertices m n)
    (fun v => cost v (ψ v)-cost v (χ v)) (fun _ => α*((m:ℝ)*n)) (fun v _ => hpoint v)
  rw [GridLocalization.realSum_sub,realSum_const] at hs
  simp only [GridLocalization.gridVertices,Finset.length_toList,Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at hs
  unfold GridLocalization.energy GridLocalization.gridVertices at hmin
  nlinarith

theorem canonical_extension_energy (m n : Nat) (hm : 0 < m) (hn : 0 < n) (b : Bool) :
    energy unit (extension (CanonicalField.phase (m:=m) (n:=n) b)) ≤ 1/12+2*GridCounts.rho m n := by
  have hp := EnergyLipschitz.energy_lipschitz unit
    (extension (CanonicalField.phase (m:=m) (n:=n) b)) (AntiperiodicThreshold.canonical (!b))
    (extension_measurable _) (AntiperiodicReplacement.canonical_measurable _)
  rw [CanonicalEnergy.canonical_energy] at hp
  have hd := canonical_extension_distance m n hm hn b
  linarith [(abs_le.mp hp).2]

/-- Actual continuous energy of the Borel extension of a finite minimizer.
No initial disagreement witness is a hypothesis. -/
theorem minimizer_extension_energy (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Vertex m n → Bool → ℝ) (α a : ℝ) (hα : 0 ≤ α)
    (ha : α+GridCounts.rho m n ≤ a)
    (hu : ∀ v, |cost v true-cost v false| ≤ α*((m:ℝ)*n))
    (χ : Vertex m n → Bool)
    (hmin : ∀ ψ, GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost χ ≤
      GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost ψ) :
    energy unit (extension χ) ≤ 1/12+5*a := by
  let ψ := CanonicalField.phase (m:=m) (n:=n) false
  have hp := minimizer_pair_comparison m n cost α hα hu χ ψ (hmin ψ)
  have hN : 0 < (m:ℝ)*n := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  have hN2 : 0 < ((m:ℝ)*n)^2 := sq_pos_of_pos hN
  have hnorm : normalizedCount χ ≤ normalizedCount ψ+α := by
    rw [normalizedCount_eq_monoCount,normalizedCount_eq_monoCount]
    calc
      _ ≤ ((Q4.monoCount (GridLocalization.gridEdges m n) ψ : ℝ)+α*((m:ℝ)*n)^2)/((m:ℝ)*n)^2 :=
        (div_le_div_iff_of_pos_right hN2).2 hp
      _ = _ := by field_simp
  have hupper := extension_energy_upper m n hm hn χ
  have hlower := extension_energy_lower m n hm hn ψ
  have hcanonical := canonical_extension_energy m n hm hn false
  change energy unit (extension ψ) ≤ 1/12+2*GridCounts.rho m n at hcanonical
  linarith [GridCounts.rho_nonneg m n]

/-- Continuum stability and the actual canonical cell discrepancy imply
the manuscript's initial finite disagreement estimate, without assuming it. -/
theorem initial_disagreement_estimate (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Vertex m n → Bool → ℝ) (α a : ℝ) (hα : 0 ≤ α)
    (ha : α+GridCounts.rho m n ≤ a)
    (hu : ∀ v, |cost v true-cost v false| ≤ α*((m:ℝ)*n))
    (χ : Vertex m n → Bool)
    (hmin : ∀ ψ, GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost χ ≤
      GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost ψ) :
    ∃ b : Bool, ((disagreement χ (CanonicalField.phase b)).card : ℝ)/((m:ℝ)*n) ≤
      2048*(5*a)^(1/72:ℝ)+GridCounts.rho m n := by
  have ha0 : 0 ≤ a := le_trans (add_nonneg hα (GridCounts.rho_nonneg m n)) ha
  have hE := minimizer_extension_energy m n hm hn cost α a hα ha hu χ hmin
  obtain ⟨c,hc⟩ := TwoPhaseStability.two_phase_stability (extension χ) (extension_measurable χ)
    (5*a) (by positivity) hE
  let ψ := CanonicalField.phase (m:=m) (n:=n) (!c)
  have hcanon := canonical_extension_distance m n hm hn (!c)
  simp only [Bool.not_not] at hcanon
  have htri := EnergyLipschitz.distance_triangle unit (extension χ) (AntiperiodicThreshold.canonical c)
    (extension ψ) (extension_measurable χ) (AntiperiodicReplacement.canonical_measurable c) (extension_measurable ψ)
  rw [EnergyLipschitz.distance_symm unit (AntiperiodicThreshold.canonical c) (extension ψ)] at htri
  rw [extension_distance_card m n hm hn χ ψ] at htri
  refine ⟨!c,?_⟩
  change ((disagreement χ ψ).card : ℝ)/((m:ℝ)*n) ≤ _
  change EnergyLipschitz.distance unit (extension ψ) _ ≤ _ at hcanon
  have he : 2*((disagreement χ ψ).card : ℝ)/((m:ℝ)*n) =
      2*(((disagreement χ ψ).card : ℝ)/((m:ℝ)*n)) := by ring
  rw [he] at htri
  linarith

theorem flip_disagreement {m n : Nat} (χ ψ : Vertex m n → Bool) :
    χ = Q4.SimultaneousFlip.flip ψ (GridLocalization.membershipMask (disagreement χ ψ)) := by
  classical
  funext v
  cases hc : χ v <;> cases hp : ψ v <;>
    simp [Q4.SimultaneousFlip.flip,GridLocalization.membershipMask,disagreement,hc,hp]

/-- The initial small disagreement witness follows from the actual finite
objective and the proved continuous theorem. It is not an input premise. -/
theorem minimizer_initial_stability (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Vertex m n → Bool → ℝ) (α a : ℝ) (hα : 0 ≤ α)
    (ha : α+GridCounts.rho m n ≤ a) (hsmall : a ≤ 1/(2:ℝ)^4096)
    (hu : ∀ v, |cost v true-cost v false| ≤ α*((m:ℝ)*n))
    (χ : Vertex m n → Bool)
    (hmin : ∀ ψ, GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost χ ≤
      GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost ψ) :
    ∃ b : Bool, ∃ F : Finset (Vertex m n),
      χ = Q4.SimultaneousFlip.flip (CanonicalField.phase b) (GridLocalization.membershipMask F) ∧
      (F.card : ℝ) ≤ ((m:ℝ)*n)/1048576 := by
  obtain ⟨b,hb⟩ := initial_disagreement_estimate m n hm hn cost α a hα ha hu χ hmin
  have hrho : GridCounts.rho m n ≤ a := by linarith
  have ha0 : 0 ≤ a := le_trans (GridCounts.rho_nonneg m n) hrho
  have hnumeric := GridInitialConstants.initial_fraction_bound a (GridCounts.rho m n) ha0 hrho hsmall
  have hN : 0 < (m:ℝ)*n := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  refine ⟨b,disagreement χ (CanonicalField.phase b),flip_disagreement _ _,?_⟩
  have hbound := (div_le_iff₀ hN).mp (hb.trans hnumeric)
  linarith

set_option exponentiation.threshold 8192

/-- Full finite rectangular-grid localization for an actual whole-objective
minimizer. Neither initial stability nor a field/localization conclusion is
assumed. Signed unary costs are allowed; only their actual oscillation is bounded. -/
theorem minimizer_localization (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Vertex m n → Bool → ℝ) (α a : ℝ) (hα : 0 ≤ α)
    (ha : α+GridCounts.rho m n ≤ a) (hsmall : a ≤ 1/(2:ℝ)^4096)
    (hu : ∀ v, |cost v true-cost v false| ≤ α*((m:ℝ)*n))
    (χ : Vertex m n → Bool)
    (hmin : ∀ ψ, GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost χ ≤
      GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost ψ) :
    ∃ b : Bool, ∃ F : Finset (Vertex m n),
      χ = Q4.SimultaneousFlip.flip (CanonicalField.phase b) (GridLocalization.membershipMask F) ∧
      (F.card : ℝ) ≤ 52*a*((m:ℝ)*n) ∧
      F ⊆ GridCounts.strip m n (220*a) ∪ GridCounts.corners m n (220*a) := by
  exact CanonicalField.minimizer_localization_from_initial_stability m n hm hn cost α a hα ha
    (hsmall.trans (by norm_num)) hu χ hmin
    (minimizer_initial_stability m n hm hn cost α a hα ha hsmall hu χ hmin)

/-- The finite-grid optimum bracket (3.1), now with all continuous-stability,
cell-error, initial-support, canonical-field and finite-graph steps discharged. -/
theorem finite_grid_optimum_interval (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Vertex m n → Bool → ℝ) (α a : ℝ) (hα : 0 ≤ α)
    (ha : α+GridCounts.rho m n ≤ a) (hsmall : a ≤ 1/(2:ℝ)^4096)
    (hu : ∀ v, |cost v true-cost v false| ≤ α*((m:ℝ)*n))
    (χ : Vertex m n → Bool)
    (hmin : ∀ ψ, GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost χ ≤
      GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost ψ) :
    let L := min
      (GridLocalization.phaseEstimate (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost (CanonicalField.phase false))
      (GridLocalization.phaseEstimate (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost (CanonicalField.phase true))
    L - 2^32*a^3*((m:ℝ)*n)^2 ≤ GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost χ ∧
    GridLocalization.energy (GridLocalization.gridVertices m n) (GridLocalization.gridEdges m n) cost χ ≤ L + 2^32*a^3*((m:ℝ)*n)^2 := by
  exact CanonicalField.finite_grid_optimum_interval m n hm hn cost α a hα ha
    (hsmall.trans (by norm_num)) hu χ hmin
    (minimizer_initial_stability m n hm hn cost α a hα ha hsmall hu χ hmin)

end Q4.Candidate.GridStepBridge

#print axioms Q4.Candidate.GridStepBridge.actual_energy_bounds
#print axioms Q4.Candidate.GridStepBridge.extension_distance_card

#print axioms Q4.Candidate.GridStepBridge.canonical_extension_distance

#print axioms Q4.Candidate.GridStepBridge.minimizer_extension_energy
#print axioms Q4.Candidate.GridStepBridge.initial_disagreement_estimate
#print axioms Q4.Candidate.GridStepBridge.minimizer_initial_stability
#print axioms Q4.Candidate.GridStepBridge.minimizer_localization
#print axioms Q4.Candidate.GridStepBridge.finite_grid_optimum_interval
