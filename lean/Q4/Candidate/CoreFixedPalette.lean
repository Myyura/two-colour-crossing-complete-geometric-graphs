import Q4.Candidate.CoreReducedPairs
import Q4.Candidate.CompleteClassEnergy
import Q4.Candidate.DummyPaletteField

/-! Exact projection of the entire actual C objective after its palette is
fixed. Mixed palette/free crossing costs become the true palette unary. -/
namespace Q4.Candidate.CoreFixedPalette
open Q4.Candidate.CompleteDrawing Q4.Candidate.CompleteGridEnergy
open Q4.Candidate.CompleteClassEnergy Q4.Candidate.ConvexSeparation
open Q4.Candidate.ProposedPalette Q4.Candidate.PaletteCounting
open Q4.Candidate.CoreLocalGeometry Q4.Candidate.CoreReducedPairs
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem halfSum_partition {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (w : α → α → ℝ) (hsym : ∀ x y, w x y=w y x) :
    halfSum w =
      halfSum (fun x y => if p x ∧ p y then w x y else 0) +
      (∑ x : α, if ¬p x then (∑ y : α, if p y then w x y else 0) else 0) +
      halfSum (fun x y => if ¬p x ∧ ¬p y then w x y else 0) := by
  have hw (x y : α) : w x y =
      (if p x ∧ p y then w x y else 0) +
      (if p x ∧ ¬p y then w x y else 0) +
      (if ¬p x ∧ p y then w x y else 0) +
      (if ¬p x ∧ ¬p y then w x y else 0) := by
    by_cases hx : p x <;> by_cases hy : p y <;> simp [hx,hy]
  have hsum : (∑ x : α, ∑ y : α, w x y) =
      (∑ x : α, ∑ y : α,
        ((if p x ∧ p y then w x y else 0) +
         (if p x ∧ ¬p y then w x y else 0) +
         (if ¬p x ∧ p y then w x y else 0) +
         (if ¬p x ∧ ¬p y then w x y else 0))) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hw x y
  have hmix : (∑ x : α, ∑ y : α, if p x ∧ ¬p y then w x y else 0) =
      ∑ x : α, ∑ y : α, if ¬p x ∧ p y then w x y else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [and_comm,hsym y x]
  have hmask : (∑ x : α, if ¬p x then (∑ y : α, if p y then w x y else 0) else 0) =
      ∑ x : α, ∑ y : α, if ¬p x ∧ p y then w x y else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : p x <;> simp [hx]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hmix] at hsum
  rw [hmask]
  unfold halfSum
  linarith

variable {O B P S : ℕ}

noncomputable def paletteBaseline (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (chi : Edge O B P → Bool) : ℝ :=
  halfSum (fun e f : Inner O => if e ∈ palette site ∧ f ∈ palette site then
    weight ys ts rs chi (C e) (C f) else 0) +
  ∑ e : Inner O, if e ∈ palette site then coreUnary ys ts rs chi e (chi (C e)) else 0

noncomputable def freeUnary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (chi : Edge O B P → Bool) (e : Inner O) (bit : Bool) : ℝ :=
  (globalCost ys site e.val.1 e.val.2 bit : ℝ) + coreUnary ys ts rs chi e bit

noncomputable def freePairHalf (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (chi : Edge O B P → Bool) : ℝ :=
  halfSum (fun e f : Inner O => if e ∉ palette site ∧ f ∉ palette site then
    weight ys ts rs chi (C e) (C f) else 0)

theorem palette_neighbor_cost (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (chi : Edge O B P → Bool)
    (hp : ∀e∈palette site, chi (C e)=paletteBit site e) (e : Inner O) :
    (∑ f : Inner O, if f ∈ palette site then weight ys ts rs chi (C e) (C f) else 0) =
      (globalCost ys site e.val.1 e.val.2 (chi (C e)) : ℝ) := by
  unfold globalCost
  push_cast
  rw [←Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro f hf
  have hh := hp f hf
  unfold weight
  rw [hh]
  have hx : Cross ys ts rs (C e) (C f) ↔
      OriginalCapAlternation.cross ys e.val.1 e.val.2 f.val.1 f.val.2 := Iff.rfl
  simp only [hx]
  split_ifs <;> simp_all

theorem core_fixed_palette_decomposition (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (chi : Edge O B P → Bool)
    (hp : ∀e∈palette site, chi (C e)=paletteBit site e) :
    coreCost ys ts rs chi = paletteBaseline ys ts rs site chi + freePairHalf ys ts rs site chi +
      ∑ e : Inner O, if e ∉ palette site then freeUnary ys ts rs site chi e (chi (C e)) else 0 := by
  rw [coreCost_eq_pair_unary,halfSum_partition (fun e : Inner O => e ∈ palette site) _
    (fun e f => weight_symm ys ts rs chi (C e) (C f))]
  simp_rw [palette_neighbor_cost ys ts rs site chi hp]
  have hu : (∑ e : Inner O, coreUnary ys ts rs chi e (chi (C e))) =
      (∑ e : Inner O, if e ∈ palette site then coreUnary ys ts rs chi e (chi (C e)) else 0) +
      (∑ e : Inner O, if e ∉ palette site then coreUnary ys ts rs chi e (chi (C e)) else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e ∈ palette site <;> simp [he]
  rw [hu]
  unfold paletteBaseline freePairHalf freeUnary
  have hs (e : Inner O) :
      (if e ∉ palette site then (globalCost ys site e.val.1 e.val.2 (chi (C e)) : ℝ) +
        coreUnary ys ts rs chi e (chi (C e)) else 0) =
      (if e ∉ palette site then (globalCost ys site e.val.1 e.val.2 (chi (C e)) : ℝ) else 0) +
      (if e ∉ palette site then coreUnary ys ts rs chi e (chi (C e)) else 0) := by
    by_cases he : e ∈ palette site <;> simp [he]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  ring


theorem ordered_halfSum {α : Type*} [Fintype α] (w : α → α → ℝ)
    (hsym : ∀e f, w e f=w f e) (hzero : ∀e, w e e=0) :
    halfSum w = ∑ e, ∑ f, if Fintype.equivFin α e < Fintype.equivFin α f then w e f else 0 := by
  have hs (e f : α) : w e f =
      (if Fintype.equivFin α e < Fintype.equivFin α f then w e f else 0)+
      (if Fintype.equivFin α f < Fintype.equivFin α e then w f e else 0) := by
    rcases lt_trichotomy (Fintype.equivFin α e) (Fintype.equivFin α f) with h|h|h
    · simp [h,not_lt_of_ge (le_of_lt h)]
    · have he := (Fintype.equivFin α).injective h
      subst f
      simp [hzero]
    · simp [h,not_lt_of_ge (le_of_lt h),hsym]
  have ht : (∑ e, ∑ f, w e f) = 2*(∑ e, ∑ f,
      if Fintype.equivFin α e < Fintype.equivFin α f then w e f else 0) := by
    conv_lhs => arg 2; ext e; arg 2; ext f; rw [hs]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f:=fun e f => if Fintype.equivFin α f < Fintype.equivFin α e then w f e else 0)]
    ring
  unfold halfSum
  rw [ht]
  ring

theorem freePairHalf_eq_actual_pairs (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (chi : Edge O B P → Bool) :
    freePairHalf ys ts rs site chi = (pairEnergy (freePairs ys site) (fun e => chi (C e)) : ℝ) := by
  unfold freePairHalf
  rw [ordered_halfSum _
    (by intro e f; simp only [and_comm,weight_symm ys ts rs chi (C e) (C f)])
    (by intro e; simp)]
  unfold pairEnergy freePairs
  push_cast
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  have hx : Cross ys ts rs (C e) (C f) ↔
      OriginalCapAlternation.cross ys e.val.1 e.val.2 f.val.1 f.val.2 := Iff.rfl
  unfold weight edgeRank
  simp only [hx,Fin.lt_def]
  split_ifs <;> simp_all

/-- Exact C-cost for every palette-respecting coloring, with all actual
completion costs retained as palette baseline, true unaries, or one of the
three exhaustive free-pair classes. -/
theorem indexed_full_core_decomposition (S W D B P : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (chi : Edge (S*W+D+S*W) B P → Bool)
    (hp : ∀e∈palette (indexedSite S W D hW pi), chi (C e)=paletteBit (indexedSite S W D hW pi) e) :
    let site := indexedSite S W D hW pi
    coreCost ys ts rs chi = paletteBaseline ys ts rs site chi +
      (pairEnergy (allLocalPairs ys site) (fun e => chi (C e)) : ℝ) +
      (pairEnergy (mainPairs ys site) (fun e => chi (C e)) : ℝ) +
      (pairEnergy (dummyPairs ys site) (fun e => chi (C e)) : ℝ) +
      ∑ e : Inner (S*W+D+S*W), if e ∉ palette site then freeUnary ys ts rs site chi e (chi (C e)) else 0 := by
  dsimp only
  rw [core_fixed_palette_decomposition ys ts rs _ chi hp,freePairHalf_eq_actual_pairs,
    free_energy_decomposition S W D hW pi ys hy]
  push_cast
  ring

/-- The computed palette baseline depends only on its fixed palette bits
and frozen T colors, never on a source, short, or dummy color. -/
theorem paletteBaseline_congr (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (chi psi : Edge O B P → Bool)
    (hpal : ∀e∈palette site, chi (C e)=psi (C e))
    (hT : ∀t : Fin B×Fin P, chi (T t)=psi (T t)) :
    paletteBaseline ys ts rs site chi = paletteBaseline ys ts rs site psi := by
  unfold paletteBaseline halfSum
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    by_cases he : e ∈ palette site
    · by_cases hf : f ∈ palette site
      · simp [he,hf,weight,hpal e he,hpal f hf]
      · simp [he,hf]
    · simp [he]
  · apply Finset.sum_congr rfl
    intro e _
    by_cases he : e ∈ palette site
    · simp only [he,ite_true]
      unfold coreUnary
      simp only [hpal e he,hT]
    · simp [he]

theorem freeUnary_congr_T (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (chi psi : Edge O B P → Bool)
    (hT : ∀t : Fin B×Fin P, chi (T t)=psi (T t)) (e : Inner O) (b : Bool) :
    freeUnary ys ts rs site chi e b = freeUnary ys ts rs site psi e b := by
  unfold freeUnary coreUnary
  simp only [hT]

end Q4.Candidate.CoreFixedPalette
#print axioms Q4.Candidate.CoreFixedPalette.halfSum_partition
#print axioms Q4.Candidate.CoreFixedPalette.palette_neighbor_cost
#print axioms Q4.Candidate.CoreFixedPalette.core_fixed_palette_decomposition

#print axioms Q4.Candidate.CoreFixedPalette.freePairHalf_eq_actual_pairs
#print axioms Q4.Candidate.CoreFixedPalette.indexed_full_core_decomposition
#print axioms Q4.Candidate.CoreFixedPalette.paletteBaseline_congr
#print axioms Q4.Candidate.CoreFixedPalette.freeUnary_congr_T
