import Q4.Candidate.ProgramPlacement
import Q4.Candidate.ActualRecipe
import Q4.Candidate.CatalogSupport

/-! The actual selected and nonincident interfaces for the computed recipe,
using the concrete original indices and common geometry scales. -/
namespace Q4.Candidate.ActualProgramGeometry
open Q4.Candidate.ConvexSeparation Q4.Candidate.OriginalVertexLayout
open Q4.Candidate.ProgramGeometry Q4.Candidate.MacroLayout
open Q4.Candidate.GlobalGeometryScales Q4.Candidate.ProgramCatalog
open Q4.Candidate.ProgramCount Q4.Candidate.RankGap Q4.Candidate.SourceChordGeometry
attribute [local instance] Classical.propDecidable

theorem interval_rank_not_mem (a b W s : ℕ) (hs : s < W) (hne : a≠b) :
    ¬(a*W ≤ b*W+s ∧ b*W+s < a*W+W) := by
  intro hh
  rcases lt_or_gt_of_ne hne with h|h
  · have hm := Nat.mul_le_mul_right W (show a+1 ≤ b by omega)
    nlinarith
  · have hm := Nat.mul_le_mul_right W (show b+1 ≤ a by omega)
    nlinarith

theorem early_mem (n q D W B : ℕ) (hW : 2 ≤ W) (j : Fin (n*q)) (s : Fin W) :
    earlyIndex n q D W j s∈(earlyBlock n q D W B hW j).parent := by
  rw [Block.mem_parent]
  change j.val*W ≤ j.val*W+s.val ∧ j.val*W+s.val < j.val*W+W
  omega

theorem late_mem (n q D W B : ℕ) (hW : 2 ≤ W) (j : Fin (n*q)) (s : Fin W) :
    lateIndex n q D W j s∈(lateBlock n q D W B hW j).parent := by
  rw [Block.mem_parent]
  change n*q*W+D+j.val*W ≤ n*q*W+D+(j.val*W+s.val) ∧
    n*q*W+D+(j.val*W+s.val) < n*q*W+D+j.val*W+W
  omega

theorem early_other (n q D W B : ℕ) (hW : 2 ≤ W) (j k : Fin (n*q)) (s : Fin W) (hne : j≠k) :
    earlyIndex n q D W j s∉(earlyBlock n q D W B hW k).parent := by
  rw [Block.mem_parent]
  exact interval_rank_not_mem k.val j.val W s.val s.isLt (by intro h; exact hne (Fin.ext h.symm))

theorem late_other (n q D W B : ℕ) (hW : 2 ≤ W) (j k : Fin (n*q)) (s : Fin W) (hne : j≠k) :
    lateIndex n q D W j s∉(lateBlock n q D W B hW k).parent := by
  rw [Block.mem_parent]
  have hh := interval_rank_not_mem k.val j.val W s.val s.isLt (by intro h; exact hne (Fin.ext h.symm))
  change ¬(n*q*W+D+k.val*W ≤ n*q*W+D+(j.val*W+s.val) ∧
    n*q*W+D+(j.val*W+s.val) < n*q*W+D+k.val*W+W)
  omega

theorem early_outside_late (n q D W B : ℕ) (hW : 2 ≤ W) (j k : Fin (n*q)) (s : Fin W) :
    earlyIndex n q D W j s∉(lateBlock n q D W B hW k).parent := by
  rw [Block.mem_parent]
  have hh := block_rank_lt n q W j s
  change ¬(n*q*W+D+k.val*W ≤ j.val*W+s.val ∧ _)
  omega

theorem late_outside_early (n q D W B : ℕ) (hW : 2 ≤ W) (j k : Fin (n*q)) (s : Fin W) :
    lateIndex n q D W j s∉(earlyBlock n q D W B hW k).parent := by
  rw [Block.mem_parent]
  have hh := Nat.mul_le_mul_right W (show k.val+1 ≤ n*q by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  change ¬(k.val*W ≤ n*q*W+D+(j.val*W+s.val) ∧
    n*q*W+D+(j.val*W+s.val) < k.val*W+W)
  omega

theorem middle_outside (n q D W B : ℕ) (hW : 2 ≤ W) (j : Fin (n*q))
    (i : Fin (O n q D W)) (hi : n*q*W ≤ i.val ∧ i.val < n*q*W+D) :
    i∉(earlyBlock n q D W B hW j).parent ∧ i∉(lateBlock n q D W B hW j).parent := by
  have hh := Nat.mul_le_mul_right W (show j.val+1 ≤ n*q by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  simp only [Block.mem_parent]
  change ¬(j.val*W ≤ i.val ∧ i.val < j.val*W+W) ∧
    ¬(n*q*W+D+j.val*W ≤ i.val ∧ i.val < n*q*W+D+j.val*W+W)
  omega

/-- The curvature margin is a consequence of actual index exclusion from a
parent block, not an assumed noncrossing condition. -/
theorem block_nonincident {n q D W B : ℕ} (b : Block n q D W B) (hW : 2 ≤ W)
    (i j : Fin (O n q D W)) (hi : i∉b.parent) (hj : j∉b.parent) (span : ℚ) (hs : span ≤ 2) :
    1200*programScale (macros n q D) W < |parameter n q D W B i-b.a| * |parameter n q D W B j-b.a| ∧
    200*programScale (macros n q D) W*span < |parameter n q D W B i-b.a| * |parameter n q D W B j-b.a| :=
  nonincident_margins (macros n q D) W B b.a (macroAt n q D W i) (macroAt n q D W j)
    (parameter n q D W B i) (parameter n q D W B j) span b.mem
    (macroAt_mem n q D W hW i) (macroAt_mem n q D W hW j)
    (b.nonparent_macro_ne hW i hi) (b.nonparent_macro_ne hW j hj)
    (parameter_near_macro n q D W B hW i) (parameter_near_macro n q D W B hW j) hs

theorem nonincident_at_indices (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (k : Fin (n*q)) (i j : Fin (O n q D W))
    (hiL : i∉(earlyBlock n q D W B hW k).parent) (hjL : j∉(earlyBlock n q D W B hW k).parent)
    (hiR : i∉(lateBlock n q D W B hW (latePhysical pi k)).parent)
    (hjR : j∉(lateBlock n q D W B hW (latePhysical pi k)).parent) :
    Nonincident (geometries n q D W B hW hEven pi) k (parameter n q D W B i) (parameter n q D W B j) := by
  have hs : (lateBlock n q D W B hW (latePhysical pi k)).a-(earlyBlock n q D W B hW k).a ≤ 2 := by
    linarith [(abs_le.mp (lateBlock n q D W B hW (latePhysical pi k)).unit_a).2,
      (abs_le.mp (earlyBlock n q D W B hW k).unit_a).1]
  have hL := block_nonincident (earlyBlock n q D W B hW k) hW i j hiL hjL _ hs
  have hR := block_nonincident (lateBlock n q D W B hW (latePhysical pi k)) hW i j hiR hjR _ hs
  exact ⟨hL.1,hR.1,fun _ => hL.2,fun _ => hR.2⟩

theorem selected_other_nonincident (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (j k : Fin (n*q)) (s t : Fin W) (hne : k≠j) :
    Nonincident (geometries n q D W B hW hEven pi) k
      (parameter n q D W B (earlyIndex n q D W j s))
      (parameter n q D W B (lateIndex n q D W (latePhysical pi j) t)) :=
  nonincident_at_indices n q D W B hW hEven pi k _ _
    (early_other n q D W B hW j k s hne.symm)
    (late_outside_early n q D W B hW _ k t)
    (early_outside_late n q D W B hW j _ s)
    (late_other n q D W B hW _ _ t (by intro h; exact hne ((latePhysical pi).injective h).symm))

theorem dummy_nonincident (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (k : Fin (n*q)) (i j : Fin (O n q D W))
    (hi : n*q*W ≤ i.val ∧ i.val < n*q*W+D) (hj : n*q*W ≤ j.val ∧ j.val < n*q*W+D) :
    Nonincident (geometries n q D W B hW hEven pi) k (parameter n q D W B i) (parameter n q D W B j) :=
  nonincident_at_indices n q D W B hW hEven pi k i j
    (middle_outside n q D W B hW k i hi).1 (middle_outside n q D W B hW k j hj).1
    (middle_outside n q D W B hW _ i hi).2 (middle_outside n q D W B hW _ j hj).2

theorem selected_indices (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0 < n*q) (hBO : O n q D W ≤ B) (h8 : 8∣B)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ) (j : Fin (n*q)) (s t : Fin W) :
    Selected (ActualRecipe.recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi))
      (geometries n q D W B hW hEven pi) j W s t
      (parameter n q D W B (earlyIndex n q D W j s))
      (parameter n q D W B (lateIndex n q D W (latePhysical pi j) t)) := by
  let g := geometries n q D W B hW hEven pi
  have hp := proportions n q D W hD hS hW
  have hcuts (ell : Fin (W-1)) := catalog_cuts n q D W B hW hEven pi j ell
  refine {
    unit_c := parameter_abs n q D W B hW _
    unit_b := parameter_abs n q D W B hW _
    ordinary_left_clone := (g.ordinaryLeft j).2.clone _ (early_mem n q D W B hW j s)
    ordinary_left_sep := (g.ordinaryLeft j).2.sep _ (late_outside_early n q D W B hW _ j t)
    ordinary_right_clone := (g.ordinaryRight j).2.clone _ (late_mem n q D W B hW _ t)
    ordinary_right_sep := (g.ordinaryRight j).2.sep _ (early_outside_late n q D W B hW j _ s)
    left_width := fun _ => rfl
    left_gap := fun _ => rfl
    left_c := fun _ => parameter_early n q D W B hW j s
    left_b := fun _ => parameter_late n q D W B hW _ t
    right_width := fun _ => rfl
    right_gap := fun _ => rfl
    right_c := fun _ => parameter_early n q D W B hW j s
    right_b := fun _ => parameter_late n q D W B hW _ t
    left_weight := ?_
    right_weight := ?_ }
  · intro ell
    exact ActualRecipe.selected_left_weight A T (by omega) (sitePermutation pi) g j ell hp.1 hBO h8
      (earlyBlock n q D W B hW j).fits (hp.2.2.1 _ (hcuts ell).2.1)
  · intro ell
    exact ActualRecipe.selected_right_weight A T (by omega) (sitePermutation pi) g j ell hp.1 hBO h8
      (hcuts ell).2.2.2.2.2 (hp.2.2.2 _ (hcuts ell).2.2.2.1)

theorem palette_late_index (n q D W : ℕ) (pi : Equiv.Perm (Fin n)) (j : Fin (n*q)) (t : Fin W) :
    ProposedPalette.lateEndpoint (n*q) W D (sitePermutation pi) j t=
      lateIndex n q D W (latePhysical pi j) t := by
  apply Fin.ext
  simp only [ProposedPalette.lateEndpoint,PaletteCounting.endpoint,sitePermutation,
    Equiv.symm_symm,lateIndex,Fin.val_mk]
  omega

/-- The exact Selected record consumed by ActualRecipe.selected_residual is
proved for every actual selected core edge and its actual computed weights. -/
theorem selected (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0 < n*q) (hBO : O n q D W ≤ B) (h8 : 8∣B)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ) (j : Fin (n*q)) (s t : Fin W) :
    Selected (ActualRecipe.recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi))
      (geometries n q D W B hW hEven pi) j W s t
      (parameter n q D W B (ProposedPalette.earlyEndpoint (n*q) W D (sitePermutation pi) j s))
      (parameter n q D W B (ProposedPalette.lateEndpoint (n*q) W D (sitePermutation pi) j t)) := by
  rw [palette_late_index]
  exact selected_indices n q D W B hW hEven hD hS hBO h8 pi A T j s t

theorem selected_other (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (j k : Fin (n*q)) (s t : Fin W) (hne : k≠j) :
    Nonincident (geometries n q D W B hW hEven pi) k
      (parameter n q D W B (ProposedPalette.earlyEndpoint (n*q) W D (sitePermutation pi) j s))
      (parameter n q D W B (ProposedPalette.lateEndpoint (n*q) W D (sitePermutation pi) j t)) := by
  rw [palette_late_index]
  exact selected_other_nonincident n q D W B hW hEven pi j k s t hne

theorem cross_support_indices (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (j k : Fin (n*q)) (s t : Fin W) :
    CatalogSupport.CrossSupport (geometries n q D W B hW hEven pi) j k
      (parameter n q D W B (earlyIndex n q D W j s))
      (parameter n q D W B (lateIndex n q D W (latePhysical pi k) t)) := by
  let g := geometries n q D W B hW hEven pi
  have hs (l : Fin (n*q)) :
      (lateBlock n q D W B hW (latePhysical pi l)).a-(earlyBlock n q D W B hW l).a ≤ 2 := by
    linarith [(abs_le.mp (lateBlock n q D W B hW (latePhysical pi l)).unit_a).2,
      (abs_le.mp (earlyBlock n q D W B hW l).unit_a).1]
  have hL (l : Fin (n*q)) (hl : l≠j) := block_nonincident (earlyBlock n q D W B hW l) hW
    (earlyIndex n q D W j s) (lateIndex n q D W (latePhysical pi k) t)
    (early_other n q D W B hW j l s hl.symm)
    (late_outside_early n q D W B hW _ l t) _ (hs l)
  have hR (l : Fin (n*q)) (hl : l≠k) := block_nonincident (lateBlock n q D W B hW (latePhysical pi l)) hW
    (earlyIndex n q D W j s) (lateIndex n q D W (latePhysical pi k) t)
    (early_outside_late n q D W B hW j _ s)
    (late_other n q D W B hW _ _ t (by intro he; exact hl ((latePhysical pi).injective he).symm)) _ (hs l)
  exact {
    unit_c := parameter_abs n q D W B hW _
    unit_b := parameter_abs n q D W B hW _
    left_clone := (g.ordinaryLeft j).2.clone _ (early_mem n q D W B hW j s)
    left_sep := (g.ordinaryLeft j).2.sep _ (late_outside_early n q D W B hW _ j t)
    right_clone := (g.ordinaryRight k).2.clone _ (late_mem n q D W B hW _ t)
    right_sep := (g.ordinaryRight k).2.sep _ (early_outside_late n q D W B hW j _ s)
    other_ordinary_left := fun l hl => (hL l hl).1
    other_ordinary_right := fun l hl => (hR l hl).1
    other_rank_left := fun l hl _ => (hL l hl).2
    other_rank_right := fun l hl _ => (hR l hl).2 }

theorem cross_support (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (j k : Fin (n*q)) (s t : Fin W) :
    CatalogSupport.CrossSupport (geometries n q D W B hW hEven pi) j k
      (parameter n q D W B (ProposedPalette.earlyEndpoint (n*q) W D (sitePermutation pi) j s))
      (parameter n q D W B (ProposedPalette.lateEndpoint (n*q) W D (sitePermutation pi) k t)) := by
  rw [palette_late_index]
  exact cross_support_indices n q D W B hW hEven pi j k s t

end Q4.Candidate.ActualProgramGeometry

#print axioms Q4.Candidate.ActualProgramGeometry.block_nonincident
#print axioms Q4.Candidate.ActualProgramGeometry.nonincident_at_indices
#print axioms Q4.Candidate.ActualProgramGeometry.selected_other_nonincident
#print axioms Q4.Candidate.ActualProgramGeometry.dummy_nonincident
#print axioms Q4.Candidate.ActualProgramGeometry.selected_indices
#print axioms Q4.Candidate.ActualProgramGeometry.selected
#print axioms Q4.Candidate.ActualProgramGeometry.selected_other
#print axioms Q4.Candidate.ActualProgramGeometry.cross_support
