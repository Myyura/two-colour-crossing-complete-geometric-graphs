import Q4.Candidate.ActualProgramGeometry
import Q4.Candidate.SideDominance

/-! Actual cut ratios, parent sizes, response weights and reference-side
agreements for the computed catalog. -/
namespace Q4.Candidate.ActualCatalogRegime
open Q4.Candidate.ProgramGeometry Q4.Candidate.OriginalVertexLayout
open Q4.Candidate.ActualProgramGeometry Q4.Candidate.ProgramCatalog
open Q4.Candidate.ActualRecipe Q4.Candidate.SideCatalog Q4.Candidate.SideDominance
attribute [local instance] Classical.propDecidable

theorem regime (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0 < n*q) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) : Regime (geometries n q D W B hW hEven pi) late j := by
  have hp := proportions n q D W hD hS hW
  have hc := catalog_cuts n q D W B hW hEven pi j ⟨0,by omega⟩
  cases late
  · refine ⟨(earlyBlock n q D W B hW j).fits.trans' (Nat.le_add_right _ _),?_,hp.2.2.1 _ hc.1⟩
    change (((earlyBlock n q D W B hW j).parent.card:ℝ)/(O n q D W)) ≤ 1/514
    rw [Block.parent_card]
    exact hp.2.1
  · refine ⟨hc.2.2.2.2.1,?_,hp.2.2.2 _ hc.2.2.1⟩
    change (((lateBlock n q D W B hW (latePhysical pi j)).parent.card:ℝ)/(O n q D W)) ≤ 1/514
    rw [Block.parent_card]
    exact hp.2.1

theorem rank_weights (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0 < n*q) (hBO : O n q D W ≤ B) (h8 : 8∣B)
    (pi : Equiv.Perm (Fin n)) (j : Fin (n*q)) :
    (∀i < W-1, 0 < rankLeftWeight (geometries n q D W B hW hEven pi) j i ∧
      rankLeftWeight (geometries n q D W B hW hEven pi) j i ≤ B ∧
      B ≤ 4*rankLeftWeight (geometries n q D W B hW hEven pi) j i) ∧
    (∀i < W-1, 0 < rankRightWeight (geometries n q D W B hW hEven pi) j i ∧
      rankRightWeight (geometries n q D W B hW hEven pi) j i ≤ B ∧
      B ≤ 4*rankRightWeight (geometries n q D W B hW hEven pi) j i) := by
  have hp := proportions n q D W hD hS hW
  have hc (ell : Fin (W-1)) := catalog_cuts n q D W B hW hEven pi j ell
  constructor
  · exact rank_left_bounds _ j hp.1 hBO h8 (fun _ => (earlyBlock n q D W B hW j).fits)
      (fun ell => hp.2.2.1 _ (hc ell).2.1)
  · exact rank_right_bounds _ j hp.1 hBO h8 (fun ell => (hc ell).2.2.2.2.2)
      (fun ell => hp.2.2.2 _ (hc ell).2.2.2.1)

theorem ordinary_weights (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0 < n*q) (hBO : O n q D W ≤ B) (h8 : 8∣B)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ) (j : Fin (n*q)) :
    0 < ordinaryLeftWeight (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) j ∧
    ordinaryLeftWeight (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) j ≤ B ∧
    0 < ordinaryRightWeight (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) j ∧
    ordinaryRightWeight (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) j ≤ B ∧
    (B:ℤ) ≤ 4*ordinaryLeftWeight (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) j ∧
    (B:ℤ) ≤ 4*ordinaryRightWeight (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) j := by
  have hL := regime n q D W B hW hEven hD hS pi false j
  have hR := regime n q D W B hW hEven hD hS pi true j
  exact ordinary_weights_bounds A T (by omega) (sitePermutation pi) _ j
    (selected n q D W B hW hEven hD hS hBO h8 pi A T j ⟨0,by omega⟩ ⟨0,by omega⟩)
    (proportions n q D W hD hS hW).1 hBO h8 hL.cut hR.cut hL.parent hR.parent hL.side hR.side

/-- Every actual late clone lies above every early parent macro, and every
actual early clone lies below every late parent macro. -/
theorem opposite_sides (n q D W B : ℕ) (hW : 2 ≤ W) (j k : Fin (n*q)) (s t : Fin W) :
    (earlyBlock n q D W B hW j).a < parameter n q D W B (lateIndex n q D W k t) ∧
    parameter n q D W B (earlyIndex n q D W j s) < (lateBlock n q D W B hW k).a := by
  have hl := (earlyBlock n q D W B hW j).outside_order hW _ (late_outside_early n q D W B hW k j t)
  have hr := (lateBlock n q D W B hW k).outside_order hW _ (early_outside_late n q D W B hW j k s)
  have hleft := Nat.mul_le_mul_right W (show j.val+1 ≤ n*q by omega)
  have hearly := block_rank_lt n q W j s
  simp only [Nat.add_mul,Nat.one_mul] at hleft
  constructor
  · apply hl.2.mpr
    change j.val*W ≤ n*q*W+D+(k.val*W+t.val)
    omega
  · apply hr.1.mpr
    change j.val*W+s.val < n*q*W+D+k.val*W
    omega

theorem cross_sides (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (j k : Fin (n*q)) (s t : Fin W) :
    (((geometries n q D W B hW hEven pi).ordinaryLeft j).2.a <
      parameter n q D W B (ProposedPalette.lateEndpoint (n*q) W D (sitePermutation pi) k t) ↔
      ((geometries n q D W B hW hEven pi).ordinaryLeft j).2.a <
      parameter n q D W B (ProposedPalette.lateEndpoint (n*q) W D (sitePermutation pi) j ⟨0,by omega⟩)) ∧
    (((geometries n q D W B hW hEven pi).ordinaryRight k).2.a <
      parameter n q D W B (ProposedPalette.earlyEndpoint (n*q) W D (sitePermutation pi) j s) ↔
      ((geometries n q D W B hW hEven pi).ordinaryRight k).2.a <
      parameter n q D W B (ProposedPalette.earlyEndpoint (n*q) W D (sitePermutation pi) k ⟨0,by omega⟩)) := by
  rw [palette_late_index,palette_late_index]
  have hl := (opposite_sides n q D W B hW j (latePhysical pi k) s t).1
  have hl0 := (opposite_sides n q D W B hW j (latePhysical pi j) s ⟨0,by omega⟩).1
  have hr := (opposite_sides n q D W B hW j (latePhysical pi k) s t).2
  have hr0 := (opposite_sides n q D W B hW k (latePhysical pi k) ⟨0,by omega⟩ t).2
  exact ⟨iff_of_true hl hl0,iff_of_false (not_lt_of_gt hr) (not_lt_of_gt hr0)⟩

end Q4.Candidate.ActualCatalogRegime

#print axioms Q4.Candidate.ActualCatalogRegime.regime
#print axioms Q4.Candidate.ActualCatalogRegime.rank_weights
#print axioms Q4.Candidate.ActualCatalogRegime.ordinary_weights
#print axioms Q4.Candidate.ActualCatalogRegime.opposite_sides
#print axioms Q4.Candidate.ActualCatalogRegime.cross_sides
