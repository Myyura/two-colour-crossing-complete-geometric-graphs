import Q4.Candidate.ActualCatalogBounds
import Q4.Candidate.CatalogTargets

/-! The actual finite Label cardinality is bounded from the computed fields,
ceil ordinary counts and greedy rank counts. No catalog-size, offset,
response-weight or target premise remains in the final theorem. -/
namespace Q4.Candidate.ActualCatalogParameters
open Q4.Candidate.ProgramGeometry Q4.Candidate.ProgramCatalog
open Q4.Candidate.OriginalVertexLayout Q4.Candidate.ActualRecipe
open Q4.Candidate.CatalogTargets Q4.Candidate.FreezingParameters
attribute [local irreducible] scale originals frames

/-- Fixed H,W,D,B,A,T and the true geometric response fields discharge every
hypothesis of the actual four-family counting bound (5.16). -/
theorem actual_count (n q D W B : ℕ) (hS : 0<n*q)
    (hWval : W=(scale (n*q))^4) (hD : D=512*(n*q)*W) (hBval : B=frames (n*q))
    (hW : 2≤W) (hEven : Even B) (pi : Equiv.Perm (Fin n)) :
    (Fintype.card (ProgramCount.Label
      (recipe (amplitude (n*q) (O n q D W)) (increment (O n q D W)) (by omega) (sitePermutation pi)
        (geometries n q D W B hW hEven pi)) (W-1)):ℝ)≤
      (2:ℝ)^80*((n*q:ℝ)+1)^4*(scale (n*q):ℝ)^3 := by
  let g := geometries n q D W B hW hEven pi
  let A := amplitude (n*q) (O n q D W)
  let T := increment (O n q D W)
  let d := recipe A T (by omega) (sitePermutation pi) g
  have hdims := dimensions n q D W B hS hWval hD hBval
  have hOeq : O n q D W=originals (n*q) := by
    dsimp [O]; rw [hD,hWval]; unfold originals; ring
  have hB : 0<B := by omega
  have hDlarge : 2*(n*q)*W<D := by
    rw [hD]; have hp := Nat.mul_pos hS (show 0<W by omega); nlinarith
  have hw := ActualCatalogRegime.rank_weights n q D W B hW hEven hD hS hdims.2.2.1 hdims.2.2.2.2 pi
  have ho := ActualCatalogRegime.ordinary_weights n q D W B hW hEven hD hS hdims.2.2.1 hdims.2.2.2.2 pi A T
  have hpal := palette_affine hS (show 0<W by omega) (sitePermutation pi) g.ys
    (parameter_strictMono n q D W B hW) hDlarge
  have hoff (j : Fin (n*q)) : |d.offset j|≤4*(O n q D W:ℚ)^2 :=
    CatalogDominance.offset_bound A T hS (by omega) (sitePermutation pi) g
      (parameter_strictMono n q D W B hW) hDlarge j hB (by have hh := hdims.2.2.2.1; omega)
      (fun i hi => ⟨((hw j).2 i hi).1,((hw j).2 i hi).2.1⟩)
  have ht (j : Fin (n*q)) := target_bounds (n*q) (O n q D W) j (d.offset j) (hoff j)
  have hcount := catalog_scale_bound d (W-1) (show 1≤n*q by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [Nat.cast_mul] using hcount
  · change (amplitude (n*q) (O n q D W):ℚ)=(2:ℚ)^26*((n*q:ℕ)+1)*(originals (n*q):ℚ)^2
    unfold amplitude
    rw [hOeq]
    push_cast
    ring
  · rw [←hWval]; omega
  · intro j
    exact ⟨(ht j).1,(ht j).2.1⟩
  · intro j
    exact ⟨(ht j).2.2.1,(ht j).2.2.2⟩
  · intro j
    change (frames (n*q):ℚ)/4≤(ordinaryLeftWeight (by omega) (sitePermutation pi) g j:ℚ)
    have hh : (B:ℚ)≤4*(ordinaryLeftWeight (by omega) (sitePermutation pi) g j:ℚ) := by
      exact_mod_cast (ho j).2.2.2.2.1
    rw [←hBval]
    linarith
  · intro j
    change (frames (n*q):ℚ)/4≤(ordinaryRightWeight (by omega) (sitePermutation pi) g j:ℚ)
    have hh : (B:ℚ)≤4*(ordinaryRightWeight (by omega) (sitePermutation pi) g j:ℚ) := by
      exact_mod_cast (ho j).2.2.2.2.2
    rw [←hBval]
    linarith
  · intro j
    exact (hpal j).1.trans_eq hOeq
  · intro j
    exact (hpal j).2.1.trans_eq hOeq
  · intro j i hi
    change 0<rankLeftWeight g j i ∧ rankLeftWeight g j i≤frames (n*q) ∧ frames (n*q)≤4*rankLeftWeight g j i
    rw [←hBval]
    exact (hw j).1 i hi
  · intro j i hi
    change 0<rankRightWeight g j i ∧ rankRightWeight g j i≤frames (n*q) ∧ frames (n*q)≤4*rankRightWeight g j i
    rw [←hBval]
    exact (hw j).2 i hi

end Q4.Candidate.ActualCatalogParameters
#print axioms Q4.Candidate.ActualCatalogParameters.actual_count
