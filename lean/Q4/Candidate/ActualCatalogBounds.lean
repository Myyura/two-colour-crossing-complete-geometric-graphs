import Q4.Candidate.ActualCatalogRegime
import Q4.Candidate.ActualSideGeometry
import Q4.Candidate.PaletteExhaustion
import Q4.Candidate.IndexedPaletteForcing

/-! Every actual palette edge is forced in every minimum of the full actual
core objective. All geometry, responses, rank weights and endpoint classes
are instantiated on the concrete source-clone/dummy layout. -/
namespace Q4.Candidate.ActualCatalogBounds
open Q4.Candidate.ConvexSeparation Q4.Candidate.ProgramGeometry
open Q4.Candidate.ProgramCatalog Q4.Candidate.OriginalVertexLayout
open Q4.Candidate.ProposedPalette Q4.Candidate.ActualRecipe
open Q4.Candidate.ActualSideGeometry
open scoped BigOperators

theorem field_reverse {S gaps B N : ℕ} (d : ProgramCount.Recipe S) (ys : Fin N→ℚ)
    (ps : ProgramCount.Label d gaps→Point) (u v : Fin N) :
    ProgramField.field (B:=B) d ys ps (original (ys u)) (original (ys v))=
    ProgramField.field (B:=B) d ys ps (original (ys v)) (original (ys u)) := by
  unfold ProgramField.field
  apply Finset.sum_congr rfl
  intro i _
  exact ProgramCatalog.coefficient_reverse _ _ _ _

theorem pair_dominance (n q D W B : ℕ) (hW : 2≤W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0<n*q) (hBO : O n q D W≤B) (h8 : 8∣B)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ)
    (p : Placement (recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi))
      (geometries n q D W B hW hEven pi))
    (hBscale : 1024*B≤(O n q D W)^2)
    (hA : 8*(O n q D W:ℤ)^2≤A) (hT : 5*(O n q D W:ℤ)^2<T)
    (u v : Fin (O n q D W))
    (huv : allowed (indexedSite (n*q) W D (by omega) (sitePermutation pi) u)
      (indexedSite (n*q) W D (by omega) (sitePermutation pi) v)) :
    (O n q D W:ℚ)^2/2 <
      if color (indexedSite (n*q) W D (by omega) (sitePermutation pi) u)
        (indexedSite (n*q) W D (by omega) (sitePermutation pi) v) then
        -(ProgramField.field (B:=B) (recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi))
          (parameter n q D W B) p.points (original (parameter n q D W B u)) (original (parameter n q D W B v)):ℚ)
      else (ProgramField.field (B:=B) (recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi))
          (parameter n q D W B) p.points (original (parameter n q D W B u)) (original (parameter n q D W B v)):ℚ) := by
  let g := geometries n q D W B hW hEven pi
  let d := recipe A T (by omega) (sitePermutation pi) g
  let ys := parameter n q D W B
  let site := indexedSite (n*q) W D (by omega) (sitePermutation pi)
  let Q (u v : Fin (O n q D W)) : Prop := (O n q D W:ℚ)^2/2 <
    if color (site u) (site v) then -(ProgramField.field (B:=B) d ys p.points (original (ys u)) (original (ys v)):ℚ)
    else (ProgramField.field (B:=B) d ys p.points (original (ys u)) (original (ys v)):ℚ)
  have hO := (proportions n q D W hD hS hW).1
  have hB : 0<B := by omega
  have hDlarge : 2*(n*q)*W<D := by rw [hD]; have hp := Nat.mul_pos hS (show 0<W by omega); nlinarith
  have hscale : 514*W≤O n q D W := by
    have hh := Nat.mul_le_mul_right W (show 1≤n*q by omega)
    dsimp [O]; rw [hD]; nlinarith
  have hT0 : 0≤T := by nlinarith [sq_nonneg (O n q D W:ℤ)]
  have hw := ActualCatalogRegime.rank_weights n q D W B hW hEven hD hS hBO h8 pi
  have ho := ActualCatalogRegime.ordinary_weights n q D W B hW hEven hD hS hBO h8 pi A T
  have hside (late : Bool) (parents : Finset (Fin (n*q))) (hne : parents.Nonempty) (hc : parents.card≤2)
      (a b : Fin (O n q D W)) (hsup : SideCatalog.Support g late parents (ys a) (ys b)) :
      (O n q D W:ℚ)^2/2 < (SideCatalog.sign late:ℚ)*
        (ProgramField.field (B:=B) d ys p.points (original (ys a)) (original (ys b)):ℚ) := by
    apply SideDominance.dominance A T hS (by omega) (sitePermutation pi) g
      (parameter_strictMono n q D W B hW) hDlarge p late parents hne hc _ _ hsup
      (p.original_mem a) (p.original_mem b)
      (fun j _ => ActualCatalogRegime.regime n q D W B hW hEven hD hS pi late j)
      hO hBO h8 hscale hBscale hA hT0
      (fun j _ => (hw j).1) (fun j _ => (hw j).2)
    · intro j _; cases late
      · exact (ho j).1
      · exact (ho j).2.2.1
    · intro j _; cases late
      · exact (ho j).2.1
      · exact (ho j).2.2.2.1
  have he (j : Fin (n*q)) (s : Fin W) : site (earlyEndpoint (n*q) W D (sitePermutation pi) j s)=.early j :=
    site_endpoint_early site j (indexed_fibers (n*q) W D (by omega) (sitePermutation pi) j) _ s
  have hl (j : Fin (n*q)) (s : Fin W) : site (lateEndpoint (n*q) W D (sitePermutation pi) j s)=.late j :=
    site_endpoint_late site j (indexed_fibers (n*q) W D (by omega) (sitePermutation pi) j) _ s
  change Q u v
  apply PaletteExhaustion.all_allowed (n*q) W D (by omega) (sitePermutation pi) Q ?_ ?_ ?_ ?_ ?_ ?_ u v huv
  · intro a b hab
    dsimp [Q] at hab ⊢
    rw [color_symm (site b) (site a),field_reverse d ys p.points b a]
    exact hab
  · intro j k s t hjk
    have hs := side_pair_support n q D W B hW hEven pi false j k s t hjk
    simp only [sideIndex_eq_palette,Bool.false_eq_true,ite_false] at hs
    have hh := hside false {j,k} (by simp) (by exact (Finset.card_insert_le _ _).trans (by simp)) _ _ hs
    simpa only [Q,he,color,SideCatalog.sign,Bool.false_eq_true,ite_false,Int.cast_one,one_mul] using hh
  · intro j k s t hjk
    have hs := side_pair_support n q D W B hW hEven pi true j k s t hjk
    simp only [sideIndex_eq_palette,ite_true] at hs
    have hh := hside true {j,k} (by simp) (by exact (Finset.card_insert_le _ _).trans (by simp)) _ _ hs
    simpa only [Q,hl,color,SideCatalog.sign,ite_true,Int.cast_neg,Int.cast_one,neg_one_mul] using hh
  · intro j k s t hjk
    have hsides := ActualCatalogRegime.cross_sides n q D W B hW hEven pi j k s t
    have hh := CatalogDominance.cross_dominance A T hS (by omega) (sitePermutation pi) g
      (parameter_strictMono n q D W B hW) hDlarge p j k hjk _ _
      (ActualProgramGeometry.cross_support n q D W B hW hEven pi j k s t)
      (p.original_mem _) (p.original_mem _)
      (ActualProgramGeometry.selected n q D W B hW hEven hD hS hBO h8 pi A T j ⟨0,by omega⟩ ⟨0,by omega⟩)
      (ActualProgramGeometry.selected n q D W B hW hEven hD hS hBO h8 pi A T k ⟨0,by omega⟩ ⟨0,by omega⟩)
      hsides.1 hsides.2 hscale hB hBscale hA hT (hw j).1
      (fun i hi => ⟨((hw j).2 i hi).1,((hw j).2 i hi).2.1⟩) (hw k).2
      (ho j).1 (ho j).2.1 (ho k).2.2.1 (ho k).2.2.2.1
    dsimp [Q]
    rw [he,hl]
    simp only [color]
    by_cases hjlt : j<k
    · simp only [hjlt,ite_true,decide_true] at hh ⊢
      change (ProgramField.field (B:=B) d ys p.points
        (original (ys (earlyEndpoint (n*q) W D (sitePermutation pi) j s)))
        (original (ys (lateEndpoint (n*q) W D (sitePermutation pi) k t))):ℚ)< -((O n q D W:ℚ)^2/2) at hh
      linarith
    · simp only [hjlt,ite_false,decide_false,Bool.false_eq_true] at hh ⊢
      change (O n q D W:ℚ)^2/2<(ProgramField.field (B:=B) d ys p.points
        (original (ys (earlyEndpoint (n*q) W D (sitePermutation pi) j s)))
        (original (ys (lateEndpoint (n*q) W D (sitePermutation pi) k t))):ℚ) at hh
      exact hh
  · intro j s i hi
    have hs := side_dummy_support n q D W B hW hEven pi false j s i hi
    simp only [sideIndex_eq_palette,Bool.false_eq_true,ite_false] at hs
    have hh := hside false {j} (by simp) (by simp) _ _ hs
    have hd : site i=.dummy := (indexed_dummy (n*q) W D (by omega) (sitePermutation pi) i).2 hi
    simpa only [Q,he,hd,color,SideCatalog.sign,Bool.false_eq_true,ite_false,Int.cast_one,one_mul] using hh
  · intro j s i hi
    have hs := side_dummy_support n q D W B hW hEven pi true j s i hi
    simp only [sideIndex_eq_palette,ite_true] at hs
    have hh := hside true {j} (by simp) (by simp) _ _ hs
    have hd : site i=.dummy := (indexed_dummy (n*q) W D (by omega) (sitePermutation pi) i).2 hi
    simpa only [Q,hl,hd,color,SideCatalog.sign,ite_true,Int.cast_neg,Int.cast_one,neg_one_mul] using hh

/-- Actual complete-core minimizers force the whole (5.2) palette while all
other core edges remain free. The statement has no assumed fan-field bound. -/
theorem every_minimizer_palette (n q D W B : ℕ) (hW : 2≤W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0<n*q) (hBO : O n q D W≤B) (h8 : 8∣B)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ)
    (p : Placement (recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi))
      (geometries n q D W B hW hEven pi))
    (hBscale : 1024*B≤(O n q D W)^2)
    (hA : 8*(O n q D W:ℤ)^2≤A) (hT : 5*(O n q D W:ℤ)^2<T)
    (κ : CompleteDrawing.Inner (O n q D W)→Bool)
    (hmin : ∀ψ, CompleteBackground.coreValue (parameter n q D W B) (DoubleCapGrid.frameParameter B)
      (ProgramIndex.points (recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi)) p.points)
      (CompleteBackground.frozenFans (parameter n q D W B) (DoubleCapGrid.frameParameter B)
        (ProgramIndex.points (recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi)) p.points) false) κ≤
      CompleteBackground.coreValue (parameter n q D W B) (DoubleCapGrid.frameParameter B)
      (ProgramIndex.points (recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi)) p.points)
      (CompleteBackground.frozenFans (parameter n q D W B) (DoubleCapGrid.frameParameter B)
        (ProgramIndex.points (recipe A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi)) p.points) false) ψ) :
    ∀v∈palette (indexedSite (n*q) W D (by omega) (sitePermutation pi)),
      κ v=paletteBit (indexedSite (n*q) W D (by omega) (sitePermutation pi)) v := by
  apply IndexedPaletteForcing.every_minimizer_palette _ _ _
    (indexedSite (n*q) W D (by omega) (sitePermutation pi)) ?_ κ hmin
  intro v hv
  have hallow := (Finset.mem_filter.mp hv).2
  have hh := pair_dominance n q D W B hW hEven hD hS hBO h8 pi A T p hBscale hA hT _ _ hallow
  unfold paletteBit
  split_ifs at hh ⊢
  all_goals
    have hhr := (Rat.cast_lt (K:=ℝ)).2 hh
    push_cast at hhr
    simpa only [Nat.cast_add,Nat.cast_mul] using hhr

end Q4.Candidate.ActualCatalogBounds
#print axioms Q4.Candidate.ActualCatalogBounds.pair_dominance
#print axioms Q4.Candidate.ActualCatalogBounds.every_minimizer_palette
