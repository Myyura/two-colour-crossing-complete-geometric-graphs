import Q4.Candidate.ActualDummyUnary
import Q4.Candidate.ProgramIndex
import Q4.Candidate.CatalogDominance
import Q4.Candidate.ActualCatalogRegime

/-! From actual catalog fields to every selected and dummy variable in the
full frozen core. All endpoint indexing and real/integer cost casts are explicit. -/
namespace Q4.Candidate.ActualSelectedUnary
open Q4.Candidate.ConvexSeparation Q4.Candidate.CompleteDrawing
open Q4.Candidate.ProgramGeometry Q4.Candidate.ProgramCatalog
open Q4.Candidate.OriginalVertexLayout Q4.Candidate.ProposedPalette
open Q4.Candidate.CoreLocalGeometry Q4.Candidate.PaletteCounting
open Q4.Candidate.ActualRecipe
set_option maxHeartbeats 1000000

/-- The actual all-palette plus all-program unary of every dummy chord is
independent of its free colour. -/
theorem dummy_unary_equal (n q D W B : ℕ) (hW : 2≤W) (hEven : Even B) (hS : 0<n*q)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ)
    (p : Placement (ActualRecipe.recipe A T (by omega) (sitePermutation pi)
      (geometries n q D W B hW hEven pi)) (geometries n q D W B hW hEven pi))
    (e : Inner (O n q D W))
    (he : dummyEdge (indexedSite (n*q) W D (by omega) (sitePermutation pi)) e) :
    let rs := ProgramIndex.points (ActualRecipe.recipe A T (by omega) (sitePermutation pi)
      (geometries n q D W B hW hEven pi)) p.points
    CoreValueBridge.unary (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs
      (indexedSite (n*q) W D (by omega) (sitePermutation pi))
      (CompleteBackground.frozenFans (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs false) e true=
    CoreValueBridge.unary (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs
      (indexedSite (n*q) W D (by omega) (sitePermutation pi))
      (CompleteBackground.frozenFans (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs false) e false := by
  dsimp only
  have htrue := ProgramIndex.actual_unary_eq A T (show 0<W by omega) (sitePermutation pi)
    (geometries n q D W B hW hEven pi) p e true
  have hfalse := ProgramIndex.actual_unary_eq A T (show 0<W by omega) (sitePermutation pi)
    (geometries n q D W B hW hEven pi) p e false
  have hu := (indexed_dummy (n*q) W D (by omega) (sitePermutation pi) e.val.1).1 he.1
  have hv := (indexed_dummy (n*q) W D (by omega) (sitePermutation pi) e.val.2).1 he.2
  exact htrue.trans ((congrArg (fun z : ℤ => (z:ℝ))
    (ActualDummyUnary.unary_constant n q D W B hW hEven hS pi A T p e.val.1 e.val.2 e.property hu.1 hv.2 true)).trans hfalse.symm)

/-- Every actual selected edge has one ordered early/late block index and
two clone ranks. This lifts a rank-by-rank field estimate to the complete
core's selected predicate, not merely a separately indexed selected family. -/
theorem selected_from_rank_bounds {S W D B : ℕ} (A T : ℤ) (hW : 0<W)
    (pi : Equiv.Perm (Fin S)) (g : Geometries S (W-1) B (S*W+D+S*W))
    (p : Placement (ActualRecipe.recipe A T hW pi g) g)
    (hrank : ∀j (s t : Fin W),
      |ActualRecipe.unary A T hW pi g p (earlyEndpoint S W D pi j s) (lateEndpoint S W D pi j t) true-
        ActualRecipe.unary A T hW pi g p (earlyEndpoint S W D pi j s) (lateEndpoint S W D pi j t) false|≤4*(B:ℤ))
    (e : Inner (S*W+D+S*W)) (he : CoreExtension.selected (indexedSite S W D hW pi) e) :
    let rs := ProgramIndex.points (ActualRecipe.recipe A T hW pi g) p.points
    |CoreValueBridge.unary g.ys (DoubleCapGrid.frameParameter B) rs (indexedSite S W D hW pi)
      (CompleteBackground.frozenFans g.ys (DoubleCapGrid.frameParameter B) rs false) e true-
    CoreValueBridge.unary g.ys (DoubleCapGrid.frameParameter B) rs (indexedSite S W D hW pi)
      (CompleteBackground.frozenFans g.ys (DoubleCapGrid.frameParameter B) rs false) e false|≤4*(B:ℝ) := by
  dsimp only
  rw [ProgramIndex.actual_unary_eq,ProgramIndex.actual_unary_eq]
  obtain ⟨j,hj⟩ := he
  have hf := indexed_fibers S W D hW pi j
  have hb := indexed_bounds S W D pi j
  rcases hj with hj|hj
  · obtain ⟨s,hs⟩ := endpoint_exists hb.1 e.val.1 ((hf.early _).1 hj.1)
    obtain ⟨t,ht⟩ := endpoint_exists hb.2.1 e.val.2 ((hf.late _).1 hj.2)
    have hh := hrank j s t
    change |ActualRecipe.unary A T hW pi g p (endpoint _ hb.1 s) (endpoint _ hb.2.1 t) true-
      ActualRecipe.unary A T hW pi g p (endpoint _ hb.1 s) (endpoint _ hb.2.1 t) false|≤4*(B:ℤ) at hh
    rw [hs,ht] at hh
    exact_mod_cast hh
  · have h1 := (hf.late _).1 hj.1
    have h2 := (hf.early _).1 hj.2
    have heord : e.val.1.val<e.val.2.val := e.property
    omega

/-- Actual placed catalog bounds, with every geometric weight, rank table,
reference-side equality and affine palette offset instantiated. Only scalar
scale inequalities remain as inputs. -/
theorem selected_rank_bound (n q D W B : ℕ) (hW : 2≤W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0<n*q) (hBO : O n q D W≤B)
    (hBsmall : B≤(O n q D W)^2) (h8 : 8∣B)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ)
    (hA : 8*(O n q D W:ℤ)^2≤A) (hT : 0≤T)
    (p : Placement (ActualRecipe.recipe A T (by omega) (sitePermutation pi)
      (geometries n q D W B hW hEven pi)) (geometries n q D W B hW hEven pi))
    (j : Fin (n*q)) (s t : Fin W) :
    |ActualRecipe.unary A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) p
        (earlyEndpoint (n*q) W D (sitePermutation pi) j s) (lateEndpoint (n*q) W D (sitePermutation pi) j t) true-
      ActualRecipe.unary A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) p
        (earlyEndpoint (n*q) W D (sitePermutation pi) j s) (lateEndpoint (n*q) W D (sitePermutation pi) j t) false|≤4*(B:ℤ) := by
  let g := geometries n q D W B hW hEven pi
  have hB : 0<B := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : 0<1000)
    (proportions n q D W hD hS hW).1) hBO
  have hD' : 2*(n*q)*W<D := by
    have hSW : 0<n*q*W := Nat.mul_pos hS (by omega)
    calc
      2*(n*q)*W = 2*(n*q*W) := by ring
      _ < 512*(n*q*W) := by omega
      _ = D := by rw [hD]; ring
  have hy : StrictMono g.ys := parameter_strictMono n q D W B hW
  have hw := ActualCatalogRegime.rank_weights n q D W B hW hEven hD hS hBO h8 pi j
  have hwL := fun i hi => (hw.1 i hi).imp_right And.left
  have hwR := fun i hi => (hw.2 i hi).imp_right And.left
  have hu := ActualCatalogRegime.ordinary_weights n q D W B hW hEven hD hS hBO h8 pi A T j
  have hsides := ActualCatalogRegime.cross_sides n q D W B hW hEven pi j j s t
  have hoff := CatalogDominance.offset_bound A T hS (show 0<W by omega) (sitePermutation pi) g hy hD' j hB hBsmall hwR
  have hoffI : |ActualRecipe.beta (by omega) (sitePermutation pi) g.ys j-
      (RankCorrection.cumulative (ActualRecipe.rightSlope (n*q) W D (by omega) (sitePermutation pi) j)
        (rankRightWeight g j) (W-1):ℤ)|≤4*(O n q D W:ℤ)^2 := by
    change |(ActualRecipe.beta (by omega) (sitePermutation pi) g.ys j:ℚ)-
      (RankCorrection.cumulative (ActualRecipe.rightSlope (n*q) W D (by omega) (sitePermutation pi) j)
        (rankRightWeight g j) (W-1):ℚ)|≤4*(O n q D W:ℚ)^2 at hoff
    exact_mod_cast hoff
  have htR : 0≤A+(j.val:ℤ)*T := by nlinarith [sq_nonneg (O n q D W:ℤ),mul_nonneg (Int.natCast_nonneg j.val) hT]
  have htL : 0≤A+(j.val:ℤ)*T-(ActualRecipe.beta (by omega) (sitePermutation pi) g.ys j-
      (RankCorrection.cumulative (ActualRecipe.rightSlope (n*q) W D (by omega) (sitePermutation pi) j)
        (rankRightWeight g j) (W-1):ℤ)) := by
    have hh := (abs_le.mp hoffI).2
    nlinarith [sq_nonneg (O n q D W:ℤ),mul_nonneg (Int.natCast_nonneg j.val) hT]
  have hh := ActualRecipe.selected_residual A T hS (show 0<W by omega) (sitePermutation pi) g hy hD' p j s t
    (ActualProgramGeometry.selected n q D W B hW hEven hD hS hBO h8 pi A T j s t)
    (ActualProgramGeometry.selected n q D W B hW hEven hD hS hBO h8 pi A T j ⟨0,by omega⟩ ⟨0,by omega⟩)
    (fun k hk => ActualProgramGeometry.selected_other n q D W B hW hEven pi j k s t hk)
    hsides.1 hsides.2 hB hwL hwR hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 htL htR
  rw [ActualRecipe.unary_difference]
  exact hh.le

/-- The resulting bound applies to every selected edge in the actual frozen
full core, after the finite label-to-program reindexing. -/
theorem selected_unary_bound (n q D W B : ℕ) (hW : 2≤W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0<n*q) (hBO : O n q D W≤B)
    (hBsmall : B≤(O n q D W)^2) (h8 : 8∣B)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ)
    (hA : 8*(O n q D W:ℤ)^2≤A) (hT : 0≤T)
    (p : Placement (ActualRecipe.recipe A T (by omega) (sitePermutation pi)
      (geometries n q D W B hW hEven pi)) (geometries n q D W B hW hEven pi))
    (e : Inner (O n q D W))
    (he : CoreExtension.selected (indexedSite (n*q) W D (by omega) (sitePermutation pi)) e) :
    let rs := ProgramIndex.points (ActualRecipe.recipe A T (by omega) (sitePermutation pi)
      (geometries n q D W B hW hEven pi)) p.points
    |CoreValueBridge.unary (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs
      (indexedSite (n*q) W D (by omega) (sitePermutation pi))
      (CompleteBackground.frozenFans (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs false) e true-
    CoreValueBridge.unary (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs
      (indexedSite (n*q) W D (by omega) (sitePermutation pi))
      (CompleteBackground.frozenFans (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs false) e false|≤4*(B:ℝ) :=
  selected_from_rank_bounds A T (by omega) (sitePermutation pi) _ p
    (selected_rank_bound n q D W B hW hEven hD hS hBO hBsmall h8 pi A T hA hT p) e he

#print axioms dummy_unary_equal
#print axioms selected_from_rank_bounds
#print axioms selected_rank_bound
#print axioms selected_unary_bound

end Q4.Candidate.ActualSelectedUnary
