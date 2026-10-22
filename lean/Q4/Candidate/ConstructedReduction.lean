import Q4.Candidate.ActualReductionValue
import Q4.Candidate.ProgramPlacement
import Q4.Candidate.ProgramIndex
import Q4.Candidate.CandidateSize
import Q4.Candidate.ActualSelectedUnary
import Q4.Candidate.ActualCatalogBounds
import Q4.Candidate.CatalogTargets
import Q4.Candidate.CompleteInput
import Q4.Candidate.SourceCutBridge
import Q4.Candidate.ActualCatalogParameters

namespace Q4.Candidate.ConstructedReduction
open Q4.Candidate.ConvexSeparation Q4.Candidate.CompleteDrawing
open Q4.Candidate.ProgramCount Q4.Candidate.ProgramCatalog
open Q4.Candidate.ProgramGeometry Q4.Candidate.ProgramPlacement
open Q4.Candidate.OriginalVertexLayout
open Q4.Candidate.FreezingParameters Q4.Candidate.ProposedPalette
open Q4.Candidate.CatalogTargets Q4.Candidate.ActualReductionValue
open Q4.Candidate.ConvexBackground Q4.Candidate.CompleteInput
attribute [local irreducible] scale originals frames
set_option maxHeartbeats 1000000

theorem reindexed_program_witnesses (n q D W B : ℕ) (hW : 2≤W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0<n*q) (pi : Equiv.Perm (Fin n))
    (d : Recipe (n*q)) (p : Placement d (geometries n q D W B hW hEven pi)) :
    ∀k, CompleteFanFields.ProgramWitness (B:=B) (parameter n q D W B) p.M p.base p.prototypes
      (ProgramIndex.points d p.points k) := by
  intro k
  exact programWitness n q D W B hW hEven hD hS pi d p ((Fintype.equivFin _).symm k)

/-- Every program-count, field, forcing and residual premise of the full-value
theorem is discharged for the actual constructed catalog. -/
theorem placed_source_threshold (n q D W B : ℕ) (hn : 1≤n)
    (hq : q=2^20*(n+1)) (hWval : W=(scale (n*q))^4)
    (hD : D=512*(n*q)*W) (hBval : B=frames (n*q))
    (hW : 2≤W) (hEven : Even B) (pi : Equiv.Perm (Fin n))
    (p : Placement (ActualRecipe.recipe (amplitude (n*q) (O n q D W)) (increment (O n q D W))
      (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi))
      (geometries n q D W B hW hEven pi))
    (hframe : ConvexOptimum B (knownZ B)) (hdummy : ConvexOptimum D (knownZ D)) (t : ℤ) :
    let d := ActualRecipe.recipe (amplitude (n*q) (O n q D W)) (increment (O n q D W))
      (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi)
    let rs := ProgramIndex.points d p.points
    let site := indexedSite (n*q) W D (by omega) (sitePermutation pi)
    let r : ℚ := baseline (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs site D+
      (q:ℚ)^2*(scale (n*q):ℚ)^16*t+(q:ℚ)^2*(scale (n*q):ℚ)^16/4
    (∃chi : Edge (O n q D W) B (Fintype.card (Label d (W-1))) → Bool,
      (Q4.monoCount (CompleteGridEnergy.crossingPairs (parameter n q D W B)
        (DoubleCapGrid.frameParameter B) rs).toList chi:ℤ)≤⌊r⌋) ↔
      (CoreEncoding.sourceOpt (SourceSelectedEdges.sourcePairs pi).toList:ℤ)≤t := by
  have hq0 : 0<q := by rw [hq]; positivity
  have hS : 0<n*q := Nat.mul_pos (by omega) hq0
  have hP := ActualCatalogParameters.actual_count n q D W B hS hWval hD hBval hW hEven pi
  have hdim := dimensions n q D W B hS hWval hD hBval
  have hmargin := margins (n*q) (O n q D W) (by change 0<n*q*W+D+n*q*W; omega)
  have hBsmall : B≤(O n q D W)^2 := by change B≤(n*q*W+D+n*q*W)^2; omega
  let d := ActualRecipe.recipe (amplitude (n*q) (O n q D W)) (increment (O n q D W))
    (show 0<W by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi)
  exact actual_source_threshold n q W D B (Fintype.card (Label d (W-1))) t
    hn hq hWval hD hBval (by simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_mul] using hP) hW pi
    p.M p.base p.prototypes (ProgramIndex.points d p.points)
    (reindexed_program_witnesses n q D W B hW hEven hD hS pi d p)
    p.frame_mem p.original_mem p.proto_below hframe hdummy
    (ActualCatalogBounds.every_minimizer_palette n q D W B hW hEven hD hS hdim.2.2.1 hdim.2.2.2.2 pi
      (amplitude (n*q) (O n q D W)) (increment (O n q D W)) p hdim.2.2.2.1 hmargin.1 hmargin.2.1)
    (ActualSelectedUnary.selected_unary_bound n q D W B hW hEven hD hS hdim.2.2.1 hBsmall hdim.2.2.2.2 pi
      (amplitude (n*q) (O n q D W)) (increment (O n q D W)) hmargin.1 hmargin.2.2 p)
    (ActualSelectedUnary.dummy_unary_equal n q D W B hW hEven hS pi _ _ p)

theorem plain_integer_threshold_iff {N : ℕ} (coords : Fin N→Point) (r : ℚ) :
    (∃chi : Inner N→Bool, (Q4.monoCount (plainPairs coords).toList chi:ℤ)≤⌊r⌋) ↔
    (∃chi : Inner N→Bool, plainEnergy coords chi≤(r:ℝ)) := by
  simp only [nat_floor_iff,plainEnergy]

/-- The source objective is now represented MaxCut, and the target objective
is freely coloring every edge of one Fin-indexed complete geometric graph. -/
theorem placed_maxcut_threshold (n q D W B : ℕ) (hn : 1≤n)
    (hq : q=2^20*(n+1)) (hWval : W=(scale (n*q))^4)
    (hD : D=512*(n*q)*W) (hBval : B=frames (n*q))
    (hW : 2≤W) (hEven : Even B) (pi : Equiv.Perm (Fin n))
    (p : Placement (ActualRecipe.recipe (amplitude (n*q) (O n q D W)) (increment (O n q D W))
      (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi))
      (geometries n q D W B hW hEven pi))
    (hframe : ConvexOptimum B (knownZ B)) (hdummy : ConvexOptimum D (knownZ D)) (k : ℤ) :
    let d := ActualRecipe.recipe (amplitude (n*q) (O n q D W)) (increment (O n q D W))
      (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi)
    let rs := ProgramIndex.points d p.points
    let site := indexedSite (n*q) W D (by omega) (sitePermutation pi)
    let r : ℚ := baseline (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs site D+
      (q:ℚ)^2*(scale (n*q):ℚ)^16*((SourceSelectedEdges.sourcePairs pi).card-k)+
      (q:ℚ)^2*(scale (n*q):ℚ)^16/4
    (∃chi : Inner (O n q D W+B+Fintype.card (Label d (W-1))) → Bool,
      (Q4.monoCount (plainPairs (finCoordinates (parameter n q D W B)
        (DoubleCapGrid.frameParameter B) rs)).toList chi:ℤ)≤⌊r⌋) ↔
      ∃psi : Fin n→Bool, k≤(Q4.cutCount (SourceSelectedEdges.sourcePairs pi).toList psi:ℤ) := by
  dsimp only
  rw [plain_integer_threshold_iff,←decision_transport,←integer_threshold_iff]
  have hh := placed_source_threshold n q D W B hn hq hWval hD hBval hW hEven pi p hframe hdummy
    ((SourceSelectedEdges.sourcePairs pi).card-k)
  push_cast at hh
  exact hh.trans (SourceCutBridge.permutation_threshold pi k)

theorem binaryPoint_mono {K L : ℕ} {z : Point} (hKL : K≤L) (hz : BinaryPoint K z) : BinaryPoint L z := by
  obtain ⟨nx,dx,ny,dy,hx,hdx,hd0,hze,hy,hdy,hdy0,hzf⟩ := hz
  have hp : (2:ℤ)^K≤2^L := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hKL
  exact ⟨nx,dx,ny,dy,hx.trans hp,hdx.trans hp,hd0,hze,hy.trans hp,hdy.trans hp,hdy0,hzf⟩

/-- One complete rational drawing simultaneously satisfies general position,
injectivity, polynomial point/coordinate bounds and the exact integer MaxCut
threshold equivalence. The only mathematical result supplied externally is
the known convex-complete-graph optimum certificate. This theorem asserts
existence and explicit output-size bounds, not a formal machine-time bound. -/
theorem constructed_maxcut_instance (n : ℕ) (hn : 1≤n) (pi : Equiv.Perm (Fin n)) (k : ℤ)
    (hconvex : ∀m, ConvexOptimum m (knownZ m)) :
    ∃(N : ℕ) (coords : Fin N→Point) (K : ℤ),
      N≤3*(2^20840*(n+1)^80)^5 ∧
      Function.Injective coords ∧ GeneralPosition (Finset.univ.image coords) ∧
      (∀v, BinaryPoint (2^17*(2^20840*(n+1)^80)^10) (coords v)) ∧
      ((∃chi : Inner N→Bool, (Q4.monoCount (plainPairs coords).toList chi:ℤ)≤K) ↔
        ∃psi : Fin n→Bool, k≤(Q4.cutCount (SourceSelectedEdges.sourcePairs pi).toList psi:ℤ)) := by
  let q := 2^20*(n+1)
  let W := (scale (n*q))^4
  let D := 512*(n*q)*W
  let B := frames (n*q)
  have hq0 : 0<q := by dsimp [q]; positivity
  have hS : 0<n*q := Nat.mul_pos (by omega) hq0
  have hdim := dimensions n q D W B hS rfl rfl rfl
  have hW : 2≤W := hdim.1
  have hEven : Even B := by
    obtain ⟨b,hb⟩ := hdim.2.2.2.2
    exact ⟨4*b,by omega⟩
  let d := ActualRecipe.recipe (amplitude (n*q) (O n q D W)) (increment (O n q D W))
    (show 0<W by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi)
  let P := Fintype.card (Label d (W-1))
  obtain ⟨p,hbase,hproto,hM,hinj,hout,hpoint,hgp,hbit⟩ := complete_fin_input_exists n q D W B hW hEven pi d
  let rs := ProgramIndex.points d p.points
  let coords := finCoordinates (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs
  let site := indexedSite (n*q) W D (show 0<W by omega) (sitePermutation pi)
  let r : ℚ := baseline (parameter n q D W B) (DoubleCapGrid.frameParameter B) rs site D+
    (q:ℚ)^2*(scale (n*q):ℚ)^16*((SourceSelectedEdges.sourcePairs pi).card-k)+
    (q:ℚ)^2*(scale (n*q):ℚ)^16/4
  have hP : (P:ℝ)≤(2:ℝ)^80*((n*q:ℕ)+1:ℝ)^4*(scale (n*q):ℝ)^3 := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
      ActualCatalogParameters.actual_count n q D W B hS rfl rfl rfl hW hEven pi
  have hsize := CandidateSize.source_polynomial_bounds n q P hn rfl hP
  have hOeq : O n q D W=originals (n*q) := by
    dsimp only [O,D,W]
    unfold originals
    ring
  have hK : encodingBudget n q D W B d*(602*(O n q D W+B)+2719)≤2^17*(2^20840*(n+1)^80)^10 := by
    simpa only [encodingBudget,hOeq,D,W,B,P] using hsize.2
  refine ⟨O n q D W+B+P,coords,⌊r⌋,?_,hpoint,hgp,?_,?_⟩
  · simpa only [hOeq,B] using hsize.1
  · intro v
    exact binaryPoint_mono hK (hbit v)
  · exact placed_maxcut_threshold n q D W B hn rfl rfl rfl rfl hW hEven pi p (hconvex B) (hconvex D) k

#print axioms reindexed_program_witnesses
#print axioms placed_source_threshold
#print axioms placed_maxcut_threshold
#print axioms constructed_maxcut_instance

end Q4.Candidate.ConstructedReduction
