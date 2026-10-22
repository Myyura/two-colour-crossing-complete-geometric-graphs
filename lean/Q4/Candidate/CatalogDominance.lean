import Q4.Candidate.CatalogSupport

/-! The numerical dominance is instantiated on actual placed catalog fields,
with computed recipe coefficients and actual finite rank-family costs. -/
namespace Q4.Candidate.CatalogDominance
open Q4.Candidate.ConvexSeparation Q4.Candidate.ProgramCount
open Q4.Candidate.ProgramCatalog Q4.Candidate.CatalogSupport
open Q4.Candidate.ActualRecipe

/-- The shared right-prefix offset is bounded from actual palette counting
and the actual greedy rank program, rather than assumed to be small. -/
theorem offset_bound {S W D B : ℕ} (A T : ℤ) (hS : 0<S) (hW : 0<W)
    (pi : Equiv.Perm (Fin S)) (g : Geometries S (W-1) B (S*W+D+S*W))
    (hy : StrictMono g.ys) (hD : 2*S*W<D) (j : Fin S) (hB : 0<B)
    (hBsmall : B≤(S*W+D+S*W)^2)
    (hwR : ∀i<W-1, 0<rankRightWeight g j i ∧ rankRightWeight g j i≤B) :
    |(recipe A T hW pi g).offset j|≤4*(((S*W+D+S*W:ℕ):ℚ)^2) := by
  have hp := palette_affine hS hW pi g.ys hy hD j
  have hc := RankCorrection.cumulative_bounds (rightSlope S W D hW pi j) B (W-1)
    (rankRightWeight g j) hB hwR
  have hWsmall : W≤S*W+D+S*W := by
    have hh := Nat.mul_le_mul_right W (show 1≤S by omega)
    omega
  have hm := Nat.mul_le_mul hp.2.1 (le_trans (Nat.sub_le W 1) hWsmall)
  have hci : (RankCorrection.cumulative (rightSlope S W D hW pi j) (rankRightWeight g j) (W-1):ℚ)
      ≤2*(((S*W+D+S*W:ℕ):ℚ)^2) := by
    have hn : RankCorrection.cumulative (rightSlope S W D hW pi j) (rankRightWeight g j) (W-1)
        ≤2*(S*W+D+S*W)^2 := by nlinarith [hc.2]
    exact_mod_cast hn
  have hbeta : |(beta hW pi g.ys j:ℚ)|≤(((S*W+D+S*W:ℕ):ℚ)^2) := by exact_mod_cast hp.2.2.1
  have hbeta' := abs_le.mp hbeta
  change |(beta hW pi g.ys j:ℚ)-RankCorrection.cumulative
    (rightSlope S W D hW pi j) (rankRightWeight g j) (W-1)|≤_
  rw [abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α:=ℚ)
    (RankCorrection.cumulative (rightSlope S W D hW pi j) (rankRightWeight g j) (W-1)),sq_nonneg (((S*W+D+S*W:ℕ):ℚ))]

/-- The selected reference half-weights also apply to any actual early-j/
late-k chord on the same sides, by the proved rank-independent incident table. -/
theorem cross_field_reference {S W D B : ℕ} (A T : ℤ) (hW : 0<W)
    (pi : Equiv.Perm (Fin S)) (g : Geometries S (W-1) B (S*W+D+S*W))
    (p : Placement (recipe A T hW pi g) g) (j k : Fin S) (c b : ℚ)
    (h : CrossSupport g j k c b) (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hj0 : Selected (recipe A T hW pi g) g j W ⟨0,hW⟩ ⟨0,hW⟩
      (g.ys (ProposedPalette.earlyEndpoint S W D pi j ⟨0,hW⟩))
      (g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩)))
    (hk0 : Selected (recipe A T hW pi g) g k W ⟨0,hW⟩ ⟨0,hW⟩
      (g.ys (ProposedPalette.earlyEndpoint S W D pi k ⟨0,hW⟩))
      (g.ys (ProposedPalette.lateEndpoint S W D pi k ⟨0,hW⟩)))
    (hsideL : (g.ordinaryLeft j).2.a<b ↔
      (g.ordinaryLeft j).2.a<g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩))
    (hsideR : (g.ordinaryRight k).2.a<c ↔
      (g.ordinaryRight k).2.a<g.ys (ProposedPalette.earlyEndpoint S W D pi k ⟨0,hW⟩)) :
    ProgramField.field (B:=B) (recipe A T hW pi g) g.ys p.points (original c) (original b)=
      (ProgramCount.ordinaryLeft (recipe A T hW pi g) j:ℤ)*ordinaryLeftWeight hW pi g j-
      (ProgramCount.ordinaryRight (recipe A T hW pi g) k:ℤ)*ordinaryRightWeight hW pi g k+
      (rankL (recipe A T hW pi g) g p j c b+rankR (recipe A T hW pi g) g p k c b) := by
  have hOL := OrdinaryCoreField.incident_rank_independent (g.ordinaryLeft j).2 _ _ _ _
    h.unit_c hj0.unit_c h.unit_b hj0.unit_b h.left_clone hj0.ordinary_left_clone
    h.left_sep hj0.ordinary_left_sep hsideL
  have hOR := OrdinaryCoreField.incident_rank_independent (g.ordinaryRight k).2 _ _ _ _
    h.unit_b hk0.unit_b h.unit_c hk0.unit_c h.right_clone hk0.ordinary_right_clone
    h.right_sep hk0.ordinary_right_sep hsideR
  change OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2 c b=ordinaryLeftWeight hW pi g j at hOL
  have hOR' : OrdinaryCoreField.coreCoefficient (g.ordinaryRight k).2 b c= -ordinaryRightWeight hW pi g k := by
    simpa only [ordinaryRightWeight,neg_neg] using hOR
  rw [cross_field (recipe A T hW pi g) g p j k c b h hcM hbM,hOL,hOR']
  ring

/-- Actual nonselected cross-block field dominates every possible core
neighbor contribution. The rank field is not prescribed: its entire actual
value is paid by the independently proved finite-copy budget. -/
theorem cross_dominance {S W D B : ℕ} (A T : ℤ) (hS : 0<S) (hW : 0<W)
    (pi : Equiv.Perm (Fin S)) (g : Geometries S (W-1) B (S*W+D+S*W))
    (hy : StrictMono g.ys) (hD : 2*S*W<D) (p : Placement (recipe A T hW pi g) g)
    (j k : Fin S) (hjk : j≠k) (c b : ℚ) (h : CrossSupport g j k c b)
    (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hj0 : Selected (recipe A T hW pi g) g j W ⟨0,hW⟩ ⟨0,hW⟩
      (g.ys (ProposedPalette.earlyEndpoint S W D pi j ⟨0,hW⟩))
      (g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩)))
    (hk0 : Selected (recipe A T hW pi g) g k W ⟨0,hW⟩ ⟨0,hW⟩
      (g.ys (ProposedPalette.earlyEndpoint S W D pi k ⟨0,hW⟩))
      (g.ys (ProposedPalette.lateEndpoint S W D pi k ⟨0,hW⟩)))
    (hsideL : (g.ordinaryLeft j).2.a<b ↔
      (g.ordinaryLeft j).2.a<g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩))
    (hsideR : (g.ordinaryRight k).2.a<c ↔
      (g.ordinaryRight k).2.a<g.ys (ProposedPalette.earlyEndpoint S W D pi k ⟨0,hW⟩))
    (hscale : 514*W≤S*W+D+S*W) (hB : 0<B) (hBscale : 1024*B≤(S*W+D+S*W)^2)
    (hA : 8*((S*W+D+S*W:ℕ):ℤ)^2≤A) (hT : 5*((S*W+D+S*W:ℕ):ℤ)^2<T)
    (hwLj : ∀i<W-1, 0<rankLeftWeight g j i ∧ rankLeftWeight g j i≤B ∧ B≤4*rankLeftWeight g j i)
    (hwRj : ∀i<W-1, 0<rankRightWeight g j i ∧ rankRightWeight g j i≤B)
    (hwRk : ∀i<W-1, 0<rankRightWeight g k i ∧ rankRightWeight g k i≤B ∧ B≤4*rankRightWeight g k i)
    (huL : 0<ordinaryLeftWeight hW pi g j) (huLB : ordinaryLeftWeight hW pi g j≤B)
    (huR : 0<ordinaryRightWeight hW pi g k) (huRB : ordinaryRightWeight hW pi g k≤B) :
    if j<k then (ProgramField.field (B:=B) (recipe A T hW pi g) g.ys p.points (original c) (original b):ℚ)<
      -(((S*W+D+S*W:ℕ):ℚ)^2/2)
    else (((S*W+D+S*W:ℕ):ℚ)^2/2)<
      (ProgramField.field (B:=B) (recipe A T hW pi g) g.ys p.points (original c) (original b):ℚ) := by
  let O := S*W+D+S*W
  let d := recipe A T hW pi g
  let R := rankL d g p j c b+rankR d g p k c b
  have ho : 0<O := by dsimp [O]; nlinarith [Nat.mul_pos hS hW]
  have hj := palette_affine hS hW pi g.ys hy hD j
  have hk := palette_affine hS hW pi g.ys hy hD k
  have hR := cross_rank_budget d g p j k c b W hB (Nat.sub_le W 1) hj.1 hk.2.1 hwLj hwRk
  have hoff := offset_bound A T hS hW pi g hy hD j hB (by omega) hwRj
  have hsign := PaletteBounds.nonselected_direction j.val k.val (by intro he; exact hjk (Fin.ext he))
    A T (d.offset j) (ordinaryLeftWeight hW pi g j) (ordinaryRightWeight hW pi g k) O W B (R:ℚ) ((O:ℚ)^2/2)
    (by exact_mod_cast ho) (Nat.cast_nonneg W) (by exact_mod_cast hscale)
    (by exact_mod_cast hB) (by exact_mod_cast hBscale) (by exact_mod_cast hA) (by exact_mod_cast hT)
    hoff (by exact_mod_cast huL) (by exact_mod_cast huLB) (by exact_mod_cast huR) (by exact_mod_cast huRB)
    (le_of_lt (by exact_mod_cast hR)) (le_refl _)
  have hf := cross_field_reference A T hW pi g p j k c b h hcM hbM hj0 hk0 hsideL hsideR
  rw [hf]
  dsimp only at hsign
  simpa only [ProgramCount.ordinaryLeft,ProgramCount.ordinaryRight,recipe,d,O,R,
    Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Fin.lt_def] using hsign

end Q4.Candidate.CatalogDominance
#print axioms Q4.Candidate.CatalogDominance.offset_bound
#print axioms Q4.Candidate.CatalogDominance.cross_field_reference
#print axioms Q4.Candidate.CatalogDominance.cross_dominance
