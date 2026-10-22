import Q4.Candidate.ProgramCatalog
import Q4.Candidate.ProposedPalette

/-! The four-family recipe computed from actual finite response weights,
the actual proposed-palette field, and the explicit greedy correction. -/
namespace Q4.Candidate.ActualRecipe
open Q4.Candidate.ProgramCount Q4.Candidate.ProgramCatalog
open Q4.Candidate.RankResponse Q4.Candidate.RankSoftRows
open scoped BigOperators

noncomputable def rankLeftWeight {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (j : Fin S) (i : ℕ) : ℕ :=
  if hi : i<gaps then (totalWeight (B:=B) (g.rankLeft j ⟨i,hi⟩).2.ys
    (leftPoint (g.rankLeft j ⟨i,hi⟩).2)).toNat else 0
noncomputable def rankRightWeight {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (j : Fin S) (i : ℕ) : ℕ :=
  if hi : i<gaps then (-totalWeight (B:=B) (g.rankRight j ⟨i,hi⟩).2.ys
    (rightPoint (g.rankRight j ⟨i,hi⟩).2)).toNat else 0

def gammaLeft (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) (j : Fin S) : ℤ :=
  PaletteCounting.slopeL (j.val*W) (S*W+D+(pi.symm j).val*W) W
    (fun y => ProposedPalette.color (.early j) (ProposedPalette.indexedSite S W D hW pi y))
def gammaRight (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) (j : Fin S) : ℤ :=
  PaletteCounting.slopeR (j.val*W) (S*W+D+(pi.symm j).val*W) W
    (fun y => ProposedPalette.color (.late j) (ProposedPalette.indexedSite S W D hW pi y))
def leftSlope (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) (j : Fin S) : ℕ :=
  (-gammaLeft S W D hW pi j).toNat
def rightSlope (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) (j : Fin S) : ℕ :=
  (-gammaRight S W D hW pi j).toNat

def beta {S W D : ℕ} (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (j : Fin S) : ℤ :=
  ProposedPalette.globalField ys (ProposedPalette.indexedSite S W D hW pi)
    (ProposedPalette.earlyEndpoint S W D pi j ⟨0,hW⟩)
    (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩)

noncomputable def ordinaryLeftWeight {S W D B : ℕ} (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) (j : Fin S) : ℤ :=
  OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2
    (g.ys (ProposedPalette.earlyEndpoint S W D pi j ⟨0,hW⟩))
    (g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩))
noncomputable def ordinaryRightWeight {S W D B : ℕ} (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) (j : Fin S) : ℤ :=
  -OrdinaryCoreField.coreCoefficient (g.ordinaryRight j).2
    (g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩))
    (g.ys (ProposedPalette.earlyEndpoint S W D pi j ⟨0,hW⟩))

/-- All counts subsequently used in Label are computed from these genuine
finite fields. There is no separately supplied beta, slope, or fan weight. -/
noncomputable def recipe {S W D B : ℕ} (A T : ℤ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) : Recipe S where
  A := A
  T := T
  offset j := (beta hW pi g.ys j:ℚ)-RankCorrection.cumulative
    (rightSlope S W D hW pi j) (rankRightWeight g j) (W-1)
  ordinaryLeftWeight j := ordinaryLeftWeight hW pi g j
  ordinaryRightWeight j := ordinaryRightWeight hW pi g j
  leftSlope j := leftSlope S W D hW pi j
  rightSlope j := rightSlope S W D hW pi j
  leftWeight j := rankLeftWeight g j
  rightWeight j := rankRightWeight g j

theorem rankLeftWeight_cast {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (j : Fin S) (h : Fin gaps)
    (hw : 0≤totalWeight (B:=B) (g.rankLeft j h).2.ys (leftPoint (g.rankLeft j h).2)) :
    (rankLeftWeight g j h.val:ℤ)=totalWeight (B:=B) (g.rankLeft j h).2.ys
      (leftPoint (g.rankLeft j h).2) := by
  simp [rankLeftWeight,h.isLt,Int.toNat_of_nonneg hw]

theorem rankRightWeight_cast {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (j : Fin S) (h : Fin gaps)
    (hw : 0≤-totalWeight (B:=B) (g.rankRight j h).2.ys (rightPoint (g.rankRight j h).2)) :
    (rankRightWeight g j h.val:ℤ)= -totalWeight (B:=B) (g.rankRight j h).2.ys
      (rightPoint (g.rankRight j h).2) := by
  simp [rankRightWeight,h.isLt,Int.toNat_of_nonneg hw]

/-- These actual natural weights satisfy the full greedy specification,
including B≤4w, by the real rank-response theorem. -/
theorem rank_left_bounds {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (j : Fin S) (hO : 1000≤O) (hBO : O≤B) (h8 : 8∣B)
    (hcut : ∀h, (g.rankLeft j h).1≤O)
    (hearly : ∀h, ((g.rankLeft j h).1:ℝ)/O≤1/514) :
    ∀i<gaps, 0<rankLeftWeight g j i ∧ rankLeftWeight g j i≤B ∧ B≤4*rankLeftWeight g j i := by
  intro i hi
  let h : Fin gaps := ⟨i,hi⟩
  have hw := left_weight_bounds (g.rankLeft j h).2 hO hBO (hcut h) h8 (hearly h)
  have he := rankLeftWeight_cast g j h hw.1.le
  have heR : (rankLeftWeight g j i:ℝ)=(totalWeight (B:=B) (g.rankLeft j h).2.ys
      (leftPoint (g.rankLeft j h).2):ℝ) := by exact_mod_cast he
  rw [←heR] at hw
  refine ⟨?_,?_,?_⟩
  · have : (0:ℤ)<rankLeftWeight g j i := by rw [he]; exact hw.1
    exact_mod_cast this
  · exact_mod_cast hw.2.2
  · have : (B:ℝ)≤4*(rankLeftWeight g j i:ℝ) := by nlinarith [hw.2.1]
    exact_mod_cast this

theorem rank_right_bounds {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (j : Fin S) (hO : 1000≤O) (hBO : O≤B) (h8 : 8∣B)
    (hcut : ∀h, (g.rankRight j h).1≤O)
    (hlate : ∀h, 1-1/514≤((g.rankRight j h).1:ℝ)/O) :
    ∀i<gaps, 0<rankRightWeight g j i ∧ rankRightWeight g j i≤B ∧ B≤4*rankRightWeight g j i := by
  intro i hi
  let h : Fin gaps := ⟨i,hi⟩
  have hw := right_weight_bounds (g.rankRight j h).2 hO hBO (hcut h) h8 (hlate h)
  have he := rankRightWeight_cast g j h hw.1.le
  have heR : (rankRightWeight g j i:ℝ)= -(totalWeight (B:=B) (g.rankRight j h).2.ys
      (rightPoint (g.rankRight j h).2):ℝ) := by exact_mod_cast he
  rw [←heR] at hw
  refine ⟨?_,?_,?_⟩
  · have : (0:ℤ)<rankRightWeight g j i := by rw [he]; exact hw.1
    exact_mod_cast this
  · exact_mod_cast hw.2.2
  · have : (B:ℝ)≤4*(rankRightWeight g j i:ℝ) := by nlinarith [hw.2.1]
    exact_mod_cast this

/-- The actual palette-counting theorem supplies both computed slopes and
its affine field formula. No aggregate-field identity is a hypothesis. -/
theorem palette_affine {S W D : ℕ} (hS : 0<S) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (hD : 2*S*W<D) (j : Fin S) :
    (leftSlope S W D hW pi j≤S*W+D+S*W) ∧
    (rightSlope S W D hW pi j≤S*W+D+S*W) ∧
    |beta hW pi ys j|≤((S*W+D+S*W:ℕ):ℤ)^2 ∧
    ∀s t, ProposedPalette.globalField ys (ProposedPalette.indexedSite S W D hW pi)
      (ProposedPalette.earlyEndpoint S W D pi j s) (ProposedPalette.lateEndpoint S W D pi j t)=
      beta hW pi ys j-(leftSlope S W D hW pi j:ℤ)*s.val-(rightSlope S W D hW pi j:ℤ)*t.val := by
  have h := ProposedPalette.indexed_palette_parameters S W D hS hW pi ys hy hD j
  change (∀s t : Fin W, _=beta hW pi ys j+gammaLeft S W D hW pi j*s.val+gammaRight S W D hW pi j*t.val) ∧
    |beta hW pi ys j|≤_ ∧ (-_≤gammaLeft S W D hW pi j ∧ gammaLeft S W D hW pi j<0) ∧
    (-_≤gammaRight S W D hW pi j ∧ gammaRight S W D hW pi j<0) at h
  have hL : (leftSlope S W D hW pi j:ℤ)= -gammaLeft S W D hW pi j := by
    simp [leftSlope,Int.toNat_of_nonneg (by omega : 0≤-gammaLeft S W D hW pi j)]
  have hR : (rightSlope S W D hW pi j:ℤ)= -gammaRight S W D hW pi j := by
    simp [rightSlope,Int.toNat_of_nonneg (by omega : 0≤-gammaRight S W D hW pi j)]
  refine ⟨?_,?_,h.2.1,?_⟩
  · have : (leftSlope S W D hW pi j:ℤ)≤S*W+D+S*W := by omega
    exact_mod_cast this
  · have : (rightSlope S W D hW pi j:ℤ)≤S*W+D+S*W := by omega
    exact_mod_cast this
  · intro s t
    rw [h.1 s t,hL,hR]
    ring


/-- Actual ordinary reference weights meet the positive integer bounds used
by the ceiling program; the half-frame lower bound is derived here. -/
theorem ordinary_weights_bounds {S W D B : ℕ} (A T : ℤ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) (j : Fin S)
    (h0 : Selected (recipe A T hW pi g) g j W ⟨0,hW⟩ ⟨0,hW⟩
      (g.ys (ProposedPalette.earlyEndpoint S W D pi j ⟨0,hW⟩))
      (g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩)))
    (hO : 1000≤S*W+D+S*W) (hBO : S*W+D+S*W≤B) (h8 : 8∣B)
    (hcutL : (g.ordinaryLeft j).1≤S*W+D+S*W) (hcutR : (g.ordinaryRight j).1≤S*W+D+S*W)
    (hparentL : ((g.ordinaryLeft j).2.parent.card:ℝ)/((S*W+D+S*W:ℕ):ℝ)≤1/514)
    (hparentR : ((g.ordinaryRight j).2.parent.card:ℝ)/((S*W+D+S*W:ℕ):ℝ)≤1/514)
    (hearly : ((g.ordinaryLeft j).1:ℝ)/((S*W+D+S*W:ℕ):ℝ)≤1/514)
    (hlate : 1-1/514≤((g.ordinaryRight j).1:ℝ)/((S*W+D+S*W:ℕ):ℝ)) :
    0<ordinaryLeftWeight hW pi g j ∧ ordinaryLeftWeight hW pi g j≤B ∧
    0<ordinaryRightWeight hW pi g j ∧ ordinaryRightWeight hW pi g j≤B ∧
    (B:ℤ)≤4*ordinaryLeftWeight hW pi g j ∧ (B:ℤ)≤4*ordinaryRightWeight hW pi g j := by
  have hL := OrdinaryCoreField.early_incident_coefficient (g.ordinaryLeft j).2 hO hBO hcutL h8
    hparentL hearly _ _ h0.unit_c h0.unit_b h0.ordinary_left_clone h0.ordinary_left_sep
  have hR := OrdinaryCoreField.late_incident_coefficient (g.ordinaryRight j).2 hO hBO hcutR h8
    hparentR hlate _ _ h0.unit_b h0.unit_c h0.ordinary_right_clone h0.ordinary_right_sep
  change (B:ℝ)/4≤(ordinaryLeftWeight hW pi g j:ℝ) ∧ (ordinaryLeftWeight hW pi g j:ℝ)≤B at hL
  have hR' : (B:ℝ)/4≤(ordinaryRightWeight hW pi g j:ℝ) ∧ (ordinaryRightWeight hW pi g j:ℝ)≤B := by
    simp only [ordinaryRightWeight,Int.cast_neg]
    constructor <;> linarith [hR.1,hR.2]
  have hB : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have : (0:ℝ)<(ordinaryLeftWeight hW pi g j:ℝ) := by linarith [hL.1]
    exact_mod_cast this
  · exact_mod_cast hL.2
  · have : (0:ℝ)<(ordinaryRightWeight hW pi g j:ℝ) := by linarith [hR'.1]
    exact_mod_cast this
  · exact_mod_cast hR'.2
  · have : (B:ℝ)≤4*(ordinaryLeftWeight hW pi g j:ℝ) := by linarith [hL.1]
    exact_mod_cast this
  · have : (B:ℝ)≤4*(ordinaryRightWeight hW pi g j:ℝ) := by linarith [hR'.1]
    exact_mod_cast this

/-- All actual palette neighbors and every actual program copy contribute a
residual of absolute value less than 4B on a selected core edge. The recipe's
beta, slopes, and all weights are computed finite fields, not input coefficients. -/
theorem selected_residual {S W D B : ℕ} (A T : ℤ) (hS : 0<S) (hW : 0<W)
    (pi : Equiv.Perm (Fin S)) (g : Geometries S (W-1) B (S*W+D+S*W))
    (hy : StrictMono g.ys) (hD : 2*S*W<D) (p : Placement (recipe A T hW pi g) g)
    (j : Fin S) (s t : Fin W)
    (h : Selected (recipe A T hW pi g) g j W s t
      (g.ys (ProposedPalette.earlyEndpoint S W D pi j s))
      (g.ys (ProposedPalette.lateEndpoint S W D pi j t)))
    (h0 : Selected (recipe A T hW pi g) g j W ⟨0,hW⟩ ⟨0,hW⟩
      (g.ys (ProposedPalette.earlyEndpoint S W D pi j ⟨0,hW⟩))
      (g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩)))
    (hother : ∀k, k≠j → Nonincident g k
      (g.ys (ProposedPalette.earlyEndpoint S W D pi j s))
      (g.ys (ProposedPalette.lateEndpoint S W D pi j t)))
    (hsideL : (g.ordinaryLeft j).2.a<g.ys (ProposedPalette.lateEndpoint S W D pi j t) ↔
      (g.ordinaryLeft j).2.a<g.ys (ProposedPalette.lateEndpoint S W D pi j ⟨0,hW⟩))
    (hsideR : (g.ordinaryRight j).2.a<g.ys (ProposedPalette.earlyEndpoint S W D pi j s) ↔
      (g.ordinaryRight j).2.a<g.ys (ProposedPalette.earlyEndpoint S W D pi j ⟨0,hW⟩))
    (hB : 0<B)
    (hwL : ∀i<W-1, 0<rankLeftWeight g j i ∧ rankLeftWeight g j i≤B)
    (hwR : ∀i<W-1, 0<rankRightWeight g j i ∧ rankRightWeight g j i≤B)
    (huL : 0<ordinaryLeftWeight hW pi g j) (huLB : ordinaryLeftWeight hW pi g j≤B)
    (huR : 0<ordinaryRightWeight hW pi g j) (huRB : ordinaryRightWeight hW pi g j≤B)
    (htL : 0≤A+(j.val:ℤ)*T-(beta hW pi g.ys j-
      RankCorrection.cumulative (rightSlope S W D hW pi j) (rankRightWeight g j) (W-1)))
    (htR : 0≤A+(j.val:ℤ)*T) :
    |ProposedPalette.globalField g.ys (ProposedPalette.indexedSite S W D hW pi)
        (ProposedPalette.earlyEndpoint S W D pi j s) (ProposedPalette.lateEndpoint S W D pi j t)+
      ProgramField.field (B:=B) (recipe A T hW pi g) g.ys p.points
        (ConvexSeparation.original (g.ys (ProposedPalette.earlyEndpoint S W D pi j s)))
        (ConvexSeparation.original (g.ys (ProposedPalette.lateEndpoint S W D pi j t)))|<4*(B:ℤ) := by
  let c := g.ys (ProposedPalette.earlyEndpoint S W D pi j s)
  let b := g.ys (ProposedPalette.lateEndpoint S W D pi j t)
  have hOL : OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2 c b=ordinaryLeftWeight hW pi g j := by
    exact OrdinaryCoreField.incident_rank_independent (g.ordinaryLeft j).2 _ _ _ _
      h.unit_c h0.unit_c h.unit_b h0.unit_b h.ordinary_left_clone h0.ordinary_left_clone
      h.ordinary_left_sep h0.ordinary_left_sep hsideL
  have hOR : OrdinaryCoreField.coreCoefficient (g.ordinaryRight j).2 b c= -ordinaryRightWeight hW pi g j := by
    have hh := OrdinaryCoreField.incident_rank_independent (g.ordinaryRight j).2 _ _ _ _
      h.unit_b h0.unit_b h.unit_c h0.unit_c h.ordinary_right_clone h0.ordinary_right_clone
      h.ordinary_right_sep h0.ordinary_right_sep hsideR
    simpa only [ordinaryRightWeight,neg_neg] using hh
  have hs : s.val≤W-1 := by omega
  have ht : t.val≤W-1 := by omega
  have hp := ProgramCatalog.selected_field (recipe A T hW pi g) g p j W s t c b h hs ht
    (p.original_mem _) (p.original_mem _) hother
  rw [hOL,hOR] at hp
  have hpal := (palette_affine hS hW pi g.ys hy hD j).2.2.2 s t
  rw [hpal,hp]
  have hres := PaletteBounds.selected_residual_bound (beta hW pi g.ys j) A ((j.val:ℤ)*T)
    (ordinaryLeftWeight hW pi g j) (ordinaryRightWeight hW pi g j)
    (leftSlope S W D hW pi j) (rightSlope S W D hW pi j) B (W-1) s.val t.val
    (rankLeftWeight g j) (rankRightWeight g j) hB hs ht hwL hwR huL huLB huR huRB htL htR
  dsimp only at hres
  have hCL : ProgramCount.ordinaryLeft (recipe A T hW pi g) j=
      PaletteForcing.multiplicity ((A:ℚ)+((j.val:ℤ)*T:ℤ)-
        (beta hW pi g.ys j-(RankCorrection.cumulative (rightSlope S W D hW pi j) (rankRightWeight g j) (W-1):ℤ):ℤ))
        (ordinaryLeftWeight hW pi g j) := by
    unfold ProgramCount.ordinaryLeft recipe
    push_cast
    rfl
  have hCR : ProgramCount.ordinaryRight (recipe A T hW pi g) j=
      PaletteForcing.multiplicity ((A:ℚ)+((j.val:ℤ)*T:ℤ)) (ordinaryRightWeight hW pi g j) := by
    unfold ProgramCount.ordinaryRight recipe
    push_cast
    rfl
  rw [hCL,hCR]
  simp only [recipe]
  convert hres using 1
  congr 1
  ring


/-- Actual binary unary cost from all proposed-palette neighbors and all
canonical frozen program fans. -/
noncomputable def unary {S W D B : ℕ} (A T : ℤ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) (p : Placement (recipe A T hW pi g) g)
    (u v : Fin (S*W+D+S*W)) (color : Bool) : ℤ :=
  ProposedPalette.globalCost g.ys (ProposedPalette.indexedSite S W D hW pi) u v color+
    ProgramField.cost (B:=B) (recipe A T hW pi g) g.ys p.points
      (ConvexSeparation.original (g.ys u)) (ConvexSeparation.original (g.ys v)) color

theorem unary_difference {S W D B : ℕ} (A T : ℤ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) (p : Placement (recipe A T hW pi g) g)
    (u v : Fin (S*W+D+S*W)) :
    unary A T hW pi g p u v true-unary A T hW pi g p u v false=
      ProposedPalette.globalField g.ys (ProposedPalette.indexedSite S W D hW pi) u v+
        ProgramField.field (B:=B) (recipe A T hW pi g) g.ys p.points
          (ConvexSeparation.original (g.ys u)) (ConvexSeparation.original (g.ys v)) := by
  unfold unary
  rw [show ∀a b c d : ℤ, (a+b)-(c+d)=(a-c)+(b-d) by intros; ring,
    ProposedPalette.global_cost_difference,ProgramField.cost_difference]

/-- The recipe's natural rank weight is exactly the positive actual response
weight under the already proved early-column geometric conditions. -/
theorem selected_left_weight {S W D B : ℕ} (A T : ℤ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) (j : Fin S) (h : Fin (W-1))
    (hO : 1000≤S*W+D+S*W) (hBO : S*W+D+S*W≤B) (h8 : 8∣B)
    (hcut : (g.rankLeft j h).1≤S*W+D+S*W)
    (hearly : ((g.rankLeft j h).1:ℝ)/((S*W+D+S*W:ℕ):ℝ)≤1/514) :
    totalWeight (B:=B) (g.rankLeft j h).2.ys (leftPoint (g.rankLeft j h).2)=
      ((recipe A T hW pi g).leftWeight j h.val:ℤ) := by
  exact (rankLeftWeight_cast g j h
    (left_weight_bounds (g.rankLeft j h).2 hO hBO hcut h8 hearly).1.le).symm

theorem selected_right_weight {S W D B : ℕ} (A T : ℤ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) (j : Fin S) (h : Fin (W-1))
    (hO : 1000≤S*W+D+S*W) (hBO : S*W+D+S*W≤B) (h8 : 8∣B)
    (hcut : (g.rankRight j h).1≤S*W+D+S*W)
    (hlate : 1-1/514≤((g.rankRight j h).1:ℝ)/((S*W+D+S*W:ℕ):ℝ)) :
    totalWeight (B:=B) (g.rankRight j h).2.ys (rightPoint (g.rankRight j h).2)=
      -((recipe A T hW pi g).rightWeight j h.val:ℤ) := by
  have he := rankRightWeight_cast g j h
    (right_weight_bounds (g.rankRight j h).2 hO hBO hcut h8 hlate).1.le
  change _= -(rankRightWeight g j h.val:ℤ)
  rw [he,neg_neg]

end Q4.Candidate.ActualRecipe
#print axioms Q4.Candidate.ActualRecipe.rankLeftWeight_cast
#print axioms Q4.Candidate.ActualRecipe.rankRightWeight_cast
#print axioms Q4.Candidate.ActualRecipe.rank_left_bounds
#print axioms Q4.Candidate.ActualRecipe.rank_right_bounds
#print axioms Q4.Candidate.ActualRecipe.palette_affine

#print axioms Q4.Candidate.ActualRecipe.ordinary_weights_bounds
#print axioms Q4.Candidate.ActualRecipe.selected_residual

#print axioms Q4.Candidate.ActualRecipe.unary_difference
#print axioms Q4.Candidate.ActualRecipe.selected_left_weight
#print axioms Q4.Candidate.ActualRecipe.selected_right_weight
