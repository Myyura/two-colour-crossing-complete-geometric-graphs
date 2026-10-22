import Q4.Candidate.MacroLayout
import Q4.Candidate.ProposedPalette
import Mathlib.Logic.Equiv.Fin.Basic

namespace Q4.Candidate.OriginalVertexLayout
open Q4.Candidate.MacroLayout Q4.Candidate.SourceChordGeometry
open Q4.Candidate.RankGap Q4.Candidate.GlobalGeometryScales Q4.Candidate.ConvexSeparation
open Q4.Candidate.OrdinaryNonincident Q4.Candidate.GeometryEncoding

def flatClone (n q W : ℕ) (tau base : ℚ) (i : Fin (n*q*W)) : ℚ :=
  cloneAt (macroParameter n q base (i.val/W)) tau W (i.val%W)

theorem flatClone_bounds (n q W : ℕ) (tau base : ℚ) (hW : 2 ≤ W) (ht : 0 ≤ tau)
    (i : Fin (n*q*W)) :
    macroParameter n q base (i.val/W)-tau/2 ≤ flatClone n q W tau base i ∧
    flatClone n q W tau base i ≤ macroParameter n q base (i.val/W)+tau/2 := by
  have hr : i.val%W < W := Nat.mod_lt _ (by omega)
  exact clone_bounds _ tau W (i.val%W) ht (by exact_mod_cast hW) (by positivity)
    (by have hr' : ((i.val%W:ℕ):ℚ)+1 ≤ W := by exact_mod_cast (show i.val%W+1 ≤ W by omega)
        linarith)

theorem flatClone_strictMono (n q W : ℕ) (tau base : ℚ) (hW : 2 ≤ W)
    (ht : 0 < tau) (hsmall : tau < 1/(8*((n*q:ℕ)+1))) :
    StrictMono (flatClone n q W tau base) := by
  intro i j hij
  have hq : i.val/W ≤ j.val/W := Nat.div_le_div_right (Nat.le_of_lt hij)
  rcases lt_or_eq_of_le hq with hlt | heq
  · have hi := flatClone_bounds n q W tau base hW ht.le i
    have hj := flatClone_bounds n q W tau base hW ht.le j
    have hgap := macro_gap n q (i.val/W) (j.val/W) base hlt
    linarith
  · have hr : i.val%W < j.val%W := by
      have hi := Nat.mod_add_div i.val W
      have hj := Nat.mod_add_div j.val W
      rw [heq] at hi
      omega
    have hw : (0:ℚ) < (W:ℚ)-1 := by exact_mod_cast (show 0 < (W:ℤ)-1 by omega)
    unfold flatClone cloneAt
    rw [heq,add_lt_add_iff_left,mul_lt_mul_iff_of_pos_left ht,sub_lt_sub_iff_right,
      div_lt_div_iff_of_pos_right hw]
    exact_mod_cast hr

theorem flatClone_regions (n q D W B : ℕ) (hW : 2 ≤ W) (i : Fin (n*q*W)) :
    (-1 < flatClone n q W (cloneScale (macros n q D) W B) (-3/4) i ∧
      flatClone n q W (cloneScale (macros n q D) W B) (-3/4) i < -1/2) ∧
    (1/2 < flatClone n q W (cloneScale (macros n q D) W B) (5/8) i ∧
      flatClone n q W (cloneScale (macros n q D) W B) (5/8) i < 1) := by
  have hi : i.val/W < n*q := (Nat.div_lt_iff_lt_mul (by omega : 0<W)).2 i.isLt
  have hm1 := source_mesh_bounds n q (-3/4) ⟨_,hi⟩
  have hm2 := source_mesh_bounds n q (5/8) ⟨_,hi⟩
  dsimp only [Fin.val_mk] at hm1 hm2
  have hs := common_scale_bounds (macros n q D) W B
  have ht0 := hs.2.2.2.1
  have ht := hs.2.2.2.2.1
  have he1 := macroSpacing_le_one (macros n q D)
  have hc1 := flatClone_bounds n q W (cloneScale (macros n q D) W B) (-3/4) hW ht0.le i
  have hc2 := flatClone_bounds n q W (cloneScale (macros n q D) W B) (5/8) hW ht0.le i
  constructor <;> constructor <;> linarith

/-- Actual physical order: all early clone blocks, central dummies, then
all late clone blocks. Source labels do not alter these coordinates. -/
noncomputable def parameter (n q D W B : ℕ) (i : Fin (n*q*W+D+n*q*W)) : ℚ :=
  if he : i.val < n*q*W then
    flatClone n q W (cloneScale (macros n q D) W B) (-3/4) ⟨i.val,he⟩
  else if hd : i.val < n*q*W+D then
    dummyParameter D ⟨i.val-n*q*W,by omega⟩
  else
    flatClone n q W (cloneScale (macros n q D) W B) (5/8) ⟨i.val-(n*q*W+D),by omega⟩

theorem parameter_strictMono (n q D W B : ℕ) (hW : 2 ≤ W) :
    StrictMono (parameter n q D W B) := by
  have ht := common_source_width n q D W B
  have he := flatClone_strictMono n q W _ (-3/4) hW ht.1 ht.2
  have hl := flatClone_strictMono n q W _ (5/8) hW ht.1 ht.2
  intro i j hij
  unfold parameter
  split_ifs with hi hi' hj hj' hj hj'
  · exact he hij
  · have h1 := (flatClone_regions n q D W B hW ⟨i.val,hi⟩).1.2
    have h2 := (dummy_bounds D ⟨j.val-n*q*W,by omega⟩).1
    linarith
  · have h1 := (flatClone_regions n q D W B hW ⟨i.val,hi⟩).1.2
    have h2 := (flatClone_regions n q D W B hW ⟨j.val-(n*q*W+D),by omega⟩).2.1
    linarith
  · exfalso; omega
  · apply dummy_strictMono D
    change i.val-n*q*W < j.val-n*q*W
    omega
  · have h1 := (dummy_bounds D ⟨i.val-n*q*W,by omega⟩).2
    have h2 := (flatClone_regions n q D W B hW ⟨j.val-(n*q*W+D),by omega⟩).2.1
    linarith
  · exfalso; omega
  · exfalso; omega
  · apply hl
    change i.val-(n*q*W+D) < j.val-(n*q*W+D)
    omega

theorem parameter_unit (n q D W B : ℕ) (hW : 2 ≤ W) (i : Fin (n*q*W+D+n*q*W)) :
    -1 < parameter n q D W B i ∧ parameter n q D W B i < 1 := by
  unfold parameter
  split_ifs with he hd
  · have h := (flatClone_regions n q D W B hW ⟨i.val,he⟩).1
    constructor <;> linarith
  · have h := dummy_bounds D ⟨i.val-n*q*W,by omega⟩
    constructor <;> linarith
  · have h := (flatClone_regions n q D W B hW ⟨i.val-(n*q*W+D),by omega⟩).2
    constructor <;> linarith

theorem parameter_provenance (n q D W B : ℕ) (hW : 2 ≤ W) (i : Fin (n*q*W+D+n*q*W)) :
    ActualBase (macros n q D) W B (original (parameter n q D W B i)) := by
  unfold parameter
  split_ifs with he hd
  · have hi : i.val/W < n*q := (Nat.div_lt_iff_lt_mul (by omega : 0<W)).2 he
    refine Or.inr (Or.inl ⟨_,mem_early n q D ⟨_,hi⟩,i.val%W,?_,rfl⟩)
    exact Nat.le_of_lt (Nat.mod_lt _ (by omega))
  · exact Or.inl ⟨_,mem_dummy n q D ⟨i.val-n*q*W,by omega⟩,rfl⟩
  · have hi : (i.val-(n*q*W+D))/W < n*q :=
      (Nat.div_lt_iff_lt_mul (by omega : 0<W)).2 (by omega)
    refine Or.inr (Or.inl ⟨_,mem_late n q D ⟨_,hi⟩,(i.val-(n*q*W+D))%W,?_,rfl⟩)
    exact Nat.le_of_lt (Nat.mod_lt _ (by omega))

theorem block_rank_lt (n q W : ℕ) (b : Fin (n*q)) (r : Fin W) : b.val*W+r.val < n*q*W := by
  have hb : (b.val+1)*W ≤ n*q*W := Nat.mul_le_mul_right W (by omega)
  nlinarith [r.isLt]

def earlyIndex (n q D W : ℕ) (b : Fin (n*q)) (r : Fin W) : Fin (n*q*W+D+n*q*W) :=
  ⟨b.val*W+r.val,by have := block_rank_lt n q W b r; omega⟩

def lateIndex (n q D W : ℕ) (b : Fin (n*q)) (r : Fin W) : Fin (n*q*W+D+n*q*W) :=
  ⟨n*q*W+D+(b.val*W+r.val),by have := block_rank_lt n q W b r; omega⟩

theorem flatClone_block (n q W : ℕ) (tau base : ℚ) (hW : 2 ≤ W)
    (b : Fin (n*q)) (r : Fin W) :
    flatClone n q W tau base ⟨b.val*W+r.val,block_rank_lt n q W b r⟩ =
      cloneAt (macroParameter n q base b.val) tau W r.val := by
  have hd : (b.val*W+r.val)/W=b.val := by
    rw [Nat.mul_comm b.val W,Nat.mul_add_div (by omega : 0<W),Nat.div_eq_of_lt r.isLt,Nat.add_zero]
  have hm : (b.val*W+r.val)%W=r.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt r.isLt]
  simp only [flatClone,hd,hm]

theorem parameter_early (n q D W B : ℕ) (hW : 2 ≤ W) (b : Fin (n*q)) (r : Fin W) :
    parameter n q D W B (earlyIndex n q D W b r) =
      cloneAt (macroParameter n q (-3/4) b.val) (cloneScale (macros n q D) W B) W r.val := by
  have he : (earlyIndex n q D W b r).val < n*q*W := block_rank_lt n q W b r
  rw [parameter]
  simp only [he,↓reduceDIte]
  exact flatClone_block n q W _ _ hW b r

/-- Encodes (source vertex, independent copy) in its actual early block. -/
def sourceBlock {n q : ℕ} (v : Fin n) (j : Fin q) : Fin (n*q) :=
  ⟨blockIndex v j,blockIndex_bound v j⟩

theorem sourceBlock_equiv {n q : ℕ} (v : Fin n) (j : Fin q) :
    sourceBlock v j=finProdFinEquiv (v,j) := by
  apply Fin.ext
  simp only [sourceBlock,blockIndex,finProdFinEquiv,Equiv.coe_fn_mk]
  ring

/-- Maps an early block to its physical late block, reversing both the
source permutation order and the independent-copy order. -/
def latePhysical {n q : ℕ} (pi : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n*q)) :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr (pi.trans Fin.revPerm) Fin.revPerm).trans finProdFinEquiv)

/-- indexedSite needs the inverse direction: physical late block to its
early source label. This distinction is essential for the palette fibers. -/
def sitePermutation {n q : ℕ} (pi : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n*q)) :=
  (latePhysical (q:=q) pi).symm

theorem latePhysical_sourceBlock {n q : ℕ} (pi : Equiv.Perm (Fin n)) (v : Fin n) (j : Fin q) :
    latePhysical pi (sourceBlock v j)=sourceBlock (pi v).rev j.rev := by
  rw [sourceBlock_equiv,sourceBlock_equiv]
  simp [latePhysical,Equiv.trans_apply,Fin.revPerm]

theorem site_source_fibers {n q : ℕ} (D W : ℕ) (hW : 0<W)
    (pi : Equiv.Perm (Fin n)) (v : Fin n) (j : Fin q) :
    Q4.Candidate.ProposedPalette.BlockFibers
      (Q4.Candidate.ProposedPalette.indexedSite (n*q) W D hW (sitePermutation pi)) W
      ((sourceBlock v j).val*W) (n*q*W+D+(sourceBlock (pi v).rev j.rev).val*W)
      (sourceBlock v j) := by
  have hh := Q4.Candidate.ProposedPalette.indexed_fibers (n*q) W D hW (sitePermutation pi) (sourceBlock v j)
  simpa only [sitePermutation,Equiv.symm_symm,latePhysical_sourceBlock] using hh

theorem parameter_late (n q D W B : ℕ) (hW : 2 ≤ W) (b : Fin (n*q)) (r : Fin W) :
    parameter n q D W B (lateIndex n q D W b r) =
      cloneAt (macroParameter n q (5/8) b.val) (cloneScale (macros n q D) W B) W r.val := by
  rw [parameter,dite_eq_right (by dsimp [lateIndex]; omega),dite_eq_right (by dsimp [lateIndex]; omega)]
  have he : ((lateIndex n q D W b r).val-(n*q*W+D))=b.val*W+r.val := by simp [lateIndex]
  simp only [he]
  exact flatClone_block n q W _ _ hW b r

theorem parameter_source_early {n q : ℕ} (D W B : ℕ) (hW : 2 ≤ W)
    (v : Fin n) (j : Fin q) (r : Fin W) :
    parameter n q D W B (earlyIndex n q D W (sourceBlock v j) r)=
      early (cloneScale (macros n q D) W B) v j r :=
  parameter_early n q D W B hW (sourceBlock v j) r

theorem parameter_source_late {n q : ℕ} (D W B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (v : Fin n) (j : Fin q) (r : Fin W) :
    parameter n q D W B (lateIndex n q D W (sourceBlock (pi v).rev j.rev) r)=
      late pi (cloneScale (macros n q D) W B) v j r :=
  parameter_late n q D W B hW (sourceBlock (pi v).rev j.rev) r

/-- The source chord model and the actual full vertex array use exactly
the same endpoints, including copy reversal in the physical late order. -/
theorem source_endpoints_match {n q : ℕ} (D W B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (v : Fin n) (j : Fin q) (r t : Fin W) :
    (original (parameter n q D W B (earlyIndex n q D W (sourceBlock v j) r)),
      original (parameter n q D W B (lateIndex n q D W (sourceBlock (pi v).rev j.rev) t))) =
    (original (early (cloneScale (macros n q D) W B) v j r),
      original (late pi (cloneScale (macros n q D) W B) v j t)) := by
  rw [parameter_source_early D W B hW,parameter_source_late D W B hW]

open Q4.Candidate.ProposedPalette in
theorem palette_endpoints_match {n q : ℕ} (D W : ℕ) (pi : Equiv.Perm (Fin n))
    (v : Fin n) (j : Fin q) (r t : Fin W) :
    earlyEndpoint (n*q) W D (sitePermutation pi) (sourceBlock v j) r =
      earlyIndex n q D W (sourceBlock v j) r ∧
    lateEndpoint (n*q) W D (sitePermutation pi) (sourceBlock v j) t =
      lateIndex n q D W (sourceBlock (pi v).rev j.rev) t := by
  constructor
  · rfl
  · apply Fin.ext
    simp only [lateEndpoint,Q4.Candidate.PaletteCounting.endpoint,lateIndex,sitePermutation,
      Equiv.symm_symm,latePhysical_sourceBlock]
    omega

open Q4.Candidate.DoubleCapGrid Q4.Candidate.RationalEncoding

noncomputable def originalParameters (n q D W B : ℕ) : Finset ℚ :=
  Finset.univ.image (parameter n q D W B)

def frameParameters (B : ℕ) : Finset ℚ := Finset.univ.image (frameParameter B)

noncomputable def fixedBase (n q D W B : ℕ) : Finset Point :=
  basePoints (originalParameters n q D W B) (frameParameters B)

theorem parameter_abs (n q D W B : ℕ) (hW : 2 ≤ W) (i : Fin (n*q*W+D+n*q*W)) :
    |parameter n q D W B i| ≤ 1 := by
  have hh := parameter_unit n q D W B hW i
  exact abs_le.mpr ⟨hh.1.le,hh.2.le⟩

theorem fixedBase_general_position (n q D W B : ℕ) (hW : 2 ≤ W) :
    GeneralPosition (fixedBase n q D W B) := by
  apply base_general_position
  · intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact parameter_abs n q D W B hW i
  · intro t ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    exact (frameParameter_unit B i).le

theorem fixedBase_card (n q D W B : ℕ) (hW : 2 ≤ W) :
    (fixedBase n q D W B).card=n*q*W+D+n*q*W+B := by
  rw [fixedBase,base_card]
  unfold originalParameters frameParameters
  rw [Finset.card_image_of_injective _ (parameter_strictMono n q D W B hW).injective,
    Finset.card_image_of_injective _ (frameParameter_antitone B).injective]
  simp

theorem fixedBase_provenance (n q D W B : ℕ) (hW : 2 ≤ W) :
    ∀p∈fixedBase n q D W B, ActualBase (macros n q D) W B p := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact parameter_provenance n q D W B hW i
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact Or.inr (Or.inr ⟨i,rfl⟩)

theorem fixedBase_encoding (n q D W B H : ℕ) (hW : 2 ≤ W) (hH : 10000 ≤ H)
    (hWH : W ≤ H) (hBH : B ≤ H) (hs : 8*(n*q+1) ≤ H) (hd : 4*(D+1) ≤ H) :
    ∀p∈fixedBase n q D W B, PointBounded p H 300 := by
  intro p hp
  exact actual_base_encoding (macros n q D) W B H hH hWH hBH (macros_encoding n q D H hs hd)
    p (fixedBase_provenance n q D W B hW p hp)

theorem actual_grid_crossing (n q D W B : ℕ) (hW : 2 ≤ W)
    (p z : Fin B × Fin (n*q*W+D+n*q*W)) :
    ProperCross (original (parameter n q D W B p.2)) (frame (frameParameter B p.1))
      (original (parameter n q D W B z.2)) (frame (frameParameter B z.1)) ↔
      (p.1<z.1 ∧ p.2<z.2) ∨ (z.1<p.1 ∧ z.2<p.2) :=
  actual_frame_grid_crossing B _ _ (parameter_strictMono n q D W B hW)
    (parameter_abs n q D W B hW) p z

#print axioms flatClone_strictMono
#print axioms parameter_strictMono
#print axioms parameter_unit
#print axioms parameter_provenance
#print axioms latePhysical_sourceBlock
#print axioms site_source_fibers
#print axioms source_endpoints_match
#print axioms palette_endpoints_match
#print axioms fixedBase_general_position
#print axioms fixedBase_card
#print axioms fixedBase_provenance
#print axioms fixedBase_encoding
#print axioms actual_grid_crossing

end Q4.Candidate.OriginalVertexLayout

