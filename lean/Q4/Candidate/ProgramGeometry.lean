import Q4.Candidate.OriginalVertexLayout
import Q4.Candidate.ProgramCatalog
import Q4.Candidate.CompleteFanFields

/-! Actual geometry witnesses for every source macro ordinary and rank
prototype in the concrete original-vertex array. -/
namespace Q4.Candidate.ProgramGeometry
open Q4.Candidate.ConvexSeparation Q4.Candidate.OriginalVertexLayout
open Q4.Candidate.MacroLayout Q4.Candidate.GlobalGeometryScales
open Q4.Candidate.OrdinaryNonincident Q4.Candidate.SourceChordGeometry
open Q4.Candidate.RankGap Q4.Candidate.PaletteCounting Q4.Candidate.ProposedPalette
attribute [local instance] Classical.propDecidable

abbrev O (n q D W : ℕ) := n*q*W+D+n*q*W

noncomputable def macroAt (n q D W : ℕ) (i : Fin (O n q D W)) : ℚ :=
  if he : i.val < n*q*W then macroParameter n q (-3/4) (i.val/W)
  else if hd : i.val < n*q*W+D then dummyParameter D ⟨i.val-n*q*W,by omega⟩
  else macroParameter n q (5/8) ((i.val-(n*q*W+D))/W)

theorem macroAt_mem (n q D W : ℕ) (hW : 2  ≤  W) (i : Fin (O n q D W)) :
    macroAt n q D W i ∈ macros n q D := by
  unfold macroAt
  split_ifs with he hd
  · exact mem_early n q D ⟨i.val/W,(Nat.div_lt_iff_lt_mul (by omega : 0 < W)).2 he⟩
  · exact mem_dummy n q D _
  · exact mem_late n q D ⟨_,(Nat.div_lt_iff_lt_mul (by omega : 0 < W)).2 (by have hi : i.val  <  n*q*W+D+n*q*W := i.isLt; omega)⟩

theorem parameter_near_macro (n q D W B : ℕ) (hW : 2  ≤  W) (i : Fin (O n q D W)) :
    |parameter n q D W B i-macroAt n q D W i|  ≤  cloneScale (macros n q D) W B/2 := by
  have ht := (common_source_width n q D W B).1
  unfold parameter macroAt
  split_ifs with he hd
  · have hh := flatClone_bounds n q W _ (-3/4) hW ht.le ⟨i.val,he⟩
    apply abs_le.mpr; constructor  <;> linarith
  · simp only [sub_self,abs_zero]
    positivity
  · have hh := flatClone_bounds n q W _ (5/8) hW ht.le ⟨i.val-(n*q*W+D),by omega⟩
    apply abs_le.mpr; constructor  <;> linarith

/-- A source macro's actual consecutive W-clone interval. The final early
and late instances below prove every field from the concrete array. -/
structure Block (n q D W B : ℕ) where
  a : ℚ
  start : ℕ
  fits : start+W  ≤  O n q D W
  mem : a∈macros n q D
  coordinates : ∀r : Fin W, parameter n q D W B (endpoint start fits r)=
    cloneAt a (cloneScale (macros n q D) W B) W r.val

noncomputable def Block.parent {n q D W B : ℕ} (b : Block n q D W B) : Finset (Fin (O n q D W)) :=
  Finset.univ.image (endpoint b.start b.fits)

theorem Block.mem_parent {n q D W B : ℕ} (b : Block n q D W B) (i : Fin (O n q D W)) :
    i∈b.parent ↔ b.start ≤ i.val ∧ i.val < b.start+W := by
  constructor
  · intro h
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp h
    simp only [endpoint,Fin.val_mk]
    omega
  · intro h
    obtain ⟨r,rfl⟩ := endpoint_exists b.fits i h
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩

theorem Block.parent_card {n q D W B : ℕ} (b : Block n q D W B) : b.parent.card=W := by
  have hinj : Function.Injective (endpoint b.start b.fits) := by
    intro r t h
    apply Fin.ext
    have he := congrArg Fin.val h
    simp only [endpoint,Fin.val_mk] at he
    omega
  rw [Block.parent,Finset.card_image_of_injective _ hinj]
  simp

theorem clone_first_last (a tau : ℚ) (W : ℕ) (hW : 2  ≤  W) :
    cloneAt a tau W 0=a-tau/2 ∧ cloneAt a tau W (W-1)=a+tau/2 := by
  have hw : (W:ℚ)-1≠0 := by
    have hw' : (2:ℚ) ≤ W := by exact_mod_cast hW
    linarith
  constructor
  · unfold cloneAt; ring
  · unfold cloneAt
    rw [div_self hw]
    ring

theorem Block.outside_bounds {n q D W B : ℕ} (b : Block n q D W B) (hW : 2  ≤  W)
    (i : Fin (O n q D W)) (hi : i∉b.parent) :
    (i.val < b.start ∧ parameter n q D W B i < b.a-cloneScale (macros n q D) W B/2) ∨
    (b.start+W ≤ i.val ∧ b.a+cloneScale (macros n q D) W B/2 < parameter n q D W B i) := by
  have hnot := (b.mem_parent i).not.mp hi
  have hmono := parameter_strictMono n q D W B hW
  have hfirst := b.coordinates ⟨0,by omega⟩
  have hlast := b.coordinates ⟨W-1,by omega⟩
  have hfl := clone_first_last b.a (cloneScale (macros n q D) W B) W hW
  simp only [Nat.cast_zero] at hfirst
  rw [hfl.1] at hfirst
  have hcast : ((W-1:ℕ):ℚ)=(W:ℚ)-1 := by exact_mod_cast (show (W:ℤ)-1=↑(W-1) by omega).symm
  dsimp only [Fin.val_mk] at hlast
  rw [hcast,hfl.2] at hlast
  by_cases hbefore : i.val < b.start
  · refine Or.inl ⟨hbefore,?_⟩
    rw [←hfirst]
    apply hmono
    change i.val < b.start+0
    omega
  · have hafter : b.start+W ≤ i.val := by omega
    refine Or.inr ⟨hafter,?_⟩
    rw [←hlast]
    apply hmono
    change b.start+(W-1) < i.val
    omega

theorem Block.nonparent_macro_ne {n q D W B : ℕ} (b : Block n q D W B) (hW : 2  ≤  W)
    (i : Fin (O n q D W)) (hi : i∉b.parent) : macroAt n q D W i≠b.a := by
  intro he
  have hc := parameter_near_macro n q D W B hW i
  rw [he] at hc
  have hc' := abs_le.mp hc
  rcases b.outside_bounds hW i hi with hh|hh  <;> linarith [hh.2]

theorem Block.outside_order {n q D W B : ℕ} (b : Block n q D W B) (hW : 2  ≤  W)
    (i : Fin (O n q D W)) (hi : i∉b.parent) :
    (parameter n q D W B i < b.a ↔ i.val < b.start) ∧
    (b.a < parameter n q D W B i ↔ b.start ≤ i.val) := by
  have ht := (common_source_width n q D W B).1
  rcases b.outside_bounds hW i hi with hh|hh
  · have hlo : parameter n q D W B i < b.a := by linarith [hh.2]
    exact ⟨by simp [hlo,hh.1],by simp [not_lt_of_gt hlo,not_le.mpr hh.1]⟩
  · have hhi : b.a < parameter n q D W B i := by linarith [hh.2]
    have hstart : b.start ≤ i.val := by omega
    exact ⟨by simp [not_lt_of_gt hhi,not_lt.mpr hstart],by simp [hhi,hstart]⟩

theorem Block.unit_a {n q D W B : ℕ} (b : Block n q D W B) : |b.a| ≤ 1 :=
  (macro_box n q D b.a b.mem).trans (by norm_num)

theorem Block.nonparent_sep {n q D W B : ℕ} (b : Block n q D W B) (hW : 2  ≤  W)
    (i : Fin (O n q D W)) (hi : i∉b.parent) :
    5*programScale (macros n q D) W  ≤  |parameter n q D W B i-b.a| :=
  (nonparent_ray_margins (macros n q D) W B b.a b.a (macroAt n q D W i)
    (parameter n q D W B i) b.mem (macroAt_mem n q D W hW i)
    (b.nonparent_macro_ne hW i hi) b.unit_a b.unit_a (parameter_near_macro n q D W B hW i)).1

theorem fin_rank_bound {W : ℕ} (r : Fin W) : (r.val:ℚ) ≤ (W:ℚ)-1 := by
  have hr : (r.val:ℚ)+1  ≤  W := by exact_mod_cast (show r.val+1 ≤ W by omega)
  linarith

theorem Block.parent_clone {n q D W B : ℕ} (b : Block n q D W B)
    (i : Fin (O n q D W)) (hi : i∈b.parent) :
    ∃s : ℚ, 0 ≤ s ∧ s ≤ (W:ℚ)-1 ∧
      parameter n q D W B i=cloneAt b.a (cloneScale (macros n q D) W B) W s := by
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hi
  exact ⟨r.val,by positivity,fin_rank_bound r,b.coordinates r⟩

noncomputable def Block.ordinaryGeometry {n q D W B : ℕ} (b : Block n q D W B)
    (hW : 2  ≤  W) (hEven : Even B) : Q4.Candidate.OrdinaryResponse.Geometry B (O n q D W) b.start where
  ys := parameter n q D W B
  a := b.a
  mu := programScale (macros n q D) W
  parent := b.parent
  even := hEven
  unit_a := b.unit_a
  unit_y := parameter_abs n q D W B hW
  mu_pos := (common_scale_bounds (macros n q D) W B).1
  mu_le := by have hh := (common_scale_bounds (macros n q D) W B).2.1; linarith
  clone := by
    intro i hi
    obtain ⟨s,hs,hs1,hys⟩ := b.parent_clone i hi
    rw [hys]
    exact (actual_clone_conditions (macros n q D) W B b.a s hW hs hs1).2
  sep := b.nonparent_sep hW
  left := fun i hi => (b.outside_order hW i hi).1
  right := fun i hi => (b.outside_order hW i hi).2

noncomputable def earlyBlock (n q D W B : ℕ) (hW : 2  ≤  W) (j : Fin (n*q)) : Block n q D W B where
  a := macroParameter n q (-3/4) j.val
  start := j.val*W
  fits := by have hj := Nat.mul_le_mul_right W (show j.val+1 ≤ n*q by omega); dsimp [O]; nlinarith
  mem := mem_early n q D j
  coordinates := fun r => parameter_early n q D W B hW j r

noncomputable def lateBlock (n q D W B : ℕ) (hW : 2  ≤  W) (j : Fin (n*q)) : Block n q D W B where
  a := macroParameter n q (5/8) j.val
  start := n*q*W+D+j.val*W
  fits := by have hj := Nat.mul_le_mul_right W (show j.val+1 ≤ n*q by omega); dsimp [O]; nlinarith
  mem := mem_late n q D j
  coordinates := by
    intro r
    have he : endpoint (n*q*W+D+j.val*W) (by have hj := Nat.mul_le_mul_right W (show j.val+1 ≤ n*q by omega); nlinarith) r =
        lateIndex n q D W j r := by
      apply Fin.ext
      simp only [endpoint,lateIndex,Fin.val_mk]
      omega
    rw [he]
    exact parameter_late n q D W B hW j r

theorem early_late_order (n q D W B : ℕ) (hW : 2  ≤  W) (j k : Fin (n*q)) :
    (earlyBlock n q D W B hW j).a < (lateBlock n q D W B hW k).a := by
  have hl := source_mesh_bounds n q (-3/4) j
  have hr := source_mesh_bounds n q (5/8) k
  dsimp [earlyBlock,lateBlock]
  linarith

theorem gap_rank_bound {W : ℕ} (ell : Fin (W-1)) : (ell.val:ℚ)+1 ≤ (W:ℚ)-1 := by
  have hh : ell.val+2 ≤ W := by omega
  have hh' : (ell.val:ℚ)+2 ≤ W := by exact_mod_cast hh
  linarith

noncomputable def Block.rankParameters {n q D W B : ℕ} (left right : Block n q D W B)
    (hW : 2 ≤ W) (hab : left.a < right.a) (ell : Fin (W-1)) : Q4.Candidate.RankSoftRows.Parameters where
  a := left.a
  b := right.a
  tau := cloneScale (macros n q D) W B
  w := W
  mu := programScale (macros n q D) W
  ell := ell.val
  ordered := hab
  width := by exact_mod_cast hW
  mu_pos := (common_scale_bounds (macros n q D) W B).1
  mu_small := (common_scale_bounds (macros n q D) W B).2.2.1
  tau_pos := (common_scale_bounds (macros n q D) W B).2.2.2.1
  tau_small := (pair_scale_conditions (macros n q D) W B left.a right.a left.mem right.mem hab).1
  box_a := (global_clone_box (macros n q D) W B left.a (macro_box n q D left.a left.mem)).1.le
  box_b := (global_clone_box (macros n q D) W B right.a (macro_box n q D right.a right.mem)).2.le
  gap_lo := Nat.cast_nonneg _
  gap_hi := gap_rank_bound ell

theorem Block.rank_sep {n q D W B : ℕ} (parent other : Block n q D W B) (hW : 2 ≤ W)
    (i : Fin (O n q D W)) (hi : i∉parent.parent) :
    2*programScale (macros n q D) W*|other.a-parent.a| ≤ |parameter n q D W B i-parent.a| := by
  have hd : |other.a-parent.a| ≤ 2 := (abs_sub _ _).trans (by linarith [other.unit_a,parent.unit_a])
  have hm := (common_scale_bounds (macros n q D) W B).1
  have hh := parent.nonparent_sep hW i hi
  nlinarith [mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*programScale (macros n q D) W by positivity)]

noncomputable def Block.leftGeometry {n q D W B : ℕ} (left right : Block n q D W B)
    (hW : 2 ≤ W) (hab : left.a < right.a) (ell : Fin (W-1)) :
    Q4.Candidate.RankSoftRows.LeftGeometry B (O n q D W) (left.start+W) where
  toParameters := left.rankParameters right hW hab ell
  ys := parameter n q D W B
  parent := left.parent
  unit_y := parameter_abs n q D W B hW
  parent_clone := left.parent_clone
  parent_index := fun i hi => ((left.mem_parent i).mp hi).2
  nonparent_sep := by
    intro i hi
    have hh := left.rank_sep right hW i hi
    simpa only [Block.rankParameters,abs_of_pos (sub_pos.mpr hab)] using hh
  lower_index := by
    intro i hi
    have hh := (left.outside_order hW i hi).1
    have hn := (left.mem_parent i).not.mp hi
    change parameter n q D W B i < left.a ↔ i.val < left.start+W
    rw [hh]
    omega
  upper_index := by
    intro i hi
    have hh := (left.outside_order hW i hi).2
    have hn := (left.mem_parent i).not.mp hi
    change left.a < parameter n q D W B i ↔ left.start+W ≤ i.val
    rw [hh]
    omega

noncomputable def Block.rightGeometry {n q D W B : ℕ} (left right : Block n q D W B)
    (hW : 2 ≤ W) (hab : left.a < right.a) (ell : Fin (W-1)) :
    Q4.Candidate.RankSoftRows.RightGeometry B (O n q D W) right.start where
  toParameters := left.rankParameters right hW hab ell
  ys := parameter n q D W B
  parent := right.parent
  unit_y := parameter_abs n q D W B hW
  parent_clone := right.parent_clone
  parent_index := fun i hi => ((right.mem_parent i).mp hi).1
  nonparent_sep := by
    intro i hi
    have hh := right.rank_sep left hW i hi
    simpa only [Block.rankParameters,abs_of_neg (sub_neg.mpr hab),neg_sub] using hh
  lower_index := fun i hi => (right.outside_order hW i hi).1
  upper_index := fun i hi => (right.outside_order hW i hi).2

/-- Every ordinary and rank witness is now instantiated from the actual
original array, source permutation, common scales and finite clone indices. -/
noncomputable def geometries (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) : Q4.Candidate.ProgramCatalog.Geometries (n*q) (W-1) B (O n q D W) where
  ys := parameter n q D W B
  ordinaryLeft j := ⟨_,(earlyBlock n q D W B hW j).ordinaryGeometry hW hEven⟩
  ordinaryRight j := ⟨_,(lateBlock n q D W B hW (latePhysical pi j)).ordinaryGeometry hW hEven⟩
  rankLeft j ell := ⟨_,(earlyBlock n q D W B hW j).leftGeometry
    (lateBlock n q D W B hW (latePhysical pi j)) hW
    (early_late_order n q D W B hW j (latePhysical pi j)) ell⟩
  rankRight j ell := ⟨_,(earlyBlock n q D W B hW j).rightGeometry
    (lateBlock n q D W B hW (latePhysical pi j)) hW
    (early_late_order n q D W B hW j (latePhysical pi j)) ell⟩
  ys_ol := fun _ => rfl
  ys_or := fun _ => rfl
  ys_rl := fun _ _ => rfl
  ys_rr := fun _ _ => rfl

theorem proportions (n q D W : ℕ) (hD : D=512*(n*q)*W) (hS : 0 < n*q) (hW : 2 ≤ W) :
    1000 ≤ O n q D W ∧ (W:ℝ)/(O n q D W) ≤ 1/514 ∧
    (∀r : ℕ, r ≤ n*q*W → (r:ℝ)/(O n q D W) ≤ 1/514) ∧
    (∀r : ℕ, n*q*W+D ≤ r → 1-1/514 ≤ (r:ℝ)/(O n q D W)) := by
  have hS1 : 1 ≤ n*q := hS
  have hSW : 2 ≤ n*q*W := by nlinarith
  have he : O n q D W=514*(n*q*W) := by dsimp [O]; rw [hD]; ring
  have he' : (O n q D W:ℝ)=514*((n*q*W:ℕ):ℝ) := by exact_mod_cast he
  have hp : (0:ℝ) < O n q D W := by rw [he']; positivity
  have hwr : (W:ℝ) ≤ (n*q*W:ℕ) := by exact_mod_cast (show W ≤ n*q*W by nlinarith)
  refine ⟨by omega,?_,?_,?_⟩
  · apply (div_le_iff₀ hp).2
    nlinarith
  · intro r hr
    have hr' : (r:ℝ) ≤ (n*q*W:ℕ) := by exact_mod_cast hr
    apply (div_le_iff₀ hp).2
    nlinarith
  · intro r hr
    have hrn : 513*(n*q*W) ≤ r := by rw [hD] at hr; nlinarith
    have hr' : 513*((n*q*W:ℕ):ℝ) ≤ (r:ℝ) := by exact_mod_cast hrn
    apply (le_div_iff₀ hp).2
    nlinarith

theorem catalog_cuts (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (j : Fin (n*q)) (ell : Fin (W-1)) :
    ((geometries n q D W B hW hEven pi).ordinaryLeft j).1  ≤  n*q*W ∧
    ((geometries n q D W B hW hEven pi).rankLeft j ell).1  ≤  n*q*W ∧
    n*q*W+D ≤ ((geometries n q D W B hW hEven pi).ordinaryRight j).1 ∧
    n*q*W+D ≤ ((geometries n q D W B hW hEven pi).rankRight j ell).1 ∧
    ((geometries n q D W B hW hEven pi).ordinaryRight j).1 ≤ O n q D W ∧
    ((geometries n q D W B hW hEven pi).rankRight j ell).1 ≤ O n q D W := by
  have hl := Nat.mul_le_mul_right W (show j.val+1 ≤ n*q by omega)
  have hr := Nat.mul_le_mul_right W (show (latePhysical pi j).val+1 ≤ n*q by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hl hr
  dsimp [geometries,earlyBlock,lateBlock,O]
  omega

open Q4.Candidate.ProgramCount Q4.Candidate.ProgramField Q4.Candidate.ProgramCatalog
open Q4.Candidate.RankSoftRows Q4.Candidate.CompleteFanFields

theorem prototype_below (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q)) (l : Label d (W-1)) :
    phi (prototype d (geometries n q D W B hW hEven pi).prototypes l) < 0 ∧
      |(prototype d (geometries n q D W B hW hEven pi).prototypes l).2| < 2 := by
  rcases l with ⟨j,i⟩|⟨j,i⟩|⟨j,ell,i⟩|⟨j,ell,i⟩
  · exact ordinary_strict_valid (macros n q D) W B _
      (macro_box n q D _ (earlyBlock n q D W B hW j).mem)
  · exact ordinary_strict_valid (macros n q D) W B _
      (macro_box n q D _ (lateBlock n q D W B hW (latePhysical pi j)).mem)
  · exact (rank_strict_valid (macros n q D) W B _ _ ell.val hW
      (earlyBlock n q D W B hW j).mem (lateBlock n q D W B hW (latePhysical pi j)).mem
      (early_late_order n q D W B hW j (latePhysical pi j))
      (macro_box n q D _ (earlyBlock n q D W B hW j).mem)
      (macro_box n q D _ (lateBlock n q D W B hW (latePhysical pi j)).mem)
      (Nat.cast_nonneg _) (gap_rank_bound ell)).1
  · exact (rank_strict_valid (macros n q D) W B _ _ ell.val hW
      (earlyBlock n q D W B hW j).mem (lateBlock n q D W B hW (latePhysical pi j)).mem
      (early_late_order n q D W B hW j (latePhysical pi j))
      (macro_box n q D _ (earlyBlock n q D W B hW j).mem)
      (macro_box n q D _ (lateBlock n q D W B hW (latePhysical pi j)).mem)
      (Nat.cast_nonneg _) (gap_rank_bound ell)).2

/-- Each actual catalog copy carries the exact coordinate/index witness
needed by complete-graph freezing; no soft-row or field condition is input. -/
theorem programWitness (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (hD : D=512*(n*q)*W) (hS : 0 < n*q) (pi : Equiv.Perm (Fin n))
    (d : Recipe (n*q)) (p : Placement d (geometries n q D W B hW hEven pi))
    (l : Label d (W-1)) :
    ProgramWitness (B:=B) (parameter n q D W B) p.M p.base p.prototypes (p.points l) := by
  have hp := proportions n q D W hD hS hW
  have hcut (j : Fin (n*q)) := catalog_cuts n q D W B hW hEven pi j ⟨0,by omega⟩
  rcases l with ⟨j,i⟩|⟨j,i⟩|⟨j,ell,i⟩|⟨j,ell,i⟩
  · apply ProgramWitness.ordinary ((geometries n q D W B hW hEven pi).ordinaryLeft j).2 rfl
    · exact ((earlyBlock n q D W B hW j).fits.trans' (Nat.le_add_right _ _))
    · change (((earlyBlock n q D W B hW j).parent.card:ℝ)/(O n q D W)) ≤ 1/514
      rw [Block.parent_card]
      exact hp.2.1
    · exact Or.inl (hp.2.2.1 _ (hcut j).1)
    · exact p.prototype_mem (.inl ⟨j,i⟩)
    · exact p.placed (.inl ⟨j,i⟩)
  · apply ProgramWitness.ordinary ((geometries n q D W B hW hEven pi).ordinaryRight j).2 rfl
    · exact (hcut j).2.2.2.2.1
    · change (((lateBlock n q D W B hW (latePhysical pi j)).parent.card:ℝ)/(O n q D W)) ≤ 1/514
      rw [Block.parent_card]
      exact hp.2.1
    · exact Or.inr (hp.2.2.2 _ (hcut j).2.2.1)
    · exact p.prototype_mem (.inr (.inl ⟨j,i⟩))
    · exact p.placed (.inr (.inl ⟨j,i⟩))
  · exact ProgramWitness.leftRank ((geometries n q D W B hW hEven pi).rankLeft j ell).2 rfl
      (earlyBlock n q D W B hW j).fits (p.prototype_mem (.inr (.inr (.inl ⟨j,ell,i⟩))))
      (p.placed (.inr (.inr (.inl ⟨j,ell,i⟩))))
  · exact ProgramWitness.rightRank ((geometries n q D W B hW hEven pi).rankRight j ell).2 rfl
      (hcut j).2.2.2.2.2 (p.prototype_mem (.inr (.inr (.inr ⟨j,ell,i⟩))))
      (p.placed (.inr (.inr (.inr ⟨j,ell,i⟩))))

end Q4.Candidate.ProgramGeometry

#print axioms Q4.Candidate.ProgramGeometry.parameter_near_macro
#print axioms Q4.Candidate.ProgramGeometry.Block.outside_bounds
#print axioms Q4.Candidate.ProgramGeometry.Block.nonparent_macro_ne
#print axioms Q4.Candidate.ProgramGeometry.Block.ordinaryGeometry
#print axioms Q4.Candidate.ProgramGeometry.Block.leftGeometry
#print axioms Q4.Candidate.ProgramGeometry.Block.rightGeometry
#print axioms Q4.Candidate.ProgramGeometry.geometries
#print axioms Q4.Candidate.ProgramGeometry.proportions
#print axioms Q4.Candidate.ProgramGeometry.catalog_cuts
#print axioms Q4.Candidate.ProgramGeometry.prototype_below
#print axioms Q4.Candidate.ProgramGeometry.programWitness
