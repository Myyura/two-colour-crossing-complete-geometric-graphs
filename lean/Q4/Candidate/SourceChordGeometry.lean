import Q4.Candidate.OriginalCapCrossing
import Q4.Candidate.RankGap
import Mathlib.Data.Fin.Rev

/-! Actual rational clone endpoints realizing the independent source blowup.
The first source order is the vertex order; pi gives the second order.
The physical late order reverses pi and the copy order, so different copies of
one source vertex are nested. Only intra-bundle crossings are deleted. -/
namespace Q4.Candidate.SourceChordGeometry
open Q4.Candidate.ConvexSeparation Q4.Candidate.RankGap
open Q4.Candidate.OriginalCapCrossing

def blockIndex {n q : ℕ} (v : Fin n) (j : Fin q) : ℕ := v.val*q+j.val

theorem blockIndex_bound {n q : ℕ} (v : Fin n) (j : Fin q) : blockIndex v j<n*q := by
  have h := Nat.mul_le_mul_right q (show v.val+1≤n by omega)
  dsimp [blockIndex]
  nlinarith [j.isLt]

theorem blockIndex_order {n q : ℕ} (v w : Fin n) (j k : Fin q) :
    blockIndex v j<blockIndex w k ↔ v<w ∨ (v=w ∧ j<k) := by
  have hvw (h : v<w) : blockIndex v j<blockIndex w k := by
    have hmul := Nat.mul_le_mul_right q (show v.val+1≤w.val by exact h)
    dsimp [blockIndex]
    nlinarith [j.isLt,Nat.zero_le k.val]
  have hwv (h : w<v) : blockIndex w k<blockIndex v j := by
    have hmul := Nat.mul_le_mul_right q (show w.val+1≤v.val by exact h)
    dsimp [blockIndex]
    nlinarith [k.isLt,Nat.zero_le j.val]
  rcases lt_trichotomy v w with h | h | h
  · simp [h,hvw h]
  · subst w
    simp [blockIndex]
  · have hh := hwv h
    constructor
    · intro hn; omega
    · intro hn; rcases hn with hn | ⟨hn,_⟩
      · exact False.elim (lt_asymm h hn)
      · subst w; exact False.elim (lt_irrefl _ h)

def macroParameter (n q : ℕ) (base : ℚ) (i : ℕ) : ℚ :=
  base+(i+1)/(8*((n*q:ℕ)+1))

def cloneParameter {n q W : ℕ} (base tau : ℚ) (v : Fin n) (j : Fin q) (r : Fin W) : ℚ :=
  cloneAt (macroParameter n q base (blockIndex v j)) tau W r

theorem macro_gap (n q i k : ℕ) (base : ℚ) (hik : i<k) :
    1/(8*((n*q:ℕ)+1)) ≤ macroParameter n q base k-macroParameter n q base i := by
  have hden : (0:ℚ)<8*((n*q:ℕ)+1) := by positivity
  have hh : (i:ℚ)+1≤k := by exact_mod_cast hik
  unfold macroParameter
  have he : base+((k:ℚ)+1)/(8*((n*q:ℕ)+1))-
      (base+((i:ℚ)+1)/(8*((n*q:ℕ)+1))) = ((k:ℚ)-i)/(8*((n*q:ℕ)+1)) := by ring
  rw [he]
  exact (div_le_div_iff_of_pos_right hden).2 (by linarith)

theorem cloneParameter_bounds {n q W : ℕ} (base tau : ℚ) (v : Fin n) (j : Fin q) (r : Fin W)
    (htau : 0≤tau) (hW : 2≤W) :
    macroParameter n q base (blockIndex v j)-tau/2 ≤ cloneParameter base tau v j r ∧
    cloneParameter base tau v j r ≤ macroParameter n q base (blockIndex v j)+tau/2 := by
  exact clone_bounds _ tau W r htau (by exact_mod_cast hW) (by positivity)
    (by have h : (r.val:ℚ)<W := by exact_mod_cast r.isLt
        have hh : (r.val:ℚ)+1≤W := by exact_mod_cast (show r.val+1≤W by omega)
        linarith)

theorem clone_blocks_lt {n q W : ℕ} (base tau : ℚ)
    (v w : Fin n) (j k : Fin q) (r t : Fin W)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1)))
    (hblock : blockIndex v j<blockIndex w k) :
    cloneParameter base tau v j r<cloneParameter base tau w k t := by
  have h1 := cloneParameter_bounds base tau v j r htau hW
  have h2 := cloneParameter_bounds base tau w k t htau hW
  have hg := macro_gap n q (blockIndex v j) (blockIndex w k) base hblock
  linarith

theorem clone_blocks_order {n q W : ℕ} (base tau : ℚ)
    (v w : Fin n) (j k : Fin q) (r t : Fin W)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1)))
    (hne : v≠w ∨ j≠k) :
    cloneParameter base tau v j r<cloneParameter base tau w k t ↔
      v<w ∨ (v=w ∧ j<k) := by
  constructor
  · intro hlt
    rcases lt_trichotomy v w with hv | hv | hv
    · exact Or.inl hv
    · subst w
      rcases lt_trichotomy j k with hj | hj | hj
      · exact Or.inr ⟨rfl,hj⟩
      · subst k; simp at hne
      · have hh := clone_blocks_lt base tau v v k j t r hW htau hsmall
          ((blockIndex_order _ _ _ _).2 (Or.inr ⟨rfl,hj⟩))
        linarith
    · have hh := clone_blocks_lt base tau w v k j t r hW htau hsmall
        ((blockIndex_order _ _ _ _).2 (Or.inl hv))
      linarith
  · intro h
    exact clone_blocks_lt base tau v w j k r t hW htau hsmall
      ((blockIndex_order _ _ _ _).2 h)

theorem macro_bounds {n q : ℕ} (base : ℚ) (v : Fin n) (j : Fin q) :
    base < macroParameter n q base (blockIndex v j) ∧
    macroParameter n q base (blockIndex v j)<base+1/8 := by
  have hden : (0:ℚ)<8*((n*q:ℕ)+1) := by positivity
  have hi : ((blockIndex v j:ℕ):ℚ)<n*q := by exact_mod_cast blockIndex_bound v j
  have hlo : (0:ℚ)<((blockIndex v j:ℕ):ℚ)+1 := by positivity
  have hhi : (((blockIndex v j:ℕ):ℚ)+1)/(8*((n*q:ℕ)+1))<1/8 :=
    (div_lt_iff₀ hden).2 (by push_cast at *; linarith)
  dsimp [macroParameter]
  exact ⟨by linarith [div_pos hlo hden],by linarith⟩

theorem separated_parameters {n q W : ℕ} (tau : ℚ)
    (v w : Fin n) (j k : Fin q) (r t : Fin W)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1))) :
    cloneParameter (-3/4) tau v j r < cloneParameter (5/8) tau w k t := by
  have h1 := cloneParameter_bounds (-3/4) tau v j r htau hW
  have h2 := cloneParameter_bounds (5/8) tau w k t htau hW
  have hb1 := macro_bounds (-3/4:ℚ) v j
  have hb2 := macro_bounds (5/8:ℚ) w k
  have hden : (0:ℚ)<8*((n*q:ℕ)+1) := by positivity
  have hle : (1:ℚ)/(8*((n*q:ℕ)+1))≤1/8 :=
    (div_le_iff₀ hden).2 (by
      have hn : (0:ℚ)≤((n*q:ℕ):ℚ) := by positivity
      linarith)
  linarith

def early {n q W : ℕ} (tau : ℚ) (v : Fin n) (j : Fin q) (r : Fin W) : ℚ :=
  cloneParameter (-3/4) tau v j r

def late {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (v : Fin n) (j : Fin q) (t : Fin W) : ℚ :=
  cloneParameter (5/8) tau (pi v).rev j.rev t

def sourceAdjacent {n : ℕ} (pi : Equiv.Perm (Fin n)) (v w : Fin n) : Prop :=
  (v<w ∧ pi w<pi v) ∨ (w<v ∧ pi v<pi w)

theorem different_vertex_crossing {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (v w : Fin n) (j k : Fin q) (r t r' t' : Fin W)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1))) (hne : v≠w) :
    ProperCross (original (early tau v j r)) (original (late pi tau v j t))
      (original (early tau w k r')) (original (late pi tau w k t')) ↔ sourceAdjacent pi v w := by
  have hs (v w : Fin n) (j k : Fin q) (r t : Fin W) : early tau v j r<late pi tau w k t :=
    separated_parameters tau v (pi w).rev j k.rev r t hW htau hsmall
  rw [separated_order _ _ _ _ (hs v v j j r t) (hs w w k k r' t')
    (hs v w j k r t') (hs w v k j r' t)]
  have hpne : (pi v).rev≠(pi w).rev := fun h => hne (pi.injective (Fin.rev_injective h))
  simp only [early,late,
    clone_blocks_order _ tau v w j k r r' hW htau hsmall (Or.inl hne),
    clone_blocks_order _ tau w v k j r' r hW htau hsmall (Or.inl hne.symm),
    clone_blocks_order _ tau (pi v).rev (pi w).rev j.rev k.rev t t' hW htau hsmall (Or.inl hpne),
    clone_blocks_order _ tau (pi w).rev (pi v).rev k.rev j.rev t' t hW htau hsmall (Or.inl hpne.symm),
    hne,hne.symm,hpne,hpne.symm,Fin.rev_lt_rev,false_and,or_false,sourceAdjacent]

theorem same_vertex_nested {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (v : Fin n) (j k : Fin q) (r t r' t' : Fin W)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1))) (hne : j≠k) :
    ¬ProperCross (original (early tau v j r)) (original (late pi tau v j t))
      (original (early tau v k r')) (original (late pi tau v k t')) := by
  have hs (j k : Fin q) (r t : Fin W) : early tau v j r<late pi tau v k t :=
    separated_parameters tau v (pi v).rev j k.rev r t hW htau hsmall
  rw [separated_order _ _ _ _ (hs j j r t) (hs k k r' t') (hs j k r t') (hs k j r' t)]
  have hrev : j.rev≠k.rev := fun h => hne (Fin.rev_injective h)
  simp only [early,late,
    clone_blocks_order _ tau v v j k r r' hW htau hsmall (Or.inr hne),
    clone_blocks_order _ tau v v k j r' r hW htau hsmall (Or.inr hne.symm),
    clone_blocks_order _ tau (pi v).rev (pi v).rev j.rev k.rev t t' hW htau hsmall (Or.inr hrev),
    clone_blocks_order _ tau (pi v).rev (pi v).rev k.rev j.rev t' t hW htau hsmall (Or.inr hrev.symm),
    lt_self_iff_false,true_and,false_or,Fin.rev_lt_rev]
  intro h
  rcases h with h | h <;> exact lt_asymm h.1 h.2

/-- Delete exactly the within-macro-bundle interactions, not edges of the
complete drawing. Every remaining selected crossing is the source adjacency,
independently of both clone ranks and the q copy indices. -/
theorem deleted_selected_crossing {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (v w : Fin n) (j k : Fin q) (r t r' t' : Fin W)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1))) :
    ((v,j)≠(w,k) ∧ ProperCross (original (early tau v j r)) (original (late pi tau v j t))
      (original (early tau w k r')) (original (late pi tau w k t'))) ↔ sourceAdjacent pi v w := by
  by_cases hv : v=w
  · subst w
    by_cases hj : j=k
    · subst k; simp [sourceAdjacent]
    · have hn := same_vertex_nested pi tau v j k r t r' t' hW htau hsmall hj
      simp [hn,sourceAdjacent]
  · have hp : (v,j)≠(w,k) := fun h => hv (congrArg Prod.fst h)
    rw [and_iff_right hp]
    exact different_vertex_crossing pi tau v w j k r t r' t' hW htau hsmall hv

end Q4.Candidate.SourceChordGeometry
#print axioms Q4.Candidate.SourceChordGeometry.blockIndex_order
#print axioms Q4.Candidate.SourceChordGeometry.clone_blocks_order
#print axioms Q4.Candidate.SourceChordGeometry.separated_parameters
#print axioms Q4.Candidate.SourceChordGeometry.different_vertex_crossing
#print axioms Q4.Candidate.SourceChordGeometry.same_vertex_nested
#print axioms Q4.Candidate.SourceChordGeometry.deleted_selected_crossing
