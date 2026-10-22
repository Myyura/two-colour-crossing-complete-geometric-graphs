import Q4.Candidate.CompleteBackground
import Q4.Candidate.CoreFixedPalette

/-! Transport of an explicitly external convex complete-graph optimum to the
actual frame and dummy crossing objectives. The external certificate is a
proposition parameter, never an axiom. All geometric and finite-index changes
of variables in this module are proved. -/
namespace Q4.Candidate.ConvexBackground
open Q4.Candidate.CompleteDrawing Q4.Candidate.ConvexSeparation
open Q4.Candidate.CompleteBackground Q4.Candidate.CompleteClassEnergy
open Q4.Candidate.PaletteCounting Q4.Candidate.ProposedPalette
open Q4.Candidate.CoreLocalGeometry Q4.Candidate.CoreReducedPairs
attribute [local instance] Classical.propDecidable

/-- The usual explicit four-floor formula, evaluated by rational arithmetic. -/
def knownZ (n : ℕ) : ℚ :=
  ((n/2:ℕ):ℚ)*(((n-1)/2:ℕ):ℚ)*(((n-2)/2:ℕ):ℚ)*(((n-3)/2:ℕ):ℚ)/4

def Alternates {n : ℕ} (e f : Inner n) : Prop :=
  (e.val.1<f.val.1 ∧ f.val.1<e.val.2 ∧ e.val.2<f.val.2) ∨
  (f.val.1<e.val.1 ∧ e.val.1<f.val.2 ∧ f.val.2<e.val.2)

noncomputable def convexEnergy (n : ℕ) (χ : Inner n → Bool) : ℝ :=
  halfSum (fun e f => if Alternates e f ∧ χ e=χ f then 1 else 0)

/-- External known theorem interface (two-page crossing number of K_n,
arXiv:1206.5669): all free Boolean chord colourings have the stated lower
bound and one colouring attains it. No instance of this interface is axiomatized. -/
def ConvexOptimum (n : ℕ) (z : ℝ) : Prop := MinimumWitness (convexEnergy n) z

theorem frame_orient_neg (a b c : ℚ) :
    orient (frame a) (frame b) (frame c)=orient (original (-a)) (original (-b)) (original (-c)) := by
  rw [DoubleCapGrid.frame_vandermonde,DoubleCapGrid.original_vandermonde]
  ring

theorem frame_cross_iff {n : ℕ} (ts : Fin n → ℚ) (ht : StrictAnti ts) (e f : Inner n) :
    ProperCross (frame (ts e.val.1)) (frame (ts e.val.2))
      (frame (ts f.val.1)) (frame (ts f.val.2)) ↔ Alternates e f := by
  have hneg : StrictMono (fun i => -ts i) := fun _ _ h => neg_lt_neg (ht h)
  have heq : ProperCross (frame (ts e.val.1)) (frame (ts e.val.2))
      (frame (ts f.val.1)) (frame (ts f.val.2)) ↔
    OriginalCapAlternation.cross (fun i => -ts i) e.val.1 e.val.2 f.val.1 f.val.2 := by
    simp only [ProperCross,OriginalCapAlternation.cross,frame_orient_neg]
  rw [heq,OriginalCapAlternation.cross_ordered _ hneg _ _ _ _ e.property f.property]
  rfl

theorem frame_value_eq {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ)
    (rs : Fin P → Point) (ht : StrictAnti ts) (χ : Inner B → Bool) :
    frameValue ys ts rs χ=convexEnergy B χ := by
  unfold frameValue convexEnergy halfSum
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  have hc : Cross ys ts rs (I e) (I f) ↔ Alternates e f := frame_cross_iff ts ht e f
  simp only [atom,hc]

theorem frame_minimum {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ)
    (rs : Fin P → Point) (ht : StrictAnti ts) (z : ℝ) (hz : ConvexOptimum B z) :
    MinimumWitness (frameValue ys ts rs) z := by
  have he : frameValue ys ts rs=convexEnergy B := funext (frame_value_eq ys ts rs ht)
  rw [he]
  exact hz

def dummyVertex (S W D : ℕ) (i : Fin D) : Fin (S*W+D+S*W) :=
  ⟨S*W+i.val, by have hi := i.isLt; omega⟩

theorem dummyVertex_strict (S W D : ℕ) : StrictMono (dummyVertex S W D) := by
  intro i j h
  exact Nat.add_lt_add_left h _

def dummyChord (S W D : ℕ) (e : Inner D) : Inner (S*W+D+S*W) :=
  ⟨(dummyVertex S W D e.val.1,dummyVertex S W D e.val.2),dummyVertex_strict S W D e.property⟩

theorem dummyChord_mem (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) (e : Inner D) :
    dummyEdge (indexedSite S W D hW pi) (dummyChord S W D e) := by
  constructor <;> apply (indexed_dummy S W D hW pi _).2 <;>
    dsimp [dummyChord,dummyVertex] <;> omega

noncomputable def dummyEquiv (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) :
    Inner D ≃ {e : Inner (S*W+D+S*W) // dummyEdge (indexedSite S W D hW pi) e} where
  toFun e := ⟨dummyChord S W D e,dummyChord_mem S W D hW pi e⟩
  invFun e := by
    have h1 := (indexed_dummy S W D hW pi e.val.val.1).1 e.property.1
    have h2 := (indexed_dummy S W D hW pi e.val.val.2).1 e.property.2
    exact ⟨(⟨e.val.val.1.val-S*W,by omega⟩,⟨e.val.val.2.val-S*W,by omega⟩),
      by
        have he := e.val.property
        change e.val.val.1.val<e.val.val.2.val at he
        change e.val.val.1.val-S*W<e.val.val.2.val-S*W
        omega⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> dsimp [dummyChord,dummyVertex] <;> omega
  right_inv := by
    intro e
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> dsimp [dummyChord,dummyVertex]
    · have h1 := (indexed_dummy S W D hW pi e.val.val.1).1 e.property.1; omega
    · have h2 := (indexed_dummy S W D hW pi e.val.val.2).1 e.property.2; omega

theorem dummy_cross_iff (S W D : ℕ) (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys)
    (e f : Inner D) :
    OriginalCapAlternation.cross ys (dummyChord S W D e).val.1 (dummyChord S W D e).val.2
      (dummyChord S W D f).val.1 (dummyChord S W D f).val.2 ↔ Alternates e f := by
  rw [OriginalCapAlternation.cross_ordered ys hy _ _ _ _ (dummyChord S W D e).property
    (dummyChord S W D f).property]
  simp only [dummyChord,(dummyVertex_strict S W D).lt_iff_lt,Alternates]

theorem masked_sum_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) [DecidablePred p] (e : β ≃ {a // p a}) (f : α → ℝ) :
    (∑ a, if p a then f a else 0) = ∑ b, f (e b).val := by
  rw [←Finset.sum_filter,Finset.sum_subtype (p:=p) _ (by intro a; simp)]
  exact (e.sum_comp (fun a => f a.val)).symm

theorem masked_half_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) [DecidablePred p] (e : β ≃ {a // p a}) (w : α → α → ℝ) :
    halfSum (fun a b => if p a ∧ p b then w a b else 0) =
      halfSum (fun c d => w (e c).val (e d).val) := by
  unfold halfSum
  have hh : (∑ a, ∑ b, if p a ∧ p b then w a b else 0) =
      ∑ a, if p a then (∑ b, if p b then w a b else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : p a <;> simp [ha]
  rw [hh,masked_sum_equiv p e]
  simp_rw [masked_sum_equiv p e]

noncomputable def dummyHalf {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S)
    (χ : Inner O → Bool) : ℝ :=
  halfSum (fun e f => if dummyEdge site e ∧ dummyEdge site f then
    (if OriginalCapAlternation.cross ys e.val.1 e.val.2 f.val.1 f.val.2 ∧ χ e=χ f then 1 else 0) else 0)

theorem dummy_pairs_half {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S)
    (χ : Inner O → Bool) : (pairEnergy (dummyPairs ys site) χ:ℝ)=dummyHalf ys site χ := by
  unfold dummyHalf
  rw [CoreFixedPalette.ordered_halfSum _
    (by intro e f; simp only [and_comm,CoreReducedPairs.cross_symm ys e f,eq_comm])
    (by intro e; simp [OriginalCapAlternation.cross,ProperCross,orient])]
  unfold pairEnergy dummyPairs freePairs
  push_cast
  rw [Finset.filter_filter,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  have he := dummy_not_palette site e
  have hf := dummy_not_palette site f
  unfold edgeRank
  simp only [Fin.lt_def]
  split_ifs <;> simp_all

theorem dummy_value_eq (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (χ : Inner (S*W+D+S*W) → Bool) :
    (pairEnergy (dummyPairs ys (indexedSite S W D hW pi)) χ:ℝ)=
      convexEnergy D (fun e => χ (dummyChord S W D e)) := by
  rw [dummy_pairs_half]
  unfold dummyHalf
  rw [masked_half_equiv _ (dummyEquiv S W D hW pi)]
  unfold convexEnergy halfSum
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  change (if OriginalCapAlternation.cross ys (dummyChord S W D e).val.1
    (dummyChord S W D e).val.2 (dummyChord S W D f).val.1 (dummyChord S W D f).val.2 ∧
    χ (dummyChord S W D e)=χ (dummyChord S W D f) then (1:ℝ) else 0)=_
  simp only [dummy_cross_iff S W D ys hy]

/-- The actual dummy colouring may be extended to every other core edge
arbitrarily. Thus the same convex optimum supplies both a global lower bound
and an actual full-core colouring attaining the dummy part. -/
theorem dummy_minimum (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (z : ℝ) (hz : ConvexOptimum D z) :
    MinimumWitness (fun χ : Inner (S*W+D+S*W) → Bool =>
      (pairEnergy (dummyPairs ys (indexedSite S W D hW pi)) χ:ℝ)) z := by
  constructor
  · intro χ
    rw [dummy_value_eq S W D hW pi ys hy χ]
    exact hz.lower _
  · obtain ⟨χ,hχ⟩ := hz.attained
    let ψ : Inner (S*W+D+S*W) → Bool := fun e =>
      if he : dummyEdge (indexedSite S W D hW pi) e then χ ((dummyEquiv S W D hW pi).symm ⟨e,he⟩)
      else false
    refine ⟨ψ,?_⟩
    rw [dummy_value_eq S W D hW pi ys hy ψ]
    have he : (fun e => ψ (dummyChord S W D e))=χ := by
      funext e
      simp only [ψ,dummyChord_mem S W D hW pi e,dite_true]
      exact congrArg χ ((dummyEquiv S W D hW pi).symm_apply_apply e)
    rw [he]
    exact hχ

#print axioms frame_cross_iff
#print axioms frame_minimum
#print axioms dummyEquiv
#print axioms dummy_pairs_half
#print axioms dummy_value_eq
#print axioms dummy_minimum

end Q4.Candidate.ConvexBackground
