import Q4.Candidate.SourceChordGeometry
import Q4.Candidate.CoreEncoding
import Mathlib.Data.Fintype.BigOperators

/-! Distinct actual source edges and the finite independent-blowup objective. -/
set_option maxHeartbeats 800000
namespace Q4.Candidate.SourceSelectedEdges
open Q4.Candidate.SourceChordGeometry Q4.Candidate.RankGap Q4.Candidate.ConvexSeparation
open Q4.Candidate.CoreEncoding

theorem clone_rank_order {n q W : ℕ} (base tau : ℚ) (v : Fin n) (j : Fin q) (r t : Fin W)
    (hW : 2≤W) (htau : 0<tau) :
    cloneParameter base tau v j r<cloneParameter base tau v j t ↔ r<t := by
  have hw : (0:ℚ)<(W:ℚ)-1 := by
    have hh : (2:ℚ)≤W := by exact_mod_cast hW
    linarith
  unfold cloneParameter cloneAt
  rw [add_lt_add_iff_left,mul_lt_mul_iff_of_pos_left htau,sub_lt_sub_iff_right,
    div_lt_div_iff_of_pos_right hw]
  exact_mod_cast (Iff.rfl : r.val<t.val ↔ r<t)

theorem clone_parameter_injective {n q W : ℕ} (base tau : ℚ)
    (hW : 2≤W) (htau : 0<tau) (hsmall : tau<1/(8*((n*q:ℕ)+1))) :
    Function.Injective (fun p : Fin n × (Fin q × Fin W) => cloneParameter base tau p.1 p.2.1 p.2.2) := by
  rintro ⟨v,j,r⟩ ⟨w,k,t⟩ he
  dsimp at he
  have hmacro : v=w ∧ j=k := by
    by_contra h
    have hn : v≠w ∨ j≠k := by tauto
    have h1 := clone_blocks_order base tau v w j k r t hW (le_of_lt htau) hsmall hn
    have h2 := clone_blocks_order base tau w v k j t r hW (le_of_lt htau) hsmall
      (by rcases hn with hn | hn; exact Or.inl hn.symm; exact Or.inr hn.symm)
    rw [he] at h1
    rw [he] at h2
    simp only [lt_self_iff_false,false_iff] at h1 h2
    rcases lt_trichotomy v w with hlt | heq | hlt
    · exact h1 (Or.inl hlt)
    · subst w
      rcases lt_trichotomy j k with hlt | heq | hlt
      · exact h1 (Or.inr ⟨rfl,hlt⟩)
      · exact h ⟨rfl,heq⟩
      · exact h2 (Or.inr ⟨rfl,hlt⟩)
    · exact h2 (Or.inl hlt)
  obtain ⟨rfl,rfl⟩ := hmacro
  have hr : r=t := by
    rcases lt_trichotomy r t with h | h | h
    · have hh := (clone_rank_order base tau v j r t hW htau).2 h
      rw [he] at hh
      exact (lt_irrefl _ hh).elim
    · exact h
    · have hh := (clone_rank_order base tau v j t r hW htau).2 h
      rw [he] at hh
      exact (lt_irrefl _ hh).elim
  subst t
  rfl

abbrev Copy (q W : ℕ) := Fin q × (Fin W × Fin W)
abbrev Selected (n q W : ℕ) := Fin n × Copy q W

def selectedEndpoints {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (e : Selected n q W) : Point × Point :=
  (original (early tau e.1 e.2.1 e.2.2.1), original (late pi tau e.1 e.2.1 e.2.2.2))

theorem selected_endpoints_injective {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (hW : 2≤W) (htau : 0<tau) (hsmall : tau<1/(8*((n*q:ℕ)+1))) :
    Function.Injective (selectedEndpoints (q:=q) (W:=W) pi tau) := by
  rintro ⟨v,j,r,t⟩ ⟨w,k,r',t'⟩ he
  have h1 := DoubleCapGrid.original_injective (congrArg Prod.fst he)
  have h2 := DoubleCapGrid.original_injective (congrArg Prod.snd he)
  change cloneParameter (-3/4) tau v j r = cloneParameter (-3/4) tau w k r' at h1
  have hp : (v,(j,r))=(w,(k,r')) := clone_parameter_injective (-3/4) tau hW htau hsmall h1
  have hv := congrArg Prod.fst hp
  have hj := congrArg (fun x => x.2.1) hp
  have hr := congrArg (fun x => x.2.2) hp
  dsimp at hv hj hr
  subst w; subst k; subst r'
  change cloneParameter (5/8) tau (pi v).rev j.rev t =
    cloneParameter (5/8) tau (pi v).rev j.rev t' at h2
  have hp2 : ((pi v).rev,(j.rev,t))=((pi v).rev,(j.rev,t')) :=
    clone_parameter_injective (5/8) tau hW htau hsmall h2
  have ht := congrArg (fun x => x.2.2) hp2
  dsimp at ht
  subst t'
  rfl

theorem selected_endpoints_distinct {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1)))
    (e : Selected n q W) : (selectedEndpoints pi tau e).1≠(selectedEndpoints pi tau e).2 := by
  intro he
  have hy := DoubleCapGrid.original_injective he
  have hs := separated_parameters tau e.1 (pi e.1).rev e.2.1 e.2.1.rev
    e.2.2.1 e.2.2.2 hW htau hsmall
  change early tau e.1 e.2.1 e.2.2.1=late pi tau e.1 e.2.1 e.2.2.2 at hy
  change early tau e.1 e.2.1 e.2.2.1<late pi tau e.1 e.2.1 e.2.2.2 at hs
  exact (ne_of_lt hs) hy

theorem selected_unordered_injective {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (hW : 2≤W) (htau : 0<tau) (hsmall : tau<1/(8*((n*q:ℕ)+1)))
    (e f : Selected n q W)
    (he : selectedEndpoints pi tau e=selectedEndpoints pi tau f ∨
      selectedEndpoints pi tau e=((selectedEndpoints pi tau f).2,(selectedEndpoints pi tau f).1)) : e=f := by
  rcases he with he | he
  · exact selected_endpoints_injective pi tau hW htau hsmall he
  · have hy := DoubleCapGrid.original_injective (congrArg Prod.fst he)
    have hs := separated_parameters tau e.1 (pi f.1).rev e.2.1 f.2.1.rev
      e.2.2.1 f.2.2.2 hW (le_of_lt htau) hsmall
    change early tau e.1 e.2.1 e.2.2.1=late pi tau f.1 f.2.1 f.2.2.2 at hy
    change early tau e.1 e.2.1 e.2.2.1<late pi tau f.1 f.2.1 f.2.2.2 at hs
    exact ((ne_of_lt hs) hy).elim

theorem selected_card (n q W : ℕ) : Fintype.card (Selected n q W)=n*q*W^2 := by
  simp only [Selected,Copy,Fintype.card_prod,Fintype.card_fin]
  ring

open scoped BigOperators
open Q4.SimultaneousFlip
attribute [local instance] Classical.propDecidable

noncomputable def sourcePairs {n : ℕ} (pi : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1<p.2 ∧ pi p.2<pi p.1)

noncomputable def retainedPairs {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ) :
    Finset (Selected n q W × Selected n q W) :=
  Finset.univ.filter (fun p => p.1.1<p.2.1 ∧
    (p.1.1,p.1.2.1)≠(p.2.1,p.2.2.1) ∧
    ProperCross (selectedEndpoints pi tau p.1).1 (selectedEndpoints pi tau p.1).2
      (selectedEndpoints pi tau p.2).1 (selectedEndpoints pi tau p.2).2)

theorem retained_predicate {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1)))
    (p z : Selected n q W) :
    (p,z)∈retainedPairs pi tau ↔ p.1<z.1 ∧ pi z.1<pi p.1 := by
  classical
  unfold retainedPairs
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  dsimp only [selectedEndpoints]
  rw [deleted_selected_crossing pi tau p.1 z.1 p.2.1 z.2.1 p.2.2.1 p.2.2.2
    z.2.2.1 z.2.2.2 hW htau hsmall]
  unfold sourceAdjacent
  constructor
  · rintro ⟨hp,h | h⟩
    · exact h
    · exact (lt_asymm hp h.1).elim
  · intro h; exact ⟨h.1,Or.inl h⟩

/-- The orientation by source vertex loses no retained physical crossing:
every retained crossing has different source vertices and one orientation. -/
theorem retained_exhaustive {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1)))
    (p z : Selected n q W) :
    ((p.1,p.2.1)≠(z.1,z.2.1) ∧
      ProperCross (selectedEndpoints pi tau p).1 (selectedEndpoints pi tau p).2
        (selectedEndpoints pi tau z).1 (selectedEndpoints pi tau z).2) ↔
    (p,z)∈retainedPairs pi tau ∨ (z,p)∈retainedPairs pi tau := by
  rw [retained_predicate pi tau hW htau hsmall,retained_predicate pi tau hW htau hsmall]
  exact deleted_selected_crossing pi tau p.1 z.1 p.2.1 z.2.1 p.2.2.1 p.2.2.2
    z.2.2.1 z.2.2.2 hW htau hsmall

theorem intSum_toList {α : Type*} (s : Finset α) (f : α → ℤ) :
    intSum s.toList f = ∑ x ∈ s, f x := by
  have hl (xs : List α) : intSum xs f = (xs.map f).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [intSum,ih]
  rw [hl,Finset.sum_map_toList]

/-- Equality of actual geometric retained-crossing count and the free-color
blowup objective; no graph-realization assumption remains in this equality. -/
theorem retained_energy {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1)))
    (χ : Selected n q W → Bool) :
    (Q4.monoCount (retainedPairs pi tau).toList χ:ℤ) =
      blowEnergy (Finset.univ : Finset (Copy q W)).toList (sourcePairs pi).toList
        (fun v i => χ (v,i)) := by
  classical
  rw [←edgeEnergy_eq_monoCount]
  unfold blowEnergy
  rw [intSum_toList]
  simp only [intSum_toList]
  have hp : retainedPairs (q:=q) (W:=W) pi tau = Finset.univ.filter
      (fun p : Selected n q W × Selected n q W => p.1.1<p.2.1 ∧ pi p.2.1<pi p.1.1) := by
    ext p
    simp only [retained_predicate pi tau hW htau hsmall,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hp,Finset.sum_filter]
  unfold sourcePairs
  rw [Finset.sum_filter]
  conv_lhs =>
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
    arg 2
    ext v
    arg 2
    ext i
    rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : v<w ∧ pi w<pi v <;> simp [h]

/-- Every retained selected edge has free color; its exact geometric optimum
is q² W⁴ times the source monochromatic minimum. This is the deleted selected
subobjective, not the full completed graph. -/
theorem retained_minimum {n q W : ℕ} (pi : Equiv.Perm (Fin n)) (tau : ℚ)
    (hW : 2≤W) (htau : 0≤tau) (hsmall : tau<1/(8*((n*q:ℕ)+1))) :
    (∀ χ : Selected n q W → Bool,
      (q:ℤ)^2*(W:ℤ)^4*(sourceOpt (sourcePairs pi).toList:ℤ) ≤
        (Q4.monoCount (retainedPairs pi tau).toList χ:ℤ)) ∧
    (∃ χ : Selected n q W → Bool,
      (Q4.monoCount (retainedPairs pi tau).toList χ:ℤ) =
        (q:ℤ)^2*(W:ℤ)^4*(sourceOpt (sourcePairs pi).toList:ℤ)) := by
  classical
  let copies := (Finset.univ : Finset (Copy q W)).toList
  have hloop : ∀ e, e∈(sourcePairs pi).toList → e.1≠e.2 := by
    intro e he
    have h := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2.1
    exact ne_of_lt h
  have hends : ∀ e, e∈(sourcePairs pi).toList →
      e.1∈(Finset.univ : Finset (Fin n)).toList ∧ e.2∈(Finset.univ : Finset (Fin n)).toList := by
    simp
  have hopt := independent_blowup_minimum copies (sourcePairs pi).toList
    (Finset.univ : Finset (Fin n)).toList hloop hends
  have hc : (copies.length:ℤ)*(copies.length:ℤ)=(q:ℤ)^2*(W:ℤ)^4 := by
    simp only [copies,Finset.length_toList,Finset.card_univ,Copy,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    ring
  constructor
  · intro χ
    rw [retained_energy pi tau hW htau hsmall]
    have h := hopt.1 (fun v i => χ (v,i))
    rw [hc] at h
    exact h
  · obtain ⟨χ,hχ⟩ := hopt.2
    refine ⟨fun p => χ p.1 p.2,?_⟩
    rw [retained_energy pi tau hW htau hsmall]
    rw [hc] at hχ
    exact hχ

end Q4.Candidate.SourceSelectedEdges
#print axioms Q4.Candidate.SourceSelectedEdges.clone_parameter_injective
#print axioms Q4.Candidate.SourceSelectedEdges.selected_endpoints_injective
#print axioms Q4.Candidate.SourceSelectedEdges.retained_exhaustive
#print axioms Q4.Candidate.SourceSelectedEdges.retained_energy
#print axioms Q4.Candidate.SourceSelectedEdges.retained_minimum

#print axioms Q4.Candidate.SourceSelectedEdges.selected_unordered_injective
#print axioms Q4.Candidate.SourceSelectedEdges.selected_card
