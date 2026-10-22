import Q4.Candidate.CoreFixedPalette
import Q4.Candidate.CompleteBackground

/-! A single actual core coloring combines a source coloring, a dummy
coloring, and all independent short-edge unary minima. -/
namespace Q4.Candidate.CoreExtension
open Q4.Candidate.ProposedPalette Q4.Candidate.PaletteCounting
open Q4.Candidate.CoreLocalGeometry Q4.Candidate.CoreReducedPairs
open Q4.Candidate.CoreFixedPalette Q4.Candidate.CompleteDrawing
open Q4.Candidate.CompleteBackground
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {O S : ℕ}

def selected (site : Fin O → Site S) (e : CoreEdge O) : Prop := ∃j, selectedEdge site j e

theorem selected_free (site : Fin O → Site S) (e : CoreEdge O)
    (he : selected site e) : e ∉ palette site := by
  obtain ⟨j,hj⟩ := he
  exact local_not_palette site j e ((local_split site j e).2 (Or.inr hj))

theorem selected_not_dummy (site : Fin O → Site S) (e : CoreEdge O)
    (he : selected site e) : ¬dummyEdge site e := by
  obtain ⟨j,hj⟩ := he
  intro hd
  exact dummy_not_local site e j hd ((local_split site j e).2 (Or.inr hj))

noncomputable def bestBit (u : CoreEdge O → Bool → ℝ) (e : CoreEdge O) : Bool :=
  if u e false≤u e true then false else true

theorem bestBit_value (u : CoreEdge O → Bool → ℝ) (e : CoreEdge O) :
    u e (bestBit u e)=min (u e false) (u e true) := by
  unfold bestBit
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

theorem unary_bit_bounds (u0 u1 R : ℝ) (hR : |u1-u0|≤R) (b : Bool) :
    min u0 u1≤(if b then u1 else u0) ∧
      (if b then u1 else u0)≤min u0 u1+R := by
  have hh := abs_le.mp hR
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals constructor
  · exact min_le_left _ _
  · rcases le_total u0 u1 with h|h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  · exact min_le_right _ _
  · rcases le_total u0 u1 with h|h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith

noncomputable def merge (site : Fin O → Site S) (u : CoreEdge O → Bool → ℝ)
    (main dummy : CoreEdge O → Bool) (e : CoreEdge O) : Bool :=
  if e∈palette site then paletteBit site e else
  if dummyEdge site e then dummy e else if selected site e then main e else bestBit u e

theorem merge_palette (site : Fin O → Site S) (u : CoreEdge O → Bool → ℝ)
    (main dummy : CoreEdge O → Bool) (e : CoreEdge O) (he : e∈palette site) :
    merge site u main dummy e=paletteBit site e := by simp [merge,he]

theorem merge_main (site : Fin O → Site S) (u : CoreEdge O → Bool → ℝ)
    (main dummy : CoreEdge O → Bool) (e : CoreEdge O) (he : selected site e) :
    merge site u main dummy e=main e := by
  simp [merge,selected_free site e he,selected_not_dummy site e he,he]

theorem merge_dummy (site : Fin O → Site S) (u : CoreEdge O → Bool → ℝ)
    (main dummy : CoreEdge O → Bool) (e : CoreEdge O) (he : dummyEdge site e) :
    merge site u main dummy e=dummy e := by simp [merge,dummy_not_palette site e he,he]

theorem pairEnergy_congr (pairs : Finset (CoreEdge O×CoreEdge O))
    (chi psi : CoreEdge O → Bool)
    (h : ∀p∈pairs, chi p.1=psi p.1 ∧ chi p.2=psi p.2) :
    pairEnergy pairs chi=pairEnergy pairs psi := by
  apply Finset.sum_congr rfl
  intro p hp
  simp only [(h p hp).1,(h p hp).2]

theorem merge_main_energy (ys : Fin O → ℚ) (site : Fin O → Site S)
    (u : CoreEdge O → Bool → ℝ) (main dummy : CoreEdge O → Bool) :
    pairEnergy (mainPairs ys site) (merge site u main dummy)=pairEnergy (mainPairs ys site) main := by
  apply pairEnergy_congr
  intro p hp
  obtain ⟨j,k,_,hj,hk⟩ := (Finset.mem_filter.mp hp).2
  exact ⟨merge_main site u main dummy p.1 ⟨j,hj⟩,merge_main site u main dummy p.2 ⟨k,hk⟩⟩

theorem merge_dummy_energy (ys : Fin O → ℚ) (site : Fin O → Site S)
    (u : CoreEdge O → Bool → ℝ) (main dummy : CoreEdge O → Bool) :
    pairEnergy (dummyPairs ys site) (merge site u main dummy)=pairEnergy (dummyPairs ys site) dummy := by
  apply pairEnergy_congr
  intro p hp
  have hh := (Finset.mem_filter.mp hp).2
  exact ⟨merge_dummy site u main dummy p.1 hh.1,merge_dummy site u main dummy p.2 hh.2⟩

noncomputable def unarySum (site : Fin O → Site S) (u : CoreEdge O → Bool → ℝ)
    (chi : CoreEdge O → Bool) : ℝ := ∑e, if e∉palette site then u e (chi e) else 0
noncomputable def unaryFloor (site : Fin O → Site S) (u : CoreEdge O → Bool → ℝ) : ℝ :=
  ∑e, if e∉palette site then min (u e false) (u e true) else 0
noncomputable def selectedSet (site : Fin O → Site S) : Finset (CoreEdge O) :=
  Finset.univ.filter (selected site)

theorem unary_lower (site : Fin O → Site S) (u : CoreEdge O → Bool → ℝ)
    (chi : CoreEdge O → Bool) : unaryFloor site u≤unarySum site u chi := by
  apply Finset.sum_le_sum
  intro e _
  by_cases he : e∈palette site
  · simp [he]
  · simp only [he,not_false_eq_true,ite_true]
    cases chi e
    · exact min_le_left _ _
    · exact min_le_right _ _

theorem merge_unary_upper (site : Fin O → Site S) (u : CoreEdge O → Bool → ℝ)
    (main dummy : CoreEdge O → Bool) (R : ℝ)
    (hR : ∀e, selected site e → |u e true-u e false|≤R)
    (hd : ∀e, dummyEdge site e → u e true=u e false) :
    unarySum site u (merge site u main dummy)≤unaryFloor site u+(selectedSet site).card*R := by
  have hp (e : CoreEdge O) :
      (if e∉palette site then u e (merge site u main dummy e) else 0) ≤
      (if e∉palette site then min (u e false) (u e true) else 0)+
      (if selected site e then R else 0) := by
    by_cases hs : selected site e
    · have he := selected_free site e hs
      simp only [he,not_false_eq_true,ite_true,hs,merge_main site u main dummy e hs]
      have hh := (unary_bit_bounds (u e false) (u e true) R (hR e hs) (main e)).2
      cases hm : main e <;> simpa [hm] using hh
    · simp only [hs,ite_false,add_zero]
      by_cases he : e∈palette site
      · simp [he]
      · simp only [he,not_false_eq_true,ite_true]
        by_cases hde : dummyEdge site e
        · rw [merge_dummy site u main dummy e hde,hd e hde,min_self]
          cases dummy e <;> simp [hd e hde]
        · rw [show merge site u main dummy e=bestBit u e by simp [merge,he,hde,hs],bestBit_value u e]
  have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset (CoreEdge O))) (fun e _ => hp e)
  simp only [Finset.sum_add_distrib] at hh
  have hs : (∑e : CoreEdge O, if selected site e then R else 0)=(selectedSet site).card*R := by
    rw [←Finset.sum_filter]
    simp [selectedSet]
  rw [hs] at hh
  exact hh

theorem indexed_selected_card (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) :
    (selectedSet (indexedSite S W D hW pi)).card≤2*S*W^2 := by
  let site := indexedSite S W D hW pi
  let L (j : Fin S) := (Finset.univ : Finset (CoreEdge (S*W+D+S*W))).filter (localEdge site j)
  have hs : selectedSet site⊆Finset.univ.biUnion L := by
    intro e he
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(local_split site j e).2 (Or.inr hj)⟩⟩
  have hj (j : Fin S) : (L j).card≤2*W^2 := by
    have hh := local_edges_card site j (indexed_fibers S W D hW pi j)
      (indexed_bounds S W D pi j).1 (indexed_bounds S W D pi j).2.1
    simpa [L,Fintype.card_subtype] using hh
  have hc := (Finset.card_le_card hs).trans (Finset.card_biUnion_le)
  have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin S))) (fun j _ => hj j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  nlinarith

noncomputable def restoredValue (ys : Fin O → ℚ) (site : Fin O → Site S)
    (base : ℝ) (u : CoreEdge O → Bool → ℝ) (chi : CoreEdge O → Bool) : ℝ :=
  base + (pairEnergy (allLocalPairs ys site) chi : ℝ) +
    (pairEnergy (mainPairs ys site) chi : ℝ) +
    (pairEnergy (dummyPairs ys site) chi : ℝ) + unarySum site u chi

theorem pairEnergy_le_card (pairs : Finset (CoreEdge O×CoreEdge O)) (chi : CoreEdge O → Bool) :
    pairEnergy pairs chi≤pairs.card := by
  unfold pairEnergy
  calc
    _ ≤ ∑ _p ∈ pairs, (1:ℕ) := Finset.sum_le_sum (by intro p _; split_ifs <;> omega)
    _ = _ := by simp

theorem restored_lower (ys : Fin O → ℚ) (site : Fin O → Site S)
    (base m z : ℝ) (u : CoreEdge O → Bool → ℝ)
    (hm : ∀chi, m≤(pairEnergy (mainPairs ys site) chi : ℝ))
    (hz : ∀chi, z≤(pairEnergy (dummyPairs ys site) chi : ℝ)) (chi : CoreEdge O → Bool) :
    base+unaryFloor site u+m+z≤restoredValue ys site base u chi := by
  have hm' := hm chi
  have hz' := hz chi
  have hu := unary_lower site u chi
  have hl : (0:ℝ)≤pairEnergy (allLocalPairs ys site) chi := by positivity
  unfold restoredValue
  linarith

/-- The same actual coloring realizes the main and dummy minima, and pays
only the selected-unary and restored-local errors. -/
theorem restored_upper (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (base m z R : ℝ)
    (u : CoreEdge (S*W+D+S*W) → Bool → ℝ)
    (hm : ∃chi, (pairEnergy (mainPairs ys (indexedSite S W D hW pi)) chi : ℝ)=m)
    (hz : ∃chi, (pairEnergy (dummyPairs ys (indexedSite S W D hW pi)) chi : ℝ)=z)
    (hR0 : 0≤R)
    (hR : ∀e, selected (indexedSite S W D hW pi) e → |u e true-u e false|≤R)
    (hd : ∀e, dummyEdge (indexedSite S W D hW pi) e → u e true=u e false) :
    ∃chi, (∀e∈palette (indexedSite S W D hW pi), chi e=paletteBit (indexedSite S W D hW pi) e) ∧
      restoredValue ys (indexedSite S W D hW pi) base u chi≤
        base+unaryFloor (indexedSite S W D hW pi) u+m+z+2*S*W^2*R+2*S*W^4 := by
  let site := indexedSite S W D hW pi
  obtain ⟨main,hm⟩ := hm
  obtain ⟨dummy,hz⟩ := hz
  let chi := merge site u main dummy
  have hm' := merge_main_energy ys site u main dummy
  have hz' := merge_dummy_energy ys site u main dummy
  have hu := merge_unary_upper site u main dummy R hR hd
  have hc : ((selectedSet site).card:ℝ)≤2*S*W^2 := by
    exact_mod_cast indexed_selected_card S W D hW pi
  have hl : (pairEnergy (allLocalPairs ys site) chi : ℝ)≤2*S*W^4 := by
    exact_mod_cast (pairEnergy_le_card _ chi).trans (indexed_allLocalPairs_card S W D hW pi ys)
  have he := mul_le_mul_of_nonneg_right hc hR0
  refine ⟨chi,fun e he => merge_palette site u main dummy e he,?_⟩
  unfold restoredValue
  dsimp only [chi]
  rw [hm',hz',hm,hz]
  dsimp only [chi] at hl
  linarith

end Q4.Candidate.CoreExtension
#print axioms Q4.Candidate.CoreExtension.merge_main_energy
#print axioms Q4.Candidate.CoreExtension.merge_dummy_energy
#print axioms Q4.Candidate.CoreExtension.merge_unary_upper
#print axioms Q4.Candidate.CoreExtension.indexed_selected_card
#print axioms Q4.Candidate.CoreExtension.restored_lower
#print axioms Q4.Candidate.CoreExtension.restored_upper
