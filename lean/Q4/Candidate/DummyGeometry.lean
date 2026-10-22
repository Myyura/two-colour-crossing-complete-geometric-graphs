import Q4.Candidate.OriginalCapAlternation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum

/-! Actual dummy-chord palette incidences. Endpoints in the early/dummy/late
regions are arbitrary rational points on the original cap, subject to their
proved strict block order. -/
namespace Q4.Candidate.DummyGeometry
open Q4.Candidate.ConvexSeparation Q4.Candidate.OriginalCapAlternation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem early_dummy_crossing (e a b d : ℚ) (hab : a<b) (hea : e<a) (hed : e<d) :
    ProperCross (original a) (original b) (original e) (original d) ↔ a<d ∧ d<b := by
  rw [cap_ordered a b e d hab hed]
  constructor
  · rintro (h|h)
    · linarith [h.1]
    · exact ⟨h.2.1,h.2.2⟩
  · intro h; exact Or.inr ⟨hea,h⟩

theorem dummy_late_crossing (a b d l : ℚ) (hab : a<b) (hbl : b<l) (hdl : d<l) :
    ProperCross (original a) (original b) (original d) (original l) ↔ a<d ∧ d<b := by
  rw [cap_ordered a b d l hab hdl]
  constructor
  · rintro (h|h)
    · exact ⟨h.1,h.2.1⟩
    · linarith [h.2.2]
  · intro h; exact Or.inl ⟨h.1,h.2,hbl⟩

theorem no_early_late_crossing (e a b l : ℚ) (hab : a<b) (hea : e<a) (hbl : b<l) :
    ¬ProperCross (original a) (original b) (original e) (original l) := by
  rw [cap_ordered a b e l hab (by linarith)]
  rintro (h|h) <;> linarith [h.1,h.2.2]

theorem no_early_short_crossing (a b e f : ℚ) (hab : a<b) (hef : e<f) (hfa : f<a) :
    ¬ProperCross (original a) (original b) (original e) (original f) := by
  rw [cap_ordered a b e f hab hef]
  rintro (h|h) <;> linarith [h.1,h.2.1]

theorem no_late_short_crossing (a b e f : ℚ) (hab : a<b) (hef : e<f) (hbe : b<e) :
    ¬ProperCross (original a) (original b) (original e) (original f) := by
  rw [cap_ordered a b e f hab hef]
  rintro (h|h) <;> linarith [h.1,h.2.1]

noncomputable def paletteCost {E D L : ℕ} (early : Fin E → ℚ) (dummy : Fin D → ℚ)
    (late : Fin L → ℚ) (a b : Fin D) (color : Bool) : ℤ :=
  (∑ i : Fin E, ∑ j : Fin D,
    if ProperCross (original (dummy a)) (original (dummy b)) (original (early i)) (original (dummy j))
    then (if color=false then 1 else 0) else 0) +
  (∑ j : Fin D, ∑ k : Fin L,
    if ProperCross (original (dummy a)) (original (dummy b)) (original (dummy j)) (original (late k))
    then (if color=true then 1 else 0) else 0)

/-- Equal early and late populations give exactly equal opposite-color
palette neighborhoods. The cost is independent of the dummy chord's color. -/
theorem paletteCost_constant {E D : ℕ} (early late : Fin E → ℚ) (dummy : Fin D → ℚ)
    (hd : StrictMono dummy) (he : ∀ i j, early i<dummy j) (hl : ∀ i j, dummy j<late i)
    (a b : Fin D) (hab : a<b) (color : Bool) :
    paletteCost early dummy late a b color=(E:ℤ)*((b.val-a.val-1:ℕ):ℤ) := by
  classical
  have hE (i : Fin E) (j : Fin D) := early_dummy_crossing (early i) (dummy a) (dummy b) (dummy j)
    (hd hab) (he i a) (he i j)
  have hL (j : Fin D) (i : Fin E) := dummy_late_crossing (dummy a) (dummy b) (dummy j) (late i)
    (hd hab) (hl i b) (hl i j)
  have hcount : (∑ j : Fin D, if a<j ∧ j<b then (1:ℤ) else 0) =
      ((b.val-a.val-1:ℕ):ℤ) := by
    have hs : (Finset.univ : Finset (Fin D)).filter (fun j => a<j ∧ j<b) = Finset.Ioo a b := by
      ext j; simp
    rw [←Finset.sum_filter,hs]
    simp [Fin.card_Ioo]
  unfold paletteCost
  simp_rw [hE,hL,hd.lt_iff_lt]
  cases color
  · simp [hcount]
  · simp only [Bool.true_eq_false,ite_false,ite_true]
    simp only [Finset.sum_ite_irrel,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one,mul_zero,ite_self,zero_add]
    calc
      _ = ∑ j : Fin D, (E:ℤ)*(if a<j ∧ j<b then (1:ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = _ := by rw [←Finset.mul_sum,hcount]

theorem gap_sum (b : ℕ) :
    Finset.sum (Finset.range b) (fun a : ℕ => b - a - 1) = b.choose 2 := by
  have hr := Finset.sum_range_reflect (fun i : ℕ => i) b
  rw [Finset.sum_range_id,←Nat.choose_two_right] at hr
  calc
    _ = Finset.sum (Finset.range b) (fun a : ℕ => b - 1 - a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Nat.sub_right_comm b a 1
    _ = _ := hr

theorem choose_prefix (D k : ℕ) : (∑ b ∈ Finset.range D, b.choose k)=D.choose (k+1) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ,ih,Nat.choose_succ_succ]
    simp only [Nat.succ_eq_add_one]
    omega

/-- Summing the exact per-chord palette constants gives E*choose(D,3).
The finite sum enumerates each increasing dummy endpoint pair exactly once. -/
theorem all_gap_sum (E D : ℕ) :
    Finset.sum (Finset.range D) (fun b => Finset.sum (Finset.range b)
      (fun a => E * (b - a - 1))) = E * D.choose 3 := by
  simp_rw [←Finset.mul_sum, gap_sum]
  rw [choose_prefix]

/-- The triangular index gives exactly one name to every increasing dummy
chord. This is an actual finite equivalence, not a counting assumption. -/
def chordEquiv (D : ℕ) : (Σ b : Fin D, Fin b.val) ≃ {e : Fin D × Fin D // e.1 < e.2} where
  toFun x := ⟨(⟨x.2.val, lt_trans x.2.isLt x.1.isLt⟩, x.1), x.2.isLt⟩
  invFun e := ⟨e.val.2, ⟨e.val.1.val, e.property⟩⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro e; rfl

noncomputable def totalPaletteCost {E D : ℕ} (early late : Fin E → ℚ) (dummy : Fin D → ℚ)
    (color : {e : Fin D × Fin D // e.1 < e.2} → Bool) : ℤ :=
  ∑ e, paletteCost early dummy late e.val.1 e.val.2 (color e)

theorem totalPaletteCost_constant {E D : ℕ} (early late : Fin E → ℚ) (dummy : Fin D → ℚ)
    (hd : StrictMono dummy) (he : ∀ i j, early i < dummy j) (hl : ∀ i j, dummy j < late i)
    (color : {e : Fin D × Fin D // e.1 < e.2} → Bool) :
    totalPaletteCost early late dummy color = (E : ℤ) * (D.choose 3 : ℕ) := by
  unfold totalPaletteCost
  have hp (e : {e : Fin D × Fin D // e.1 < e.2}) :=
    paletteCost_constant early late dummy hd he hl e.val.1 e.val.2 e.property (color e)
  simp_rw [hp]
  rw [←(chordEquiv D).sum_comp]
  rw [Fintype.sum_sigma]
  change (∑ b : Fin D, ∑ a : Fin b.val, (E : ℤ) * ((b.val - a.val - 1 : ℕ) : ℤ)) = _
  have hg (b : ℕ) : (∑ a : Fin b, (b - a.val - 1)) = b.choose 2 := by
    exact (Fin.sum_univ_eq_sum_range (fun a : ℕ => b - a - 1) b).trans (gap_sum b)
  simp_rw [←Finset.mul_sum, ←Nat.cast_sum, hg]
  congr 2
  exact (Fin.sum_univ_eq_sum_range (fun b : ℕ => b.choose 2) D).trans (choose_prefix D 2)

end Q4.Candidate.DummyGeometry
#print axioms Q4.Candidate.DummyGeometry.early_dummy_crossing
#print axioms Q4.Candidate.DummyGeometry.dummy_late_crossing
#print axioms Q4.Candidate.DummyGeometry.no_early_late_crossing
#print axioms Q4.Candidate.DummyGeometry.no_early_short_crossing
#print axioms Q4.Candidate.DummyGeometry.no_late_short_crossing
#print axioms Q4.Candidate.DummyGeometry.paletteCost_constant

#print axioms Q4.Candidate.DummyGeometry.all_gap_sum

#print axioms Q4.Candidate.DummyGeometry.totalPaletteCost_constant
