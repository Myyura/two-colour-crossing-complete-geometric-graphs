import Q4.Candidate.CoreReducedPairs

/-! The full (5.2) palette gives each actual dummy chord zero unary field.
The constant itself may be computed by ordinary crossing enumeration; no
optimization oracle is needed for this baseline term. -/
namespace Q4.Candidate.DummyPaletteField
open Q4.Candidate.ProposedPalette Q4.Candidate.PaletteCounting
open Q4.Candidate.OriginalCapAlternation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def coefficient {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S)
    (a b u v : Fin O) : ℤ :=
  if allowed (site u) (site v) ∧ cross ys a b u v then spin (color (site u) (site v)) else 0

theorem core_sum {O : ℕ} (f : Fin O → Fin O → ℤ) :
    (∑ e : CoreEdge O, f e.val.1 e.val.2) =
      ∑ u : Fin O, ∑ v : Fin O, if u<v then f u v else 0 := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun p : Fin O × Fin O => p.1<p.2))
    (by intro p; simp) (fun p => f p.1 p.2)]
  rw [Finset.sum_filter,Fintype.sum_prod_type]

theorem global_field_sum {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S) (a b : Fin O) :
    globalField ys site a b = ∑ u : Fin O, ∑ v : Fin O,
      if u<v then coefficient ys site a b u v else 0 := by
  unfold globalField palette
  rw [Finset.sum_filter]
  have hh : (∑ e : CoreEdge O,
      if allowed (site e.val.1) (site e.val.2) then
        (if cross ys a b e.val.1 e.val.2 then spin (paletteBit site e) else 0) else 0) =
      ∑ e : CoreEdge O, coefficient ys site a b e.val.1 e.val.2 := by
    apply Finset.sum_congr rfl
    intro e _
    unfold coefficient paletteBit
    split_ifs <;> simp_all
  rw [hh,core_sum]

theorem indexed_coefficient (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys)
    (a b u v : Fin (S*W+D+S*W)) (hab : a<b) (huv : u<v)
    (ha : S*W≤a.val) (hb : b.val<S*W+D) :
    coefficient ys (indexedSite S W D hW pi) a b u v =
      (if u.val<S*W ∧ a<v ∧ v<b then (-1:ℤ) else 0) +
      (if a<u ∧ u<b ∧ S*W+D≤v.val then 1 else 0) := by
  have hab' : a.val<b.val := hab
  have huv' : u.val<v.val := huv
  have hcross := cross_ordered ys hy a b u v hab huv
  unfold coefficient
  simp only [hcross]
  simp only [Fin.lt_def]
  unfold indexedSite
  split_ifs <;> simp_all [allowed,color,spin] <;> omega


theorem indexed_ordered_coefficient (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys)
    (a b u v : Fin (S*W+D+S*W)) (hab : a<b)
    (ha : S*W≤a.val) (hb : b.val<S*W+D) :
    (if u<v then coefficient ys (indexedSite S W D hW pi) a b u v else 0) =
      (if u.val<S*W ∧ a<v ∧ v<b then (-1:ℤ) else 0) +
      (if a<u ∧ u<b ∧ S*W+D≤v.val then 1 else 0) := by
  by_cases huv : u<v
  · rw [ite_eq_left huv]
    exact indexed_coefficient S W D hW pi ys hy a b u v hab huv ha hb
  · rw [ite_eq_right huv]
    simp only [Fin.lt_def] at *
    split_ifs <;> omega

theorem rectangle_sum {α β : Type*} [Fintype α] [Fintype β]
    (A : α → Prop) (B : β → Prop) [DecidablePred A] [DecidablePred B] (z : ℤ) :
    (∑ u : α, ∑ v : β, if A u ∧ B v then z else 0) =
      (∑ u : α, if A u then (1:ℤ) else 0) * (∑ v : β, if B v then z else 0) := by
  have hh (u : α) (v : β) : (if A u ∧ B v then z else 0) =
      (if A u then (1:ℤ) else 0) * (if B v then z else 0) := by split_ifs <;> simp_all
  simp_rw [hh,←Finset.mul_sum]
  rw [←Finset.sum_mul]

theorem side_counts (E D : ℕ) (hE : 0<E) :
    (∑ u : Fin (E+D+E), if u.val<E then (1:ℤ) else 0) = (E:ℤ) ∧
    (∑ u : Fin (E+D+E), if E+D≤u.val then (1:ℤ) else 0) = (E:ℤ) := by
  let lo : Fin (E+D+E) := ⟨E,by omega⟩
  let hi : Fin (E+D+E) := ⟨E+D,by omega⟩
  have hleft : (Finset.univ : Finset (Fin (E+D+E))).filter (fun u => u.val<E) = Finset.Iio lo := by
    ext u; simp [lo,Fin.lt_def]
  have hright : (Finset.univ : Finset (Fin (E+D+E))).filter (fun u => E+D≤u.val) = Finset.Ici hi := by
    ext u; simp [hi,Fin.le_def]
  constructor
  · rw [←Finset.sum_filter,hleft]
    simp [lo]
  · rw [←Finset.sum_filter,hright]
    simp [hi]

/-- Full palette balance on every actual dummy edge. No assumed palette
neighborhood list or prebalanced fields occurs in this statement. -/
theorem indexed_dummy_field_zero (S W D : ℕ) (hS : 0<S) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys)
    (a b : Fin (S*W+D+S*W)) (hab : a<b)
    (ha : S*W≤a.val) (hb : b.val<S*W+D) :
    globalField ys (indexedSite S W D hW pi) a b = 0 := by
  rw [global_field_sum]
  simp_rw [indexed_ordered_coefficient S W D hW pi ys hy a b _ _ hab ha hb]
  simp only [Finset.sum_add_distrib]
  have hfirst : (∑ u : Fin (S*W+D+S*W), ∑ v : Fin (S*W+D+S*W),
      if u.val<S*W ∧ a<v ∧ v<b then (-1:ℤ) else 0) =
      (S*W:ℕ) * (∑ v : Fin (S*W+D+S*W), if a<v ∧ v<b then (-1:ℤ) else 0) := by
    rw [rectangle_sum, (side_counts (S*W) D (Nat.mul_pos hS hW)).1]
  have hsecond : (∑ u : Fin (S*W+D+S*W), ∑ v : Fin (S*W+D+S*W),
      if a<u ∧ u<b ∧ S*W+D≤v.val then (1:ℤ) else 0) =
      (∑ u : Fin (S*W+D+S*W), if a<u ∧ u<b then (1:ℤ) else 0) * (S*W:ℕ) := by
    simp only [←and_assoc]
    rw [rectangle_sum, (side_counts (S*W) D (Nat.mul_pos hS hW)).2]
  rw [hfirst,hsecond]
  have hneg : (∑ v : Fin (S*W+D+S*W), if a<v ∧ v<b then (-1:ℤ) else 0) =
      -(∑ v : Fin (S*W+D+S*W), if a<v ∧ v<b then (1:ℤ) else 0) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> norm_num
  rw [hneg]
  ring


/-- The palette cost of every actual dummy chord is independent of its
color. The constant on the right is directly computable by crossing counts. -/
theorem indexed_dummy_cost_constant (S W D : ℕ) (hS : 0<S) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys)
    (a b : Fin (S*W+D+S*W)) (hab : a<b)
    (ha : S*W≤a.val) (hb : b.val<S*W+D) (bit : Bool) :
    globalCost ys (indexedSite S W D hW pi) a b bit =
      globalCost ys (indexedSite S W D hW pi) a b false := by
  have hz := indexed_dummy_field_zero S W D hS hW pi ys hy a b hab ha hb
  have hc := global_cost_difference ys (indexedSite S W D hW pi) a b
  cases bit
  · rfl
  · linarith

end Q4.Candidate.DummyPaletteField
#print axioms Q4.Candidate.DummyPaletteField.global_field_sum
#print axioms Q4.Candidate.DummyPaletteField.indexed_coefficient

#print axioms Q4.Candidate.DummyPaletteField.indexed_dummy_field_zero

#print axioms Q4.Candidate.DummyPaletteField.indexed_dummy_cost_constant
