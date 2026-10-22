import Q4.Candidate.OrdinaryFan
import Q4.Candidate.CanonicalField

/-!
Actual finite signed grid fields and their virtual-column comparison.
The canonical spin uses the manuscript's strict diagonal convention. Geometric
ordinary fields sum all actual ProperCross neighbors; no field formula is an
input assumption.
-/

namespace Q4.Candidate.VirtualColumnField

open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid Q4.Candidate.OrdinaryFan

noncomputable def spin {B O : ℕ} (p : Fin B × Fin O) : ℤ :=
  if Q4.Candidate.CanonicalField.canonical p then 1 else -1

theorem spin_abs {B O : ℕ} (p : Fin B × Fin O) : |spin p| = 1 := by
  unfold spin
  split <;> norm_num

def rowPrefix {B O : ℕ} (σ : Fin B × Fin O → ℤ) (j : Fin O) (k : ℕ) : ℤ :=
  ∑ i : Fin B, if i.val < k then σ (i,j) else 0

def rowSuffix {B O : ℕ} (σ : Fin B × Fin O → ℤ) (j : Fin O) (k : ℕ) : ℤ :=
  ∑ i : Fin B, if k < i.val then σ (i,j) else 0

def virtualColumn {B O : ℕ} (σ : Fin B × Fin O → ℤ) (r k : ℕ) (j : Fin O) : ℤ :=
  if j.val < r then rowPrefix σ j k else rowSuffix σ j k

def virtualField {B O : ℕ} (σ : Fin B × Fin O → ℤ) (r k : ℕ) : ℤ :=
  ∑ j : Fin O, virtualColumn σ r k j

noncomputable def ordinaryColumn {B O : ℕ} (σ : Fin B × Fin O → ℤ) (ys : Fin O → ℚ)
    (a mu : ℚ) (k : Fin B) (j : Fin O) : ℤ := by
  classical
  exact ∑ i : Fin B, if ProperCross (ordinary a mu) (frame (frameParameter B k))
    (original (ys j)) (frame (frameParameter B i)) then σ (i,j) else 0

noncomputable def ordinaryField {B O : ℕ} (σ : Fin B × Fin O → ℤ) (ys : Fin O → ℚ)
    (a mu : ℚ) (k : Fin B) : ℤ := ∑ j : Fin O, ordinaryColumn σ ys a mu k j

def colorSpin {B O : ℕ} (χ : Fin B × Fin O → Bool) (p : Fin B × Fin O) : ℤ :=
  if χ p then 1 else -1

noncomputable def probeCost {B O : ℕ} (χ : Fin B × Fin O → Bool) (probe : Bool)
    (ys : Fin O → ℚ) (a mu : ℚ) (k : Fin B) : ℤ := by
  classical
  exact ∑ j : Fin O, ∑ i : Fin B,
    if ProperCross (ordinary a mu) (frame (frameParameter B k))
      (original (ys j)) (frame (frameParameter B i))
    then (if probe=χ (i,j) then 1 else 0) else 0

/-- The signed field really is cost(true)-cost(false) for all actual grid
neighbors of this program fan, under arbitrary Boolean grid coloring. -/
theorem ordinaryField_eq_cost_difference {B O : ℕ} (χ : Fin B × Fin O → Bool)
    (ys : Fin O → ℚ) (a mu : ℚ) (k : Fin B) :
    ordinaryField (colorSpin χ) ys a mu k =
      probeCost χ true ys a mu k-probeCost χ false ys a mu k := by
  classical
  unfold ordinaryField ordinaryColumn probeCost
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : ProperCross (ordinary a mu) (frame (frameParameter B k))
    (original (ys j)) (frame (frameParameter B i)) <;>
    cases hχ : χ (i,j) <;> simp [hc,colorSpin,hχ]

theorem canonical_spin_eq {B O : ℕ} :
    (spin : Fin B × Fin O → ℤ) = colorSpin Q4.Candidate.CanonicalField.canonical := rfl

theorem signed_row_bound {B : ℕ} (σ : Fin B → ℤ) (hσ : ∀ i, |σ i| ≤ 1)
    (P : Fin B → Prop) [DecidablePred P] :
    |∑ i : Fin B, if P i then σ i else 0| ≤ (B:ℤ) := by
  calc
    _ ≤ ∑ i : Fin B, |if P i then σ i else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin B, (1:ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : P i <;> simp [hi,hσ i]
    _ = _ := by simp

theorem ordinaryColumn_bound {B O : ℕ} (σ : Fin B × Fin O → ℤ)
    (hσ : ∀ p, |σ p| ≤ 1) (ys : Fin O → ℚ) (a mu : ℚ) (k : Fin B) (j : Fin O) :
    |ordinaryColumn σ ys a mu k j| ≤ (B:ℤ) := by
  classical
  exact signed_row_bound (fun i => σ (i,j)) (fun i => hσ _) _

theorem virtualColumn_bound {B O : ℕ} (σ : Fin B × Fin O → ℤ)
    (hσ : ∀ p, |σ p| ≤ 1) (r k : ℕ) (j : Fin O) :
    |virtualColumn σ r k j| ≤ (B:ℤ) := by
  unfold virtualColumn
  split
  · exact signed_row_bound (fun i => σ (i,j)) (fun i => hσ _) _
  · exact signed_row_bound (fun i => σ (i,j)) (fun i => hσ _) _

/-- Geometric nonparent columns are exactly equal to the actual virtual
prefix/suffix sums, for any signed grid coloring. -/
theorem ordinaryColumn_eq_virtual {B O : ℕ} (σ : Fin B × Fin O → ℤ)
    (ys : Fin O → ℚ) (a mu : ℚ) (r : ℕ) (k : Fin B) (j : Fin O)
    (ha : |a| ≤ 1) (hj : |ys j| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hsep : 5*mu ≤ |ys j-a|)
    (hleft : ys j < a ↔ j.val < r) (hright : a < ys j ↔ r ≤ j.val) :
    ordinaryColumn σ ys a mu k j = virtualColumn σ r k.val j := by
  classical
  unfold ordinaryColumn virtualColumn
  simp_rw [ordinary_nonparent_indexed B _ k a (ys j) mu ha hj hm hm1 hsep,hleft,hright]
  by_cases hjr : j.val < r
  · simp only [hjr,ite_true,not_le.mpr hjr,and_true,and_false,or_false,rowPrefix]
    rfl
  · simp only [hjr,ite_false,not_lt.mp hjr,and_false,false_or,and_true,rowSuffix]
    rfl

/-- The ordinary-field error is supported only on the actual parent columns.
This proves the 2 B W bound of (4.13) after setting W=parent.card, from actual
proper crossings and numerical geometric separation. -/
theorem ordinary_field_error {B O : ℕ} (σ : Fin B × Fin O → ℤ)
    (hσ : ∀ p, |σ p| ≤ 1) (ys : Fin O → ℚ) (a mu : ℚ) (r : ℕ)
    (parent : Finset (Fin O)) (k : Fin B)
    (ha : |a| ≤ 1) (hy : ∀ j, |ys j| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hsep : ∀ j ∉ parent, 5*mu ≤ |ys j-a|)
    (hleft : ∀ j ∉ parent, ys j < a ↔ j.val < r)
    (hright : ∀ j ∉ parent, a < ys j ↔ r ≤ j.val) :
    |ordinaryField σ ys a mu k - virtualField σ r k.val| ≤ 2*(B:ℤ)*parent.card := by
  have heq (j : Fin O) (hj : j ∉ parent) :
      ordinaryColumn σ ys a mu k j = virtualColumn σ r k.val j :=
    ordinaryColumn_eq_virtual σ ys a mu r k j ha (hy j) hm hm1 (hsep j hj)
      (hleft j hj) (hright j hj)
  unfold ordinaryField virtualField
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin O, |ordinaryColumn σ ys a mu k j - virtualColumn σ r k.val j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin O, if j ∈ parent then 2*(B:ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ parent
      · simp only [hj,ite_true]
        have ht := abs_sub_le (ordinaryColumn σ ys a mu k j) 0 (virtualColumn σ r k.val j)
        simp only [sub_zero,zero_sub,abs_neg] at ht
        linarith [ordinaryColumn_bound σ hσ ys a mu k j,virtualColumn_bound σ hσ r k.val j]
      · simp [hj,heq j hj]
    _ = _ := by simp [mul_comm]

theorem rowPrefix_step {B O : ℕ} (σ : Fin B × Fin O → ℤ) (j : Fin O) (k : Fin B) :
    rowPrefix σ j (k.val+1) = rowPrefix σ j k.val + σ (k,j) := by
  unfold rowPrefix
  have he (i : Fin B) : (if i.val < k.val+1 then σ (i,j) else 0) =
      (if i.val < k.val then σ (i,j) else 0) + (if i=k then σ (i,j) else 0) := by
    by_cases hik : i=k
    · subst i; simp
    · have hv : i.val ≠ k.val := by intro h; exact hik (Fin.ext h)
      by_cases hi : i.val < k.val
      · simp [hik,hi,show i.val < k.val+1 by omega]
      · simp [hik,hi,show ¬i.val < k.val+1 by omega]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

theorem rowSuffix_step {B O : ℕ} (σ : Fin B × Fin O → ℤ) (j : Fin O)
    (k l : Fin B) (hl : l.val=k.val+1) :
    rowSuffix σ j k.val = rowSuffix σ j l.val + σ (l,j) := by
  unfold rowSuffix
  have he (i : Fin B) : (if k.val < i.val then σ (i,j) else 0) =
      (if l.val < i.val then σ (i,j) else 0) + (if i=l then σ (i,j) else 0) := by
    by_cases hil : i=l
    · subst i; simp [show k.val < l.val by omega]
    · have hv : i.val ≠ l.val := by intro h; exact hil (Fin.ext h)
      by_cases hi : l.val < i.val
      · simp [hil,hi,show k.val < i.val by omega]
      · simp [hil,hi,show ¬k.val < i.val by omega]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

theorem virtualColumn_increment {B O : ℕ} (σ : Fin B × Fin O → ℤ) (r : ℕ)
    (j : Fin O) (k l : Fin B) (hl : l.val=k.val+1) :
    virtualColumn σ r l.val j-virtualColumn σ r k.val j =
      if j.val < r then σ (k,j) else -σ (l,j) := by
  have hp := rowPrefix_step σ j k
  have hs := rowSuffix_step σ j k l hl
  rw [←hl] at hp
  unfold virtualColumn
  by_cases hj : j.val < r <;> simp only [hj,ite_true,ite_false] <;> omega

/-- Exact finite row recurrence (4.11), including omission of the shared
frame-endpoint row. -/
theorem virtualField_increment {B O : ℕ} (σ : Fin B × Fin O → ℤ) (r : ℕ)
    (k l : Fin B) (hl : l.val=k.val+1) :
    virtualField σ r l.val-virtualField σ r k.val =
      (∑ j : Fin O, if j.val < r then σ (k,j) else 0) -
        (∑ j : Fin O, if r ≤ j.val then σ (l,j) else 0) := by
  unfold virtualField
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [virtualColumn_increment σ r j k l hl]
  by_cases hj : j.val < r
  · simp [hj,not_le.mpr hj]
  · simp [hj,not_lt.mp hj]

theorem ordinary_parent_column {B O : ℕ} (σ : Fin B × Fin O → ℤ)
    (ys : Fin O → ℚ) (a mu : ℚ) (k : Fin B) (j : Fin O) (hB : Even B)
    (ha : |a| ≤ 1) (hj : |ys j| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*((B:ℚ)+1)*|ys j-a| ≤ mu) :
    ordinaryColumn σ ys a mu k j =
      if k.val < B/2 then rowPrefix σ j k.val else rowSuffix σ j k.val := by
  classical
  unfold ordinaryColumn
  simp_rw [ordinary_clone_indexed B hB _ k a (ys j) mu ha hj hm hm1 hclone]
  by_cases hk : k.val < B/2
  · simp only [hk,ite_true,not_le.mpr hk,and_true,and_false,or_false,rowPrefix]; rfl
  · simp only [hk,ite_false,not_lt.mp hk,and_false,false_or,and_true,rowSuffix]; rfl

theorem ordinary_parent_increment {B O : ℕ} (σ : Fin B × Fin O → ℤ)
    (ys : Fin O → ℚ) (a mu : ℚ) (k l : Fin B) (j : Fin O) (hB : Even B)
    (hl : l.val=k.val+1) (hcut : l.val ≠ B/2)
    (ha : |a| ≤ 1) (hj : |ys j| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*((B:ℚ)+1)*|ys j-a| ≤ mu) :
    ordinaryColumn σ ys a mu l j-ordinaryColumn σ ys a mu k j =
      if k.val < B/2 then σ (k,j) else -σ (l,j) := by
  rw [ordinary_parent_column σ ys a mu l j hB ha hj hm hm1 hclone,
    ordinary_parent_column σ ys a mu k j hB ha hj hm hm1 hclone]
  have hp := rowPrefix_step σ j k
  have hs := rowSuffix_step σ j k l hl
  rw [←hl] at hp
  by_cases hk : k.val < B/2
  · simp only [hk,show l.val < B/2 by omega,ite_true]
    omega
  · simp only [hk,show ¬l.val < B/2 by omega,ite_false]
    omega

theorem supported_sum_bound {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → ℤ) (P : Finset J) (C : ℤ)
    (hz : ∀ j ∉ P, d j=0) (hb : ∀ j ∈ P, |d j| ≤ C) :
    |∑ j, d j| ≤ C*P.card := by
  calc
    _ ≤ ∑ j, |d j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, if j∈P then C else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j∈P
      · simpa only [hj,ite_true] using hb j hj
      · simp [hj,hz j hj]
    _ = _ := by simp [mul_comm]

/-- The actual ordinary versus virtual increment error, away from the central
ordinary switch. Both the 2W coefficient and the exceptional increment follow
from actual finite sums and the proved ordinary geometric tables. -/
theorem ordinary_field_increment_error {B O : ℕ} (σ : Fin B × Fin O → ℤ)
    (hσ : ∀ p, |σ p| ≤ 1) (ys : Fin O → ℚ) (a mu : ℚ) (r : ℕ)
    (parent : Finset (Fin O)) (k l : Fin B) (hB : Even B)
    (hl : l.val=k.val+1) (hcut : l.val ≠ B/2)
    (ha : |a| ≤ 1) (hy : ∀ j, |ys j| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : ∀ j ∈ parent, 3*((B:ℚ)+1)*|ys j-a| ≤ mu)
    (hsep : ∀ j ∉ parent, 5*mu ≤ |ys j-a|)
    (hleft : ∀ j ∉ parent, ys j < a ↔ j.val < r)
    (hright : ∀ j ∉ parent, a < ys j ↔ r ≤ j.val) :
    |(ordinaryField σ ys a mu l-ordinaryField σ ys a mu k)-
      (virtualField σ r l.val-virtualField σ r k.val)| ≤ 2*(parent.card:ℤ) := by
  let d := fun j => (ordinaryColumn σ ys a mu l j-ordinaryColumn σ ys a mu k j)-
    (virtualColumn σ r l.val j-virtualColumn σ r k.val j)
  have hz (j : Fin O) (hj : j ∉ parent) : d j=0 := by
    have he (v : Fin B) := ordinaryColumn_eq_virtual σ ys a mu r v j ha (hy j) hm hm1
      (hsep j hj) (hleft j hj) (hright j hj)
    dsimp [d]
    rw [he l,he k]
    omega
  have hb (j : Fin O) (hj : j ∈ parent) : |d j| ≤ 2 := by
    have he := ordinary_parent_increment σ ys a mu k l j hB hl hcut ha (hy j) hm hm1
      (hclone j hj)
    have hv := virtualColumn_increment σ r j k l hl
    dsimp [d]
    rw [he,hv]
    have hfirst : |if k.val < B/2 then σ (k,j) else -σ (l,j)| ≤ 1 := by
      split <;> simpa only [abs_neg] using hσ _
    have hsecond : |if j.val < r then σ (k,j) else -σ (l,j)| ≤ 1 := by
      split <;> simpa only [abs_neg] using hσ _
    have ht := abs_sub_le (if k.val < B/2 then σ (k,j) else -σ (l,j)) 0
      (if j.val < r then σ (k,j) else -σ (l,j))
    simp only [sub_zero,zero_sub,abs_neg] at ht
    omega
  have hs := supported_sum_bound d parent 2 hz hb
  unfold ordinaryField virtualField
  simp only [←Finset.sum_sub_distrib]
  exact hs

end Q4.Candidate.VirtualColumnField

#print axioms Q4.Candidate.VirtualColumnField.ordinaryColumn_eq_virtual
#print axioms Q4.Candidate.VirtualColumnField.ordinaryField_eq_cost_difference
#print axioms Q4.Candidate.VirtualColumnField.ordinary_field_error
#print axioms Q4.Candidate.VirtualColumnField.virtualField_increment
#print axioms Q4.Candidate.VirtualColumnField.ordinary_parent_increment
#print axioms Q4.Candidate.VirtualColumnField.ordinary_field_increment_error
