import Q4.Candidate.RankTablePreservation
import Q4.Candidate.VirtualColumnSoftSupport

/-! Actual rank fields, including the parent block, equal the virtual column
exactly. The finite soft-row bound applies to the final placed points too. -/
open scoped BigOperators
namespace Q4.Candidate.RankSoftRows
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.RankGap Q4.Candidate.RankNonselected
open Q4.Candidate.RankTablePreservation Q4.Candidate.OrientationPreservation
open Q4.Candidate.UniformInsertion Q4.Candidate.VirtualColumnField
open Q4.Candidate.VirtualColumnSoftRows Q4.Candidate.VirtualColumnShape

noncomputable def pointColumn {B O : ℕ} (sigma : Fin B × Fin O → ℤ)
    (ys : Fin O → ℚ) (p : Point) (k : Fin B) (j : Fin O) : ℤ := by
  classical
  exact ∑ i : Fin B, if ProperCross p (frame (frameParameter B k))
    (original (ys j)) (frame (frameParameter B i)) then sigma (i,j) else 0

noncomputable def pointField {B O : ℕ} (sigma : Fin B × Fin O → ℤ)
    (ys : Fin O → ℚ) (p : Point) (k : Fin B) : ℤ :=
  ∑ j : Fin O, pointColumn sigma ys p k j

noncomputable def pointCost {B O : ℕ} (chi : Fin B × Fin O → Bool)
    (ys : Fin O → ℚ) (p : Point) (k : Fin B) (color : Bool) : ℤ := by
  classical
  exact ∑ j : Fin O, ∑ i : Fin B,
    if ProperCross p (frame (frameParameter B k)) (original (ys j)) (frame (frameParameter B i))
    then (if color=chi (i,j) then 1 else 0) else 0

theorem pointField_cost_difference {B O : ℕ} (chi : Fin B × Fin O → Bool)
    (ys : Fin O → ℚ) (p : Point) (k : Fin B) :
    pointField (colorSpin chi) ys p k = pointCost chi ys p k true-pointCost chi ys p k false := by
  classical
  unfold pointField pointColumn pointCost
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : ProperCross p (frame (frameParameter B k)) (original (ys j)) (frame (frameParameter B i)) <;>
    cases hx : chi (i,j) <;> simp [hc,colorSpin,hx]

structure Parameters where
  a : ℚ
  b : ℚ
  tau : ℚ
  w : ℚ
  mu : ℚ
  ell : ℚ
  ordered : a<b
  width : 2≤w
  mu_pos : 0<mu
  mu_small : 100*w*mu≤1
  tau_pos : 0<tau
  tau_small : 100*tau≤mu*(b-a)
  box_a : -1≤a-tau/2
  box_b : b+tau/2≤1
  gap_lo : 0≤ell
  gap_hi : ell+1≤w-1

/-- Coordinate/index data only; no crossing or field identity is a field. -/
structure LeftGeometry (B O cut : ℕ) extends Parameters where
  ys : Fin O → ℚ
  parent : Finset (Fin O)
  unit_y : ∀j, |ys j|≤1
  parent_clone : ∀j∈parent, ∃s : ℚ, 0≤s ∧ s≤w-1 ∧ ys j=cloneAt a tau w s
  parent_index : ∀j∈parent, j.val<cut
  nonparent_sep : ∀j∉parent, 2*mu*(b-a)≤|ys j-a|
  lower_index : ∀j∉parent, ys j<a ↔ j.val<cut
  upper_index : ∀j∉parent, a<ys j ↔ cut≤j.val

noncomputable def leftPoint {B O cut : ℕ} (d : LeftGeometry B O cut) : Point :=
  leftRank d.a d.b d.tau d.w d.mu d.ell

theorem left_crossing {B O cut : ℕ} (d : LeftGeometry B O cut) (i k : Fin B) (j : Fin O) :
    ProperCross (leftPoint d) (frame (frameParameter B k)) (original (d.ys j)) (frame (frameParameter B i)) ↔
      (i<k ∧ j.val<cut) ∨ (k<i ∧ cut≤j.val) := by
  by_cases hj : j∈d.parent
  · obtain ⟨s,hs,hs1,hys⟩ := d.parent_clone j hj
    have hindex := d.parent_index j hj
    unfold leftPoint
    rw [hys,leftRank_parent_fan_indexed B i k d.a d.b d.tau d.w d.mu d.ell s
      d.ordered d.width d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b
      d.gap_lo d.gap_hi hs hs1]
    simp [hindex,not_le.mpr hindex]
  · unfold leftPoint
    rw [leftRank_nonparent_fan_indexed B i k d.a d.b d.tau d.w d.mu d.ell (d.ys j)
      d.ordered d.width d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b
      d.gap_lo d.gap_hi (d.unit_y j) (d.nonparent_sep j hj),d.lower_index j hj,d.upper_index j hj]

/-- The same true table holds for every final copy in the common batch grid. -/
theorem placed_left_crossing {N O cut : ℕ} (d : LeftGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i) ∈ B) (hy : ∀j, original (d.ys j) ∈ B)
    (hr : leftPoint d ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (leftPoint d) p) (i k : Fin N) (j : Fin O) :
    ProperCross p (frame (frameParameter N k)) (original (d.ys j)) (frame (frameParameter N i)) ↔
      (i<k ∧ j.val<cut) ∨ (k<i ∧ cut≤j.val) := by
  by_cases hj : j∈d.parent
  · obtain ⟨s,hs,hs1,hys⟩ := d.parent_clone j hj
    have hindex := d.parent_index j hj
    have hc := hy j
    rw [hys] at hc ⊢
    rw [placed_leftRank_parent_fan M N B R i k d.a d.b d.tau d.w d.mu d.ell s p
      d.ordered d.width d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b
      d.gap_lo d.gap_hi hs hs1 (hf i) (hf k) hc hr hproto hp]
    simp [hindex,not_le.mpr hindex]
  · rw [placed_leftRank_nonparent_fan M N B R i k d.a d.b d.tau d.w d.mu d.ell (d.ys j) p
      d.ordered d.width d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b
      d.gap_lo d.gap_hi (d.unit_y j) (d.nonparent_sep j hj) (hf i) (hf k) (hy j) hr hproto hp,
      d.lower_index j hj,d.upper_index j hj]

/-- Coordinate/index data only; no crossing or field identity is a field. -/
structure RightGeometry (B O cut : ℕ) extends Parameters where
  ys : Fin O → ℚ
  parent : Finset (Fin O)
  unit_y : ∀j, |ys j|≤1
  parent_clone : ∀j∈parent, ∃s : ℚ, 0≤s ∧ s≤w-1 ∧ ys j=cloneAt b tau w s
  parent_index : ∀j∈parent, cut≤j.val
  nonparent_sep : ∀j∉parent, 2*mu*(b-a)≤|ys j-b|
  lower_index : ∀j∉parent, ys j<b ↔ j.val<cut
  upper_index : ∀j∉parent, b<ys j ↔ cut≤j.val

noncomputable def rightPoint {B O cut : ℕ} (d : RightGeometry B O cut) : Point :=
  rightRank d.a d.b d.tau d.w d.mu d.ell

theorem right_crossing {B O cut : ℕ} (d : RightGeometry B O cut) (i k : Fin B) (j : Fin O) :
    ProperCross (rightPoint d) (frame (frameParameter B k)) (original (d.ys j)) (frame (frameParameter B i)) ↔
      (i<k ∧ j.val<cut) ∨ (k<i ∧ cut≤j.val) := by
  by_cases hj : j∈d.parent
  · obtain ⟨s,hs,hs1,hys⟩ := d.parent_clone j hj
    have hindex := d.parent_index j hj
    unfold rightPoint
    rw [hys,rightRank_parent_fan_indexed B i k d.a d.b d.tau d.w d.mu d.ell s
      d.ordered d.width d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b
      d.gap_lo d.gap_hi hs hs1]
    simp [hindex,not_lt.mpr hindex]
  · unfold rightPoint
    rw [rightRank_nonparent_fan_indexed B i k d.a d.b d.tau d.w d.mu d.ell (d.ys j)
      d.ordered d.width d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b
      d.gap_lo d.gap_hi (d.unit_y j) (d.nonparent_sep j hj),d.lower_index j hj,d.upper_index j hj]

/-- The same true table holds for every final copy in the common batch grid. -/
theorem placed_right_crossing {N O cut : ℕ} (d : RightGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i) ∈ B) (hy : ∀j, original (d.ys j) ∈ B)
    (hr : rightPoint d ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (rightPoint d) p) (i k : Fin N) (j : Fin O) :
    ProperCross p (frame (frameParameter N k)) (original (d.ys j)) (frame (frameParameter N i)) ↔
      (i<k ∧ j.val<cut) ∨ (k<i ∧ cut≤j.val) := by
  by_cases hj : j∈d.parent
  · obtain ⟨s,hs,hs1,hys⟩ := d.parent_clone j hj
    have hindex := d.parent_index j hj
    have hc := hy j
    rw [hys] at hc ⊢
    rw [placed_rightRank_parent_fan M N B R i k d.a d.b d.tau d.w d.mu d.ell s p
      d.ordered d.width d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b
      d.gap_lo d.gap_hi hs hs1 (hf i) (hf k) hc hr hproto hp]
    simp [hindex,not_lt.mpr hindex]
  · rw [placed_rightRank_nonparent_fan M N B R i k d.a d.b d.tau d.w d.mu d.ell (d.ys j) p
      d.ordered d.width d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b
      d.gap_lo d.gap_hi (d.unit_y j) (d.nonparent_sep j hj) (hf i) (hf k) (hy j) hr hproto hp,
      d.lower_index j hj,d.upper_index j hj]

/-- Pure finite summation helper. Final rank theorems below supply its table
from explicit coordinates rather than postulating this hypothesis. -/
theorem pointField_eq_virtual_of_table {B O : ℕ} (sigma : Fin B × Fin O → ℤ)
    (ys : Fin O → ℚ) (p : Point) (cut : ℕ) (k : Fin B)
    (ht : ∀i j, ProperCross p (frame (frameParameter B k)) (original (ys j)) (frame (frameParameter B i)) ↔
      (i<k ∧ j.val<cut) ∨ (k<i ∧ cut≤j.val)) :
    pointField sigma ys p k=virtualField sigma cut k.val := by
  classical
  unfold pointField virtualField
  apply Finset.sum_congr rfl
  intro j _
  unfold pointColumn virtualColumn
  simp_rw [ht]
  by_cases hj : j.val<cut
  · simp only [hj,ite_true,not_le.mpr hj,and_true,and_false,or_false,rowPrefix]
    rfl
  · simp only [hj,ite_false,not_lt.mp hj,and_false,false_or,and_true,rowSuffix]
    rfl

noncomputable def actualSoftRows {B O : ℕ} (ys : Fin O → ℚ) (p : Point) (z : ℝ) : Finset (Fin B) :=
  Finset.univ.filter (fun k => |(pointField (spin : Fin B × Fin O → ℤ) ys p k:ℝ)|≤z*((B:ℝ)*O))

theorem actual_soft_card_of_field {B O cut : ℕ} (ys : Fin O → ℚ) (p : Point)
    (heq : ∀k, pointField (spin : Fin B × Fin O → ℤ) ys p k=virtualField (spin : Fin B × Fin O → ℤ) cut k.val)
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((actualSoftRows (B:=B) ys p z).card:ℝ) ≤ 12*(B:ℝ)*z+3 := by
  have hset : actualSoftRows (B:=B) ys p z=softRows B O cut z := by
    unfold actualSoftRows Q4.Candidate.VirtualColumnSoftRows.softRows
    apply Finset.filter_congr
    intro k _
    change (|(pointField (spin : Fin B × Fin O → ℤ) ys p k:ℝ)|≤z*((B:ℝ)*O)) ↔
      (|(virtualField (spin : Fin B × Fin O → ℤ) cut k.val:ℝ)|≤z*((B:ℝ)*O))
    rw [heq k]
  rw [hset]
  exact virtual_soft_card B O cut hO hBO hcut z hz hz1

/-- Exact actual rank field, for arbitrary integer grid weights. -/
theorem left_field_eq_virtual {B O cut : ℕ} (d : LeftGeometry B O cut)
    (sigma : Fin B × Fin O → ℤ) (k : Fin B) :
    pointField sigma d.ys (leftPoint d) k=virtualField sigma cut k.val :=
  pointField_eq_virtual_of_table sigma d.ys (leftPoint d) cut k (fun i j => left_crossing d i k j)

/-- Actual field equality survives the final common-radius placement. -/
theorem placed_left_field_eq_virtual {N O cut : ℕ} (d : LeftGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i) ∈ B) (hy : ∀j, original (d.ys j) ∈ B)
    (hr : leftPoint d ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (leftPoint d) p)
    (sigma : Fin N × Fin O → ℤ) (k : Fin N) :
    pointField sigma d.ys p k=virtualField sigma cut k.val :=
  pointField_eq_virtual_of_table sigma d.ys p cut k
    (fun i j => placed_left_crossing d M B R p hf hy hr hproto hp i k j)

/-- The manuscript's constant 12 for the actual left rank prototype. -/
theorem left_soft_card {B O cut : ℕ} (d : LeftGeometry B O cut)
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((actualSoftRows (B:=B) d.ys (leftPoint d) z).card:ℝ)≤12*(B:ℝ)*z+3 :=
  actual_soft_card_of_field d.ys (leftPoint d) (left_field_eq_virtual d spin)
    hO hBO hcut z hz hz1

/-- The same constant 12 holds for every final left rank copy; neither a
field formula nor a soft-set estimate is an input. -/
theorem placed_left_soft_card {N O cut : ℕ} (d : LeftGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i) ∈ B) (hy : ∀j, original (d.ys j) ∈ B)
    (hr : leftPoint d ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (leftPoint d) p)
    (hO : 1000≤O) (hBO : O≤N) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((actualSoftRows (B:=N) d.ys p z).card:ℝ)≤12*(N:ℝ)*z+3 :=
  actual_soft_card_of_field d.ys p (placed_left_field_eq_virtual d M B R p hf hy hr hproto hp spin)
    hO hBO hcut z hz hz1

/-- Exact actual rank field, for arbitrary integer grid weights. -/
theorem right_field_eq_virtual {B O cut : ℕ} (d : RightGeometry B O cut)
    (sigma : Fin B × Fin O → ℤ) (k : Fin B) :
    pointField sigma d.ys (rightPoint d) k=virtualField sigma cut k.val :=
  pointField_eq_virtual_of_table sigma d.ys (rightPoint d) cut k (fun i j => right_crossing d i k j)

/-- Actual field equality survives the final common-radius placement. -/
theorem placed_right_field_eq_virtual {N O cut : ℕ} (d : RightGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i) ∈ B) (hy : ∀j, original (d.ys j) ∈ B)
    (hr : rightPoint d ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (rightPoint d) p)
    (sigma : Fin N × Fin O → ℤ) (k : Fin N) :
    pointField sigma d.ys p k=virtualField sigma cut k.val :=
  pointField_eq_virtual_of_table sigma d.ys p cut k
    (fun i j => placed_right_crossing d M B R p hf hy hr hproto hp i k j)

/-- The manuscript's constant 12 for the actual right rank prototype. -/
theorem right_soft_card {B O cut : ℕ} (d : RightGeometry B O cut)
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((actualSoftRows (B:=B) d.ys (rightPoint d) z).card:ℝ)≤12*(B:ℝ)*z+3 :=
  actual_soft_card_of_field d.ys (rightPoint d) (right_field_eq_virtual d spin)
    hO hBO hcut z hz hz1

/-- The same constant 12 holds for every final right rank copy; neither a
field formula nor a soft-set estimate is an input. -/
theorem placed_right_soft_card {N O cut : ℕ} (d : RightGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i) ∈ B) (hy : ∀j, original (d.ys j) ∈ B)
    (hr : rightPoint d ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (rightPoint d) p)
    (hO : 1000≤O) (hBO : O≤N) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((actualSoftRows (B:=N) d.ys p z).card:ℝ)≤12*(N:ℝ)*z+3 :=
  actual_soft_card_of_field d.ys p (placed_right_field_eq_virtual d M B R p hf hy hr hproto hp spin)
    hO hBO hcut z hz hz1

end Q4.Candidate.RankSoftRows

#print axioms Q4.Candidate.RankSoftRows.pointField_cost_difference
#print axioms Q4.Candidate.RankSoftRows.left_crossing
#print axioms Q4.Candidate.RankSoftRows.right_crossing
#print axioms Q4.Candidate.RankSoftRows.left_field_eq_virtual
#print axioms Q4.Candidate.RankSoftRows.right_field_eq_virtual
#print axioms Q4.Candidate.RankSoftRows.placed_left_field_eq_virtual
#print axioms Q4.Candidate.RankSoftRows.placed_right_field_eq_virtual
#print axioms Q4.Candidate.RankSoftRows.left_soft_card
#print axioms Q4.Candidate.RankSoftRows.right_soft_card
#print axioms Q4.Candidate.RankSoftRows.placed_left_soft_card
#print axioms Q4.Candidate.RankSoftRows.placed_right_soft_card
