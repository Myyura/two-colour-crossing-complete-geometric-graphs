import Q4.Candidate.ConvexSeparationGrid

/-!
Lemma 4.1 for the actual rational double-cap drawing. This module proves base
general position and the complete X-X crossing relation, including coincident
original or frame endpoints. Frame parameters decrease with the frame index;
original parameters increase with the original index.
-/

namespace Q4.Candidate.DoubleCapGrid

open Q4.Candidate.ConvexSeparation

def bridge (a b t : ℚ) : ℚ := 11 + (t ^ 2 + (a + b) * t - a * b) / 100

theorem bridge_positive (a b t : ℚ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 < bridge a b t := by
  have haa := unit_square_bound a (abs_le.mp ha).1 (abs_le.mp ha).2
  have hbb := unit_square_bound b (abs_le.mp hb).1 (abs_le.mp hb).2
  unfold bridge
  nlinarith [sq_nonneg (t + a), sq_nonneg (t + b), sq_nonneg (a - b)]

theorem original_vandermonde (a b c : ℚ) :
    orient (original a) (original b) (original c) =
      (b - a) * (c - a) * (c - b) / 100 := by
  unfold orient original
  ring

theorem frame_vandermonde (a b c : ℚ) :
    orient (frame a) (frame b) (frame c) =
      -(b - a) * (c - a) * (c - b) / 100 := by
  unfold orient frame
  ring

theorem original_pair_frame (a b t : ℚ) :
    orient (original a) (original b) (frame t) = -(b - a) * bridge a b t := by
  unfold orient original frame bridge
  ring

theorem frame_pair_original (a b t : ℚ) :
    orient (frame a) (frame b) (original t) = (b - a) * bridge a b t := by
  unfold orient original frame bridge
  ring

theorem original_injective : Function.Injective original := by
  intro a b he
  exact congrArg Prod.snd he

theorem frame_injective : Function.Injective frame := by
  intro a b he
  exact congrArg Prod.snd he

theorem original_frame_distinct (a t : ℚ) : original a ≠ frame t := by
  intro he
  have hx := congrArg Prod.fst he
  dsimp [original, frame] at hx
  nlinarith [sq_nonneg a, sq_nonneg t]

theorem original_triple_nonzero (a b c : ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient (original a) (original b) (original c) ≠ 0 := by
  rw [original_vandermonde]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hab))
    (sub_ne_zero.mpr (Ne.symm hac))) (sub_ne_zero.mpr (Ne.symm hbc))) (by norm_num)

theorem frame_triple_nonzero (a b c : ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient (frame a) (frame b) (frame c) ≠ 0 := by
  rw [frame_vandermonde]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hab)))
    (sub_ne_zero.mpr (Ne.symm hac))) (sub_ne_zero.mpr (Ne.symm hbc))) (by norm_num)

theorem original_pair_frame_nonzero (a b t : ℚ) (hab : a ≠ b)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) : orient (original a) (original b) (frame t) ≠ 0 := by
  rw [original_pair_frame]
  exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hab)))
    (ne_of_gt (bridge_positive a b t ha hb))

theorem frame_pair_original_nonzero (a b t : ℚ) (hab : a ≠ b)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) : orient (frame a) (frame b) (original t) ≠ 0 := by
  rw [frame_pair_original]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hab))
    (ne_of_gt (bridge_positive a b t ha hb))

def basePoints (ys ts : Finset ℚ) : Finset Point := ys.image original ∪ ts.image frame

theorem base_card (ys ts : Finset ℚ) : (basePoints ys ts).card = ys.card + ts.card := by
  have hd : Disjoint (ys.image original) (ts.image frame) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t, _, he⟩ := Finset.mem_image.mp hq
    exact original_frame_distinct a t he.symm
  unfold basePoints
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ original_injective,
    Finset.card_image_of_injective _ frame_injective]

/-- Every triple of distinct actual base points is noncollinear, for any
finite parameter sets in the specified cap intervals. -/
theorem base_general_position (ys ts : Finset ℚ)
    (hys : ∀ a ∈ ys, |a| ≤ 1) (hts : ∀ t ∈ ts, |t| ≤ 1) :
    GeneralPosition (basePoints ys ts) := by
  intro p hp q hq r hr hpq hpr hqr
  rcases Finset.mem_union.mp hp with hp | hp <;>
    rcases Finset.mem_union.mp hq with hq | hq <;>
    rcases Finset.mem_union.mp hr with hr | hr
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
    exact original_triple_nonzero a b c (fun h => hpq (congrArg original h))
      (fun h => hpr (congrArg original h)) (fun h => hqr (congrArg original h))
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    exact original_pair_frame_nonzero a b t (fun h => hpq (congrArg original h)) (hys a ha) (hys b hb)
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    rw [orient_reverse_last]
    exact neg_ne_zero.mpr (original_pair_frame_nonzero a b t
      (fun h => hpr (congrArg original h)) (hys a ha) (hys b hb))
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    rw [orient_cycle]
    exact frame_pair_original_nonzero t u a (fun h => hqr (congrArg frame h)) (hts t ht) (hts u hu)
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    rw [orient_cycle]
    exact original_pair_frame_nonzero a b t (fun h => hqr (congrArg original h)) (hys a ha) (hys b hb)
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    rw [orient_reverse_last]
    exact neg_ne_zero.mpr (frame_pair_original_nonzero t u a
      (fun h => hpr (congrArg frame h)) (hts t ht) (hts u hu))
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact frame_pair_original_nonzero t u a (fun h => hpq (congrArg frame h)) (hts t ht) (hts u hu)
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    exact frame_triple_nonzero t u v (fun h => hpq (congrArg frame h))
      (fun h => hpr (congrArg frame h)) (fun h => hqr (congrArg frame h))

theorem fan_orientation_original (a t b : ℚ) :
    orient (original a) (frame t) (original b) = (b - a) * bridge a b t := by
  unfold orient original frame bridge
  ring

theorem fan_orientation_frame (a t u : ℚ) :
    orient (original a) (frame t) (frame u) = (u - t) * bridge t u a := by
  unfold orient original frame bridge
  ring

/-- The strict sign test on the actual four endpoints, before substituting
the opposite parameter orders of the two cap sequences. -/
theorem fan_crossing_scalar (a b t u : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1) (hu : |u| ≤ 1) :
    ProperCross (original a) (frame t) (original b) (frame u) ↔ (b - a) * (u - t) < 0 := by
  have h1 : 0 < bridge a b t * bridge t u a :=
    mul_pos (bridge_positive a b t ha hb) (bridge_positive t u a ht hu)
  have h2 : 0 < bridge b a u * bridge u t b :=
    mul_pos (bridge_positive b a u hb ha) (bridge_positive u t b hu ht)
  have he1 : orient (original a) (frame t) (original b) * orient (original a) (frame t) (frame u) =
      ((b - a) * (u - t)) * (bridge a b t * bridge t u a) := by
    rw [fan_orientation_original, fan_orientation_frame]
    ring
  have he2 : orient (original b) (frame u) (original a) * orient (original b) (frame u) (frame t) =
      ((b - a) * (u - t)) * (bridge b a u * bridge u t b) := by
    rw [fan_orientation_original, fan_orientation_frame]
    ring
  have hh1 : ((b - a) * (u - t)) * (bridge a b t * bridge t u a) < 0 ↔ (b - a) * (u - t) < 0 := by
    simpa using (mul_lt_mul_iff_of_pos_right h1 :
      (b - a) * (u - t) * (bridge a b t * bridge t u a) < 0 * (bridge a b t * bridge t u a) ↔ _)
  have hh2 : ((b - a) * (u - t)) * (bridge b a u * bridge u t b) < 0 ↔ (b - a) * (u - t) < 0 := by
    simpa using (mul_lt_mul_iff_of_pos_right h2 :
      (b - a) * (u - t) * (bridge b a u * bridge u t b) < 0 * (bridge b a u * bridge u t b) ↔ _)
  simp only [ProperCross, he1, he2, hh1, hh2, and_self]

theorem fan_crossing_order (a b t u : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1) (hu : |u| ≤ 1) :
    ProperCross (original a) (frame t) (original b) (frame u) ↔
      (a < b ∧ u < t) ∨ (b < a ∧ t < u) := by
  rw [fan_crossing_scalar a b t u ha hb ht hu, mul_neg_iff]
  simp only [sub_pos, sub_neg]

/-- The exact strict comparison-grid adjacency, with the manuscript's reversed
frame parameter order. The same-row and same-column cases are included. -/
theorem indexed_grid_crossing (B O : ℕ) (ys : Fin O → ℚ) (ts : Fin B → ℚ)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (p q : Fin B × Fin O) :
    ProperCross (original (ys p.2)) (frame (ts p.1)) (original (ys q.2)) (frame (ts q.1)) ↔
      (p.1 < q.1 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ q.2 < p.2) := by
  rw [fan_crossing_order _ _ _ _ (hybox _) (hybox _) (htbox _) (htbox _)]
  rw [hy.lt_iff_lt, hy.lt_iff_lt, ht.lt_iff_gt, ht.lt_iff_gt]
  tauto

def frameParameter (B : ℕ) (i : Fin B) : ℚ :=
  1 - 2 * ((i.val : ℚ) + 1) / ((B : ℚ) + 1)

theorem frameParameter_antitone (B : ℕ) : StrictAnti (frameParameter B) := by
  intro i j hij
  have hh : (i.val : ℚ) < j.val := by exact_mod_cast hij
  have hden : 0 < (B : ℚ) + 1 := by positivity
  have hquot : 2 * ((i.val : ℚ) + 1) / ((B : ℚ) + 1) <
      2 * ((j.val : ℚ) + 1) / ((B : ℚ) + 1) :=
    (div_lt_div_iff_of_pos_right hden).2 (by linarith)
  dsimp [frameParameter]
  linarith

theorem frameParameter_unit (B : ℕ) (i : Fin B) : |frameParameter B i| < 1 := by
  have hi0 : 0 ≤ (i.val : ℚ) := by positivity
  have hiB : (i.val : ℚ) < B := by exact_mod_cast i.isLt
  have hden : 0 < (B : ℚ) + 1 := by positivity
  have hq0 : 0 < 2 * ((i.val : ℚ) + 1) / ((B : ℚ) + 1) := div_pos (by linarith) hden
  have hq2 : 2 * ((i.val : ℚ) + 1) / ((B : ℚ) + 1) < 2 :=
    (div_lt_iff₀ hden).2 (by linarith)
  unfold frameParameter
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Specialization to the exact frame sequence used by the candidate, not just
an assumed antitone family. Original coordinates may be any strictly increasing
valid rational sequence, including all selected clones and dummy points. -/
theorem actual_frame_grid_crossing (B O : ℕ) (ys : Fin O → ℚ)
    (hy : StrictMono ys) (hybox : ∀ j, |ys j| ≤ 1) (p q : Fin B × Fin O) :
    ProperCross (original (ys p.2)) (frame (frameParameter B p.1))
      (original (ys q.2)) (frame (frameParameter B q.1)) ↔
      (p.1 < q.1 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ q.2 < p.2) :=
  indexed_grid_crossing B O ys (frameParameter B) hy (frameParameter_antitone B)
    hybox (fun i => le_of_lt (frameParameter_unit B i)) p q

end Q4.Candidate.DoubleCapGrid

#print axioms Q4.Candidate.DoubleCapGrid.original_vandermonde
#print axioms Q4.Candidate.DoubleCapGrid.frame_vandermonde
#print axioms Q4.Candidate.DoubleCapGrid.original_pair_frame
#print axioms Q4.Candidate.DoubleCapGrid.frame_pair_original
#print axioms Q4.Candidate.DoubleCapGrid.base_card
#print axioms Q4.Candidate.DoubleCapGrid.base_general_position
#print axioms Q4.Candidate.DoubleCapGrid.fan_crossing_scalar
#print axioms Q4.Candidate.DoubleCapGrid.indexed_grid_crossing
#print axioms Q4.Candidate.DoubleCapGrid.frameParameter_antitone
#print axioms Q4.Candidate.DoubleCapGrid.frameParameter_unit
#print axioms Q4.Candidate.DoubleCapGrid.actual_frame_grid_crossing
