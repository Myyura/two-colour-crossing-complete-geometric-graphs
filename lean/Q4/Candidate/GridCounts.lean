import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Actual finite rectangular-grid counting for candidate Theorem 3.1.
Vertices are pairs `Fin m × Fin n`, with the manuscript's cell-center
coordinates. All cardinalities count those vertices, not a continuous proxy.
-/

namespace Q4.Candidate.GridCounts

abbrev Point (m n : Nat) := Fin m × Fin n

noncomputable def u (m : Nat) (i : Fin m) : ℝ := ((i : ℝ) + 1 / 2) / m

noncomputable def rho (m n : Nat) : ℝ := 1 / m + 1 / n

noncomputable def interval (m : Nat) (L U : ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => L ≤ u m i ∧ u m i ≤ U)

noncomputable def rectangle (m n : Nat) (L U V W : ℝ) : Finset (Point m n) :=
  Finset.univ.filter (fun p => L ≤ u m p.1 ∧ u m p.1 ≤ U ∧
    V ≤ u n p.2 ∧ u n p.2 ≤ W)

noncomputable def strip (m n : Nat) (w : ℝ) : Finset (Point m n) :=
  Finset.univ.filter (fun p => |u m p.1 + u n p.2 - 1| ≤ w)

noncomputable def corners (m n : Nat) (w : ℝ) : Finset (Point m n) :=
  Finset.univ.filter (fun p => u m p.1 + u n p.2 ≤ w ∨
    2 - w ≤ u m p.1 + u n p.2)

def adj {m n : Nat} (p q : Point m n) : Prop :=
  (p.1 < q.1 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ q.2 < p.2)

noncomputable def neighborsIn {m n : Nat} (S : Finset (Point m n)) (p : Point m n) :
    Finset (Point m n) := by classical exact S.filter (adj p)

noncomputable def forwardNeighbors {m n : Nat} (S : Finset (Point m n)) (p : Point m n) :
    Finset (Point m n) := S.filter (fun q => p.1 < q.1 ∧ p.2 < q.2)

noncomputable def orientedEdges (m n : Nat) : Finset (Point m n × Point m n) :=
  Finset.univ.filter (fun e => e.1.1 < e.2.1 ∧ e.1.2 < e.2.2)

noncomputable def inducedEdges {m n : Nat} (S : Finset (Point m n)) :
    Finset (Point m n × Point m n) :=
  (orientedEdges m n).filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)

/-- A finite set of integer ranks in a real interval has the expected length bound. -/
theorem nat_card_le_span (s : Finset Nat) (L U : ℝ) (hLU : L ≤ U)
    (h : ∀ i ∈ s, L ≤ (i : ℝ) ∧ (i : ℝ) ≤ U) :
    (s.card : ℝ) ≤ U - L + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := Finset.min'_mem s hs
    have hb : b ∈ s := Finset.max'_mem s hs
    have hab : a ≤ b := Finset.min'_le s b hb
    have hsub : s ⊆ Finset.Icc a b := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le s i hi, Finset.le_max' s i hi⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hc
    have hsum : s.card + a ≤ b + 1 := by omega
    have hsumR : (s.card : ℝ) + (a : ℝ) ≤ (b : ℝ) + 1 := by exact_mod_cast hsum
    have hL := (h a ha).1
    have hU := (h b hb).2
    linarith
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    linarith

theorem fin_card_le_span (s : Finset (Fin m)) (L U : ℝ) (hLU : L ≤ U)
    (h : ∀ i ∈ s, L ≤ (i : ℝ) ∧ (i : ℝ) ≤ U) :
    (s.card : ℝ) ≤ U - L + 1 := by
  classical
  have hc : (s.image Fin.val).card = s.card := Finset.card_image_iff.mpr
    (by intro a _ b _ heq; exact Fin.ext heq)
  have hi := nat_card_le_span (s.image Fin.val) L U hLU (by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact h i hi)
  simpa only [hc] using hi

/-- Center spacing is exactly `1/m`, with no aspect-ratio restriction. -/
theorem interval_card (m : Nat) (hm : 0 < m) (L U : ℝ) (hLU : L ≤ U) :
    ((interval m L U).card : ℝ) ≤ (m : ℝ) * (U - L) + 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hscaled : (m : ℝ) * L - 1/2 ≤ m * U - 1/2 := by nlinarith
  have h := fin_card_le_span (interval m L U)
    ((m : ℝ) * L - 1/2) (m * U - 1/2) hscaled (by
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      have hleft : L * m ≤ (i : ℝ) + 1/2 := (le_div_iff₀ hmR).mp hh.1
      have hright : (i : ℝ) + 1/2 ≤ U * m := (div_le_iff₀ hmR).mp hh.2
      constructor <;> nlinarith)
  nlinarith

theorem rectangle_eq_product (m n : Nat) (L U V W : ℝ) :
    rectangle m n L U V W = (interval m L U).product (interval n V W) := by
  classical
  ext p
  simp [rectangle, interval, and_assoc]

/-- The real count bound before normalization by N=mn. -/
theorem rectangle_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (L U V W : ℝ) (hLU : L ≤ U) (hVW : V ≤ W) :
    ((rectangle m n L U V W).card : ℝ) ≤
      ((m : ℝ) * (U - L) + 1) * ((n : ℝ) * (W - V) + 1) := by
  rw [rectangle_eq_product]
  simp only [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
  have hx := interval_card m hm L U hLU
  have hy := interval_card n hn V W hVW
  apply mul_le_mul hx hy
  · positivity
  · have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

theorem rho_nonneg (m n : Nat) : 0 ≤ rho m n := by unfold rho; positivity

theorem one_le_mul_rho_left (m n : Nat) (hm : 0 < m) :
    1 ≤ (m : ℝ) * rho m n := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have he : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
  unfold rho
  rw [mul_add, he]
  have h : (0 : ℝ) ≤ (m : ℝ) * (1 / (n : ℝ)) := by positivity
  linarith

theorem one_le_mul_rho_right (m n : Nat) (hn : 0 < n) :
    1 ≤ (n : ℝ) * rho m n := by
  simpa [rho, add_comm] using one_le_mul_rho_left n m hn

/-- The manuscript's normalized rectangle estimate with rho=1/m+1/n. -/
theorem rectangle_card_normalized (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (L U V W : ℝ) (hLU : L ≤ U) (hVW : V ≤ W) :
    ((rectangle m n L U V W).card : ℝ) ≤
      (m : ℝ) * n * (U - L + rho m n) * (W - V + rho m n) := by
  have hbase := rectangle_card m n hm hn L U V W hLU hVW
  have hx := one_le_mul_rho_left m n hm
  have hy := one_le_mul_rho_right m n hn
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hp : ((m : ℝ) * (U-L)+1) * ((n : ℝ) * (W-V)+1) ≤
      ((m : ℝ) * (U-L+rho m n)) * ((n : ℝ) * (W-V+rho m n)) := by
    apply mul_le_mul
    · nlinarith
    · nlinarith
    · nlinarith
    · have hr := rho_nonneg m n
      positivity
  nlinarith [le_trans hbase hp]

theorem strip_eq_rows (m n : Nat) (w : ℝ) :
    strip m n w = Finset.univ.biUnion (fun i : Fin m =>
      (interval n (1-w-u m i) (1+w-u m i)).image (fun j => (i,j))) := by
  classical
  ext p
  constructor
  · intro hp
    have hs := abs_le.mp (Finset.mem_filter.mp hp).2
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩⟩
    simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> linarith
  · intro hp
    obtain ⟨i, _, jmem⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp jmem
    subst p
    have hs := (Finset.mem_filter.mp hj).2
    simp only [strip, Finset.mem_filter, Finset.mem_univ, true_and]
    apply abs_le.mpr
    constructor <;> linarith

/-- Exact row counting before using rho<=w. -/
theorem strip_card_rows (m n : Nat) (hn : 0 < n) (w : ℝ) (hw : 0 ≤ w) :
    ((strip m n w).card : ℝ) ≤ (m : ℝ) * (2 * n * w + 1) := by
  classical
  rw [strip_eq_rows]
  have hcard := @Finset.card_biUnion_le (Fin m) (Point m n) _
    Finset.univ (fun i => (interval n (1-w-u m i) (1+w-u m i)).image (fun j => (i,j)))
  have hcardR : ((Finset.univ.biUnion (fun i : Fin m =>
      (interval n (1-w-u m i) (1+w-u m i)).image (fun j => (i,j)))).card : ℝ) ≤
      ∑ i : Fin m, (((interval n (1-w-u m i) (1+w-u m i)).image (fun j => (i,j))).card : ℝ) :=
    by exact_mod_cast hcard
  have hsum : (∑ i : Fin m,
      (((interval n (1-w-u m i) (1+w-u m i)).image (fun j => (i,j))).card : ℝ)) ≤
      ∑ _i : Fin m, (2 * (n : ℝ) * w + 1) := by
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.card_image_of_injective _ (by intro x y heq; exact (Prod.mk.inj heq).2)]
    have hi := interval_card n hn (1-w-u m i) (1+w-u m i) (by linarith)
    nlinarith
  have hsimp : (∑ _i : Fin m, (2 * (n : ℝ) * w + 1)) = (m : ℝ) * (2 * n * w + 1) := by simp
  exact le_trans hcardR (hsimp ▸ hsum)

/-- The actual finite diagonal strip contains at most 3*w*N vertices. -/
theorem strip_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (hw : rho m n ≤ w) :
    ((strip m n w).card : ℝ) ≤ 3 * w * ((m : ℝ) * n) := by
  have hw0 : 0 ≤ w := le_trans (rho_nonneg m n) hw
  have hs := strip_card_rows m n hn w hw0
  have hnrho := one_le_mul_rho_right m n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnw : 1 ≤ (n : ℝ) * w := by nlinarith
  have hm0 : (0 : ℝ) ≤ m := by positivity
  nlinarith

theorem u_pos (m : Nat) (hm : 0 < m) (i : Fin m) : 0 < u m i := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold u
  positivity

theorem u_lt_one (m : Nat) (hm : 0 < m) (i : Fin m) : u m i < 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hi : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.isLt
  unfold u
  apply (div_lt_iff₀ hmR).mpr
  linarith

theorem corners_subset_squares (m n : Nat) (hm : 0 < m) (hn : 0 < n) (w : ℝ) :
    corners m n w ⊆ rectangle m n 0 w 0 w ∪ rectangle m n (1-w) 1 (1-w) 1 := by
  classical
  intro p hp
  have hx0 := u_pos m hm p.1
  have hy0 := u_pos n hn p.2
  have hx1 := u_lt_one m hm p.1
  have hy1 := u_lt_one n hn p.2
  rcases (Finset.mem_filter.mp hp).2 with hlo | hhi
  · apply Finset.mem_union_left
    simp only [rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · apply Finset.mem_union_right
    simp only [rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Both corner triangles together contain at most 8*w^2*N vertices. -/
theorem corners_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (hw : rho m n ≤ w) :
    ((corners m n w).card : ℝ) ≤ 8 * w^2 * ((m : ℝ) * n) := by
  classical
  have hr0 := rho_nonneg m n
  have hw0 : 0 ≤ w := le_trans hr0 hw
  have hc := le_trans (Finset.card_le_card (corners_subset_squares m n hm hn w))
    (Finset.card_union_le (rectangle m n 0 w 0 w) (rectangle m n (1-w) 1 (1-w) 1))
  have hcR : ((corners m n w).card : ℝ) ≤
      ((rectangle m n 0 w 0 w).card : ℝ) +
      ((rectangle m n (1-w) 1 (1-w) 1).card : ℝ) := by exact_mod_cast hc
  have hl := rectangle_card_normalized m n hm hn 0 w 0 w hw0 hw0
  have hu := rectangle_card_normalized m n hm hn (1-w) 1 (1-w) 1 (by linarith) (by linarith)
  have hsq : (w + rho m n)^2 ≤ 4*w^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ (m:ℝ)*n by positivity)
  nlinarith

theorem u_mono (m : Nat) (hm : 0 < m) (i j : Fin m) (hij : i ≤ j) :
    u m i ≤ u m j := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold u
  apply (div_le_div_iff_of_pos_right hmR).mpr
  have hi : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  linarith

theorem strip_forward_subset_square (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (p : Point m n) (hp : p ∈ strip m n w) :
    forwardNeighbors (strip m n w) p ⊆
      rectangle m n (u m p.1) (u m p.1+2*w) (u n p.2) (u n p.2+2*w) := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hps := abs_le.mp (Finset.mem_filter.mp hp).2
  have hqs := abs_le.mp (Finset.mem_filter.mp hq'.1).2
  have hxu := u_mono m hm p.1 q.1 (le_of_lt hq'.2.1)
  have hyu := u_mono n hn p.2 q.2 (le_of_lt hq'.2.2)
  simp only [rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hxu, by linarith, hyu, by linarith⟩

theorem strip_neighbors_subset_squares (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (p : Point m n) (hp : p ∈ strip m n w) :
    neighborsIn (strip m n w) p ⊆
      rectangle m n (u m p.1) (u m p.1+2*w) (u n p.2) (u n p.2+2*w) ∪
      rectangle m n (u m p.1-2*w) (u m p.1) (u n p.2-2*w) (u n p.2) := by
  classical
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  rcases hq'.2 with hf | hb
  · apply Finset.mem_union_left
    exact strip_forward_subset_square m n hm hn w p hp (Finset.mem_filter.mpr ⟨hq'.1,hf⟩)
  · apply Finset.mem_union_right
    have hps := abs_le.mp (Finset.mem_filter.mp hp).2
    have hqs := abs_le.mp (Finset.mem_filter.mp hq'.1).2
    have hxu := u_mono m hm q.1 p.1 (le_of_lt hb.1)
    have hyu := u_mono n hn q.2 p.2 (le_of_lt hb.2)
    simp only [rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by linarith, hxu, by linarith, hyu⟩

theorem square_two_w_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w L V : ℝ) (hw : rho m n ≤ w) :
    ((rectangle m n L (L+2*w) V (V+2*w)).card : ℝ) ≤
      9*w^2*((m:ℝ)*n) := by
  have hr := rho_nonneg m n
  have hw0 : 0 ≤ w := le_trans hr hw
  have hrect := rectangle_card_normalized m n hm hn L (L+2*w) V (V+2*w)
    (by linarith) (by linarith)
  have hsq : (2*w+rho m n)^2 ≤ 9*w^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ (m:ℝ)*n by positivity)
  nlinarith

theorem strip_forward_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (hw : rho m n ≤ w) (p : Point m n) (hp : p ∈ strip m n w) :
    ((forwardNeighbors (strip m n w) p).card : ℝ) ≤ 9*w^2*((m:ℝ)*n) := by
  have hc := Finset.card_le_card (strip_forward_subset_square m n hm hn w p hp)
  have hcR : ((forwardNeighbors (strip m n w) p).card : ℝ) ≤
      ((rectangle m n (u m p.1) (u m p.1+2*w) (u n p.2) (u n p.2+2*w)).card : ℝ) :=
    by exact_mod_cast hc
  exact le_trans hcR (square_two_w_card m n hm hn w (u m p.1) (u n p.2) hw)

theorem strip_neighbors_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (hw : rho m n ≤ w) (p : Point m n) (hp : p ∈ strip m n w) :
    ((neighborsIn (strip m n w) p).card : ℝ) ≤ 18*w^2*((m:ℝ)*n) := by
  classical
  have hc := le_trans (Finset.card_le_card (strip_neighbors_subset_squares m n hm hn w p hp))
    (Finset.card_union_le _ _)
  have hcR : ((neighborsIn (strip m n w) p).card : ℝ) ≤
      ((rectangle m n (u m p.1) (u m p.1+2*w) (u n p.2) (u n p.2+2*w)).card : ℝ) +
      ((rectangle m n (u m p.1-2*w) (u m p.1) (u n p.2-2*w) (u n p.2)).card : ℝ) :=
    by exact_mod_cast hc
  have h1 := square_two_w_card m n hm hn w (u m p.1) (u n p.2) hw
  have h2 := square_two_w_card m n hm hn w (u m p.1-2*w) (u n p.2-2*w) hw
  have he1 : u m p.1-2*w+2*w = u m p.1 := by ring
  have he2 : u n p.2-2*w+2*w = u n p.2 := by ring
  rw [he1,he2] at h2
  linarith

/-- The 26*w^2*N degree bound is restricted to strip vertices, as required. -/
theorem localized_degree (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (hw : rho m n ≤ w) (S : Finset (Point m n))
    (hS : S ⊆ strip m n w ∪ corners m n w)
    (p : Point m n) (hp : p ∈ strip m n w) :
    ((neighborsIn S p).card : ℝ) ≤ 26*w^2*((m:ℝ)*n) := by
  classical
  have hsub : neighborsIn S p ⊆ neighborsIn (strip m n w) p ∪ corners m n w := by
    intro q hq
    have hqm := Finset.mem_filter.mp hq
    rcases Finset.mem_union.mp (hS hqm.1) with hd | hc
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd,hqm.2⟩)
    · exact Finset.mem_union_right _ hc
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hcR : ((neighborsIn S p).card : ℝ) ≤
      ((neighborsIn (strip m n w) p).card : ℝ) + ((corners m n w).card : ℝ) :=
    by exact_mod_cast hc
  have hd := strip_neighbors_card m n hm hn w hw p hp
  have hcorn := corners_card m n hm hn w hw
  linarith

@[simp] theorem mem_inducedEdges {m n : Nat} (S : Finset (Point m n))
    (e : Point m n × Point m n) :
    e ∈ inducedEdges S ↔ e.1 ∈ S ∧ e.2 ∈ S ∧ e.1.1 < e.2.1 ∧ e.1.2 < e.2.2 := by
  simp only [inducedEdges, orientedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hord,hmem⟩
    exact ⟨hmem.1,hmem.2,hord.1,hord.2⟩
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨⟨h3,h4⟩,⟨h1,h2⟩⟩

theorem inducedEdges_eq_rows {m n : Nat} (S : Finset (Point m n)) :
    inducedEdges S = S.biUnion (fun p => (forwardNeighbors S p).image (fun q => (p,q))) := by
  classical
  ext e
  constructor
  · intro he
    have h := (mem_inducedEdges S e).mp he
    exact Finset.mem_biUnion.mpr ⟨e.1,h.1,
      Finset.mem_image.mpr ⟨e.2,Finset.mem_filter.mpr ⟨h.2.1,h.2.2⟩,rfl⟩⟩
  · intro he
    obtain ⟨p,hp,hrow⟩ := Finset.mem_biUnion.mp he
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hrow
    subst e
    have hq' := Finset.mem_filter.mp hq
    exact (mem_inducedEdges S (p,q)).mpr ⟨hp,hq'.1,hq'.2.1,hq'.2.2⟩

/-- Bounds the actual once-oriented edge set by its forward degrees. -/
theorem inducedEdges_card_le {m n : Nat} (S : Finset (Point m n)) (L : ℝ)
    (hL : ∀ p ∈ S, ((forwardNeighbors S p).card : ℝ) ≤ L) :
    ((inducedEdges S).card : ℝ) ≤ (S.card : ℝ) * L := by
  classical
  rw [inducedEdges_eq_rows]
  have hc := @Finset.card_biUnion_le (Point m n) (Point m n × Point m n) _
    S (fun p => (forwardNeighbors S p).image (fun q => (p,q)))
  have hcR : ((S.biUnion (fun p => (forwardNeighbors S p).image (fun q => (p,q)))).card : ℝ) ≤
      ∑ p ∈ S, (((forwardNeighbors S p).image (fun q => (p,q))).card : ℝ) := by exact_mod_cast hc
  have hs : (∑ p ∈ S, (((forwardNeighbors S p).image (fun q => (p,q))).card : ℝ)) ≤
      ∑ _p ∈ S, L := by
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.card_image_of_injective _ (by intro x y heq; exact (Prod.mk.inj heq).2)]
    exact hL p hp
  have hsimp : (∑ _p ∈ S, L) = (S.card : ℝ) * L := by simp
  exact le_trans hcR (hsimp ▸ hs)

theorem strip_edges_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (hw : rho m n ≤ w) :
    ((inducedEdges (strip m n w)).card : ℝ) ≤ 27*w^3*((m:ℝ)*n)^2 := by
  have hd := inducedEdges_card_le (strip m n w) (9*w^2*((m:ℝ)*n))
    (fun p hp => strip_forward_card m n hm hn w hw p hp)
  have hs := strip_card m n hm hn w hw
  have hm0 : 0 ≤ 9*w^2*((m:ℝ)*n) := by positivity
  calc
    ((inducedEdges (strip m n w)).card : ℝ) ≤
        ((strip m n w).card : ℝ) * (9*w^2*((m:ℝ)*n)) := hd
    _ ≤ (3*w*((m:ℝ)*n)) * (9*w^2*((m:ℝ)*n)) := mul_le_mul_of_nonneg_right hs hm0
    _ = 27*w^3*((m:ℝ)*n)^2 := by ring

/-- No ordered edge and its reversal can both belong to the actual grid edge set. -/
theorem oriented_no_swap {m n : Nat} (e f : Point m n × Point m n)
    (he : e ∈ orientedEdges m n) (hf : f ∈ orientedEdges m n) : e ≠ f.swap := by
  intro h
  subst e
  have he' := (Finset.mem_filter.mp he).2.1
  have hf' := (Finset.mem_filter.mp hf).2.1
  exact (lt_asymm he' hf')

/-- Twice the actual induced edge count is at most the squared vertex count. -/
theorem twice_inducedEdges_le_square {m n : Nat} (S : Finset (Point m n)) :
    2 * (inducedEdges S).card ≤ S.card * S.card := by
  classical
  let E := inducedEdges S
  have hdis : Disjoint E (E.image Prod.swap) := by
    apply Finset.disjoint_left.mpr
    intro e he hr
    obtain ⟨f,hf,heq⟩ := Finset.mem_image.mp hr
    exact oriented_no_swap e f (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 heq.symm
  have hsub : E ∪ E.image Prod.swap ⊆ S.product S := by
    intro e he
    rcases Finset.mem_union.mp he with he | hr
    · have h := (mem_inducedEdges S e).mp he
      simpa only [Finset.product_eq_sprod, Finset.mem_product] using And.intro h.1 h.2.1
    · obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hr
      have h := (mem_inducedEdges S f).mp hf
      simp only [Finset.product_eq_sprod, Finset.mem_product]
      exact And.intro h.2.1 h.1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ Prod.swap_injective] at hc
  simp only [Finset.product_eq_sprod, Finset.card_product] at hc
  dsimp [E] at hc
  omega

noncomputable def crossEdges {m n : Nat} (D C : Finset (Point m n)) :
    Finset (Point m n × Point m n) :=
  (orientedEdges m n).filter (fun e =>
    (e.1 ∈ D ∧ e.2 ∈ C) ∨ (e.2 ∈ D ∧ e.1 ∈ C))

theorem crossEdges_card_le {m n : Nat} (D C : Finset (Point m n)) :
    (crossEdges D C).card ≤ D.card * C.card := by
  classical
  let orient : (Point m n × Point m n) → (Point m n × Point m n) :=
    fun e => if e.1 ∈ D ∧ e.2 ∈ C then e else e.swap
  have hinj : Set.InjOn orient (crossEdges D C) := by
    intro e he f hf hef
    have he0 := (Finset.mem_filter.mp he).1
    have hf0 := (Finset.mem_filter.mp hf).1
    by_cases hec : e.1 ∈ D ∧ e.2 ∈ C <;> by_cases hfc : f.1 ∈ D ∧ f.2 ∈ C
    · simpa [orient,hec,hfc] using hef
    · have heq : e = f.swap := by simpa [orient,hec,hfc] using hef
      exact False.elim (oriented_no_swap e f he0 hf0 heq)
    · have heq : f = e.swap := by simpa [orient,hec,hfc] using hef.symm
      exact False.elim (oriented_no_swap f e hf0 he0 heq)
    · have heq : e.swap = f.swap := by simpa [orient,hec,hfc] using hef
      exact Prod.swap_inj.mp heq
  have hsub : (crossEdges D C).image orient ⊆ D.product C := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    have hm := (Finset.mem_filter.mp hf).2
    by_cases hc : f.1 ∈ D ∧ f.2 ∈ C
    · simp [orient,hc,Finset.product_eq_sprod]
    · have hb : f.2 ∈ D ∧ f.1 ∈ C := hm.resolve_left hc
      simpa [orient,hc,Finset.product_eq_sprod] using hb
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj] at hcard
  simpa only [Finset.product_eq_sprod, Finset.card_product] using hcard

theorem inducedEdges_partition_bound {m n : Nat} (S D C : Finset (Point m n))
    (hS : S ⊆ D ∪ C) :
    (inducedEdges S).card ≤ (inducedEdges D).card + (crossEdges D C).card + (inducedEdges C).card := by
  classical
  have hsub : inducedEdges S ⊆ (inducedEdges D ∪ crossEdges D C) ∪ inducedEdges C := by
    intro e he
    have hs := (mem_inducedEdges S e).mp he
    have he0 := (Finset.mem_filter.mp he).1
    rcases Finset.mem_union.mp (hS hs.1) with hd1 | hc1 <;>
      rcases Finset.mem_union.mp (hS hs.2.1) with hd2 | hc2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((mem_inducedEdges D e).mpr ⟨hd1,hd2,hs.2.2⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨he0,Or.inl ⟨hd1,hc2⟩⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨he0,Or.inr ⟨hd2,hc1⟩⟩))
    · exact Finset.mem_union_right _ ((mem_inducedEdges C e).mpr ⟨hc1,hc2,hs.2.2⟩)
  have hc := Finset.card_le_card hsub
  have h1 := Finset.card_union_le (inducedEdges D ∪ crossEdges D C) (inducedEdges C)
  have h2 := Finset.card_union_le (inducedEdges D) (crossEdges D C)
  omega

/-- The manuscript's 83*w^3*N^2 bound, on the actual once-oriented edge set. -/
theorem localized_edges_card (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (w : ℝ) (hw : rho m n ≤ w) (hw1 : w ≤ 1) (S : Finset (Point m n))
    (hS : S ⊆ strip m n w ∪ corners m n w) :
    ((inducedEdges S).card : ℝ) ≤ 83*w^3*((m:ℝ)*n)^2 := by
  have hw0 : 0 ≤ w := le_trans (rho_nonneg m n) hw
  have hds := strip_card m n hm hn w hw
  have hcs := corners_card m n hm hn w hw
  have hdd := strip_edges_card m n hm hn w hw
  have hdc0 := crossEdges_card_le (strip m n w) (corners m n w)
  have hdcR : ((crossEdges (strip m n w) (corners m n w)).card : ℝ) ≤
      ((strip m n w).card : ℝ) * ((corners m n w).card : ℝ) := by exact_mod_cast hdc0
  have hprod := mul_le_mul hds hcs (by positivity : (0:ℝ) ≤ ((corners m n w).card : ℝ))
    (by positivity : (0:ℝ) ≤ 3*w*((m:ℝ)*n))
  have hdc : ((crossEdges (strip m n w) (corners m n w)).card : ℝ) ≤
      24*w^3*((m:ℝ)*n)^2 := by nlinarith [le_trans hdcR hprod]
  have hcc0 := twice_inducedEdges_le_square (corners m n w)
  have hccR : 2 * ((inducedEdges (corners m n w)).card : ℝ) ≤
      ((corners m n w).card : ℝ)^2 := by
    rw [pow_two]
    exact_mod_cast hcc0
  have hc0 : (0:ℝ) ≤ ((corners m n w).card : ℝ) := by positivity
  have hsq : ((corners m n w).card : ℝ)^2 ≤ (8*w^2*((m:ℝ)*n))^2 := by nlinarith
  have hcc : ((inducedEdges (corners m n w)).card : ℝ) ≤ 32*w^4*((m:ℝ)*n)^2 := by nlinarith
  have hpart := inducedEdges_partition_bound S (strip m n w) (corners m n w) hS
  have hpR : ((inducedEdges S).card : ℝ) ≤ ((inducedEdges (strip m n w)).card : ℝ) +
      ((crossEdges (strip m n w) (corners m n w)).card : ℝ) +
      ((inducedEdges (corners m n w)).card : ℝ) := by exact_mod_cast hpart
  have hpow : w^4 ≤ w^3 := by nlinarith [pow_nonneg hw0 2, pow_nonneg hw0 3]
  have hscale := mul_le_mul_of_nonneg_right hpow (show (0:ℝ) ≤ ((m:ℝ)*n)^2 by positivity)
  linarith

end Q4.Candidate.GridCounts

#print axioms Q4.Candidate.GridCounts.interval_card
#print axioms Q4.Candidate.GridCounts.rectangle_card
#print axioms Q4.Candidate.GridCounts.rectangle_card_normalized
#print axioms Q4.Candidate.GridCounts.strip_card_rows
#print axioms Q4.Candidate.GridCounts.strip_card
#print axioms Q4.Candidate.GridCounts.corners_card
#print axioms Q4.Candidate.GridCounts.strip_forward_card
#print axioms Q4.Candidate.GridCounts.strip_neighbors_card
#print axioms Q4.Candidate.GridCounts.localized_degree
#print axioms Q4.Candidate.GridCounts.strip_edges_card
#print axioms Q4.Candidate.GridCounts.twice_inducedEdges_le_square
#print axioms Q4.Candidate.GridCounts.crossEdges_card_le
#print axioms Q4.Candidate.GridCounts.localized_edges_card
