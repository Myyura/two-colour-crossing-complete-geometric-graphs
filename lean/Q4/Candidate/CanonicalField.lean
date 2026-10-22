import Q4.Candidate.GridLocalization
import Mathlib.Order.Interval.Finset.Fin

/-!
Direct finite canonical-field estimates for the actual rectangular comparison
grid. The key area bound below is proved by finite rank sums, not a presumed
continuous approximation. The canonical colour, its complement and the full energy are connected below;
only the initial stability witness remains external to finite localization.
-/

namespace Q4.Candidate.CanonicalField
open Q4.Candidate.GridCounts Q4.Candidate.GridLocalization

/-- Distinct positive integer ranks have at least the triangular rank sum. -/
theorem positive_ranks_sum (S : Finset Nat) (hpos : ∀ k ∈ S, 1 ≤ k) :
    (S.card : ℝ) * ((S.card : ℝ)+1) ≤ 2 * ∑ k ∈ S, (k : ℝ) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | @insert a S hmax ih =>
    have haS : a ∉ S := by intro ha; exact lt_irrefl a (hmax a ha)
    have ha := hpos a (Finset.mem_insert_self _ _)
    have hpS : ∀ k ∈ S, 1 ≤ k := fun k hk => hpos k (Finset.mem_insert_of_mem hk)
    have hsub : S ⊆ Finset.Icc 1 (a-1) := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨hpS k hk, by have hh := hmax k hk; omega⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hc
    have hca : S.card+1 ≤ a := by omega
    have hcaR : (S.card : ℝ)+1 ≤ (a : ℝ) := by exact_mod_cast hca
    have hi := ih hpS
    rw [Finset.card_insert_of_notMem haS, Finset.sum_insert haS]
    push_cast
    nlinarith

/-- Any finite positive lattice set inside a right triangle obeys the area
upper bound. m,n are grid densities; no aspect-ratio assumption occurs. -/
theorem triangle_lattice_upper (S : Finset (Nat × Nat)) (m n : ℝ)
    (hm : 0 < m) (hn : 0 < n) (t : ℝ)
    (hpos : ∀ p ∈ S, 1 ≤ p.1 ∧ 1 ≤ p.2)
    (htriangle : ∀ p ∈ S, n*p.1 + m*p.2 ≤ m*n*t) :
    (S.card : ℝ) ≤ m*n*t^2/2 := by
  classical
  let R := S.image Prod.fst
  let fiber := fun k : Nat => S.filter (fun p => p.1 = k)
  have hRpos : ∀ k ∈ R, 1 ≤ k := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    exact (hpos p hp).1
  have hfiber (k : Nat) (hk : k ∈ R) :
      m * ((fiber k).card : ℝ) ≤ m*n*t - n*k := by
    obtain ⟨p,hp,hpk⟩ := Finset.mem_image.mp hk
    let L := (fiber k).image Prod.snd
    have hLcard : L.card = (fiber k).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      apply Prod.ext
      · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      · exact hab
    have hU : (1:ℝ) ≤ (m*n*t - n*k)/m := by
      have ht := htriangle p hp
      have hp2 : (1:ℝ) ≤ p.2 := by exact_mod_cast (hpos p hp).2
      rw [hpk] at ht
      apply (le_div_iff₀ hm).mpr
      nlinarith
    have hc := nat_card_le_span L 1 ((m*n*t-n*k)/m) hU (by
      intro l hl
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hl
      have hqS := (Finset.mem_filter.mp hq).1
      have hqk := (Finset.mem_filter.mp hq).2
      refine ⟨by exact_mod_cast (hpos q hqS).2, ?_⟩
      apply (le_div_iff₀ hm).mpr
      have ht := htriangle q hqS
      rw [hqk] at ht
      nlinarith)
    rw [hLcard] at hc
    have hcard : ((fiber k).card : ℝ) ≤ (m*n*t-n*k)/m := by linarith
    simpa only [mul_comm] using (le_div_iff₀ hm).mp hcard
  have hsum := Finset.sum_le_sum hfiber
  have hcardN : S.card = ∑ k ∈ R, (fiber k).card :=
    Finset.card_eq_sum_card_fiberwise (by intro p hp; exact Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  have hcard : (S.card : ℝ) = ∑ k ∈ R, ((fiber k).card : ℝ) := by exact_mod_cast hcardN
  have hsum' : m*(S.card : ℝ) ≤ m*n*t*(R.card : ℝ) - n*(∑ k ∈ R, (k : ℝ)) := by
    simpa only [← Finset.mul_sum, ← hcard, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_comm (R.card : ℝ), mul_assoc] using hsum
  have hrank := positive_ranks_sum R hRpos
  have hr0 : (0:ℝ) ≤ (R.card : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hrank (le_of_lt hn)
  have hsq := mul_nonneg (le_of_lt hn) (sq_nonneg (m*t-(R.card : ℝ)))
  have hscaled : m*(2*(S.card : ℝ)) ≤ m*(m*n*t^2) := by nlinarith
  have hfinal := (mul_le_mul_iff_of_pos_left hm).mp hscaled
  linarith

/-- The manuscript's strict convention: the diagonal tie has colour false. -/
noncomputable def canonical {m n : Nat} (p : Point m n) : Bool :=
  decide (u m p.1 + u n p.2 < 1)

theorem canonical_true_iff {m n : Nat} (p : Point m n) :
    canonical p = true ↔ u m p.1 + u n p.2 < 1 := by simp [canonical]

theorem canonical_false_iff {m n : Nat} (p : Point m n) :
    canonical p = false ↔ 1 ≤ u m p.1 + u n p.2 := by simp [canonical]

theorem canonical_diagonal {m n : Nat} (p : Point m n)
    (hp : u m p.1 + u n p.2 = 1) : canonical p = false := by simp [canonical,hp]

noncomputable def below {m n : Nat} (p : Point m n) : Finset (Point m n) :=
  Finset.univ.filter (fun q => q.1 < p.1 ∧ q.2 < p.2)

noncomputable def above {m n : Nat} (p : Point m n) : Finset (Point m n) :=
  Finset.univ.filter (fun q => p.1 < q.1 ∧ p.2 < q.2)

noncomputable def positiveAbove {m n : Nat} (p : Point m n) : Finset (Point m n) :=
  (above p).filter (fun q => canonical q = true)

noncomputable def negativeBelow {m n : Nat} (p : Point m n) : Finset (Point m n) :=
  (below p).filter (fun q => canonical q = false)

theorem below_card {m n : Nat} (p : Point m n) :
    (below p).card = p.1.val * p.2.val := by
  have he : below p = (Finset.Iio p.1).product (Finset.Iio p.2) := by
    ext q; simp [below]
  rw [he, Finset.product_eq_sprod, Finset.card_product, Fin.card_Iio, Fin.card_Iio]

theorem above_card {m n : Nat} (p : Point m n) :
    (above p).card = (m-1-p.1.val) * (n-1-p.2.val) := by
  have he : above p = (Finset.Ioi p.1).product (Finset.Ioi p.2) := by
    ext q; simp [above]
  rw [he, Finset.product_eq_sprod, Finset.card_product, Fin.card_Ioi, Fin.card_Ioi]

theorem scaled_displacement (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p q : Point m n) :
    (n : ℝ)*((q.1 : ℝ)-(p.1 : ℝ)) + (m : ℝ)*((q.2 : ℝ)-(p.2 : ℝ)) =
      ((m : ℝ)*n)*((u m q.1+u n q.2)-(u m p.1+u n p.2)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold u
  field_simp
  ring

/-- The positive upper-neighbor triangle has at most its continuous area;
this follows from the finite lattice theorem, not an area approximation. -/
theorem positiveAbove_upper (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p : Point m n) :
    ((positiveAbove p).card : ℝ) ≤
      ((m : ℝ)*n)*(1-u m p.1-u n p.2)^2/2 := by
  classical
  let f : Point m n → Nat × Nat := fun q => (q.1.val-p.1.val, q.2.val-p.2.val)
  let S := (positiveAbove p).image f
  have hsteps (q : Point m n) (hq : q ∈ positiveAbove p) :
      p.1.val < q.1.val ∧ p.2.val < q.2.val :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hinj : Set.InjOn f (positiveAbove p) := by
    intro q hq r hr he
    have hq' := hsteps q hq
    have hr' := hsteps r hr
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext <;> apply Fin.ext <;> dsimp [f] at h1 h2 <;> omega
  have hc : S.card = (positiveAbove p).card := Finset.card_image_iff.mpr hinj
  have ht := triangle_lattice_upper S (m : ℝ) (n : ℝ)
    (by exact_mod_cast hm) (by exact_mod_cast hn) (1-u m p.1-u n p.2)
    (by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      have hs := hsteps q hq
      dsimp [f]
      constructor <;> omega)
    (by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      have hs := hsteps q hq
      have hqcan : u m q.1+u n q.2 < 1 := by
        simpa [canonical] using (Finset.mem_filter.mp hq).2
      have hd := scaled_displacement m n hm hn p q
      dsimp [f]
      rw [Nat.cast_sub (le_of_lt hs.1), Nat.cast_sub (le_of_lt hs.2)]
      have hN : (0 : ℝ) ≤ (m : ℝ)*n := by positivity
      nlinarith)
  simpa [hc] using ht

/-- The negative lower-neighbor triangle has the same lattice bound. Negative
includes the diagonal tie, so the closed triangle is the actual relevant region. -/
theorem negativeBelow_upper (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p : Point m n) :
    ((negativeBelow p).card : ℝ) ≤
      ((m : ℝ)*n)*(u m p.1+u n p.2-1)^2/2 := by
  classical
  let f : Point m n → Nat × Nat := fun q => (p.1.val-q.1.val, p.2.val-q.2.val)
  let S := (negativeBelow p).image f
  have hsteps (q : Point m n) (hq : q ∈ negativeBelow p) :
      q.1.val < p.1.val ∧ q.2.val < p.2.val :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hinj : Set.InjOn f (negativeBelow p) := by
    intro q hq r hr he
    have hq' := hsteps q hq
    have hr' := hsteps r hr
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext <;> apply Fin.ext <;> dsimp [f] at h1 h2 <;> omega
  have hc : S.card = (negativeBelow p).card := Finset.card_image_iff.mpr hinj
  have ht := triangle_lattice_upper S (m : ℝ) (n : ℝ)
    (by exact_mod_cast hm) (by exact_mod_cast hn) (u m p.1+u n p.2-1)
    (by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      have hs := hsteps q hq
      dsimp [f]
      constructor <;> omega)
    (by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      have hs := hsteps q hq
      have hqcan : 1 ≤ u m q.1+u n q.2 := by
        have hh := (Finset.mem_filter.mp hq).2
        simp only [canonical, decide_eq_false_iff_not, not_lt] at hh
        exact hh
      have hd := scaled_displacement m n hm hn q p
      dsimp [f]
      rw [Nat.cast_sub (le_of_lt hs.1), Nat.cast_sub (le_of_lt hs.2)]
      have hN : (0 : ℝ) ≤ (m : ℝ)*n := by positivity
      nlinarith)
  simpa [hc] using ht

/-- The actual pair-cost single difference is degree minus twice same-colour
degree; each edge occurrence is counted once. -/
theorem pair_delta_degree {α : Type*} [DecidableEq α] (es : List (α × α))
    (χ : α → Bool) (p : α) (hloop : ∀ e ∈ es, e.1 ≠ e.2) :
    (Q4.monoCount es (Q4.SimultaneousFlip.flipOne χ p) : Int) - (Q4.monoCount es χ : Int) =
      (internalDegree es (fun _ => true) p : Int) -
      2*(internalDegree es (fun q => decide (χ q = χ p)) p : Int) := by
  induction es with
  | nil => simp [Q4.monoCount, internalDegree]
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    have hab := hloop (a,b) (by simp)
    have hi := ih (fun e he => hloop e (by simp [he]))
    by_cases hpa : p = a
    · subst p
      cases hca : χ a <;> cases hcb : χ b <;>
        simp [Q4.monoCount, Q4.SimultaneousFlip.flipOne, internalDegree, incidentSelected,
          hab, Ne.symm hab, hca, hcb] at * <;> omega
    · by_cases hpb : p = b
      · subst p
        cases hca : χ a <;> cases hcb : χ b <;>
          simp [Q4.monoCount, Q4.SimultaneousFlip.flipOne, internalDegree, incidentSelected,
            hab, Ne.symm hab, hca, hcb] at * <;> omega
      · simp [Q4.monoCount, Q4.SimultaneousFlip.flipOne, internalDegree, incidentSelected,
          hpa,hpb,Ne.symm hpa,Ne.symm hpb] at *
        omega

noncomputable def sameVertices {m n : Nat} (χ : Point m n → Bool) (p : Point m n) :
    Finset (Point m n) := Finset.univ.filter (fun q => χ q = χ p)

theorem pure_grid_delta (m n : Nat) (χ : Point m n → Bool) (p : Point m n) :
    delta (gridVertices m n) (gridEdges m n) (fun _ _ => 0) χ p =
      (gridDegree Finset.univ p : ℝ) - 2*(gridDegree (sameVertices χ p) p : ℝ) := by
  have h := pair_delta_degree (gridEdges m n) χ p (gridEdges_loopless m n)
  have hall : membershipMask (Finset.univ : Finset (Point m n)) = (fun _ => true) := by
    funext q; simp [membershipMask]
  have hs : membershipMask (sameVertices χ p) = (fun q => decide (χ q = χ p)) := by
    funext q; simp [membershipMask, sameVertices]
  rw [← hall, ← hs, grid_internalDegree, grid_internalDegree] at h
  have hr : (Q4.monoCount (gridEdges m n) (Q4.SimultaneousFlip.flipOne χ p) : ℝ) -
      (Q4.monoCount (gridEdges m n) χ : ℝ) =
      (gridDegree Finset.univ p : ℝ) - 2*(gridDegree (sameVertices χ p) p : ℝ) := by
    exact_mod_cast h
  have hd := delta_decomposition (gridVertices m n) (gridEdges m n) (fun _ _ => 0) χ p
    (Finset.nodup_toList _) (by simp [gridVertices])
  simpa [unaryDelta, hr] using hd

theorem neighbors_univ {m n : Nat} (p : Point m n) :
    neighborsIn Finset.univ p = below p ∪ above p := by
  ext q
  simp [neighborsIn, below, above, adj, or_comm]

theorem below_above_disjoint {m n : Nat} (p : Point m n) : Disjoint (below p) (above p) := by
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  exact lt_asymm (Finset.mem_filter.mp hq).2.1 (Finset.mem_filter.mp hq').2.1

theorem positive_below (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p q : Point m n) (hp : canonical p = true) (hq : q ∈ below p) : canonical q = true := by
  have hp' : u m p.1+u n p.2 < 1 := by simpa [canonical] using hp
  have hqs := (Finset.mem_filter.mp hq).2
  have hx := u_mono m hm q.1 p.1 (le_of_lt hqs.1)
  have hy := u_mono n hn q.2 p.2 (le_of_lt hqs.2)
  simp only [canonical, decide_eq_true_eq]
  linarith

theorem negative_above (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p q : Point m n) (hp : canonical p = false) (hq : q ∈ above p) : canonical q = false := by
  have hp' : 1 ≤ u m p.1+u n p.2 := by simpa [canonical] using hp
  have hqs := (Finset.mem_filter.mp hq).2
  have hx := u_mono m hm p.1 q.1 (le_of_lt hqs.1)
  have hy := u_mono n hn p.2 q.2 (le_of_lt hqs.2)
  simp only [canonical, decide_eq_false_iff_not, not_lt]
  linarith

theorem same_neighbors_positive (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p : Point m n) (hp : canonical p = true) :
    neighborsIn (sameVertices canonical p) p = below p ∪ positiveAbove p := by
  classical
  ext q
  simp only [neighborsIn, sameVertices, Finset.mem_filter, Finset.mem_univ, true_and, hp]
  constructor
  · rintro ⟨hcan,hf|hb⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,hcan⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hlo | hhi
    · exact ⟨positive_below m n hm hn p q hp hlo, Or.inr (Finset.mem_filter.mp hlo).2⟩
    · exact ⟨(Finset.mem_filter.mp hhi).2, Or.inl (Finset.mem_filter.mp (Finset.mem_filter.mp hhi).1).2⟩

theorem same_neighbors_negative (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p : Point m n) (hp : canonical p = false) :
    neighborsIn (sameVertices canonical p) p = negativeBelow p ∪ above p := by
  classical
  ext q
  simp only [neighborsIn, sameVertices, Finset.mem_filter, Finset.mem_univ, true_and, hp]
  constructor
  · rintro ⟨hcan,hf|hb⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,hcan⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hlo | hhi
    · exact ⟨(Finset.mem_filter.mp hlo).2, Or.inr (Finset.mem_filter.mp (Finset.mem_filter.mp hlo).1).2⟩
    · exact ⟨negative_above m n hm hn p q hp hhi, Or.inl (Finset.mem_filter.mp hhi).2⟩

theorem canonical_delta_positive (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p : Point m n) (hp : canonical p = true) :
    delta (gridVertices m n) (gridEdges m n) (fun _ _ => 0) canonical p =
      ((above p).card : ℝ) - ((below p).card : ℝ) - 2*((positiveAbove p).card : ℝ) := by
  rw [pure_grid_delta]
  change ((neighborsIn Finset.univ p).card : ℝ) -
    2*((neighborsIn (sameVertices canonical p) p).card : ℝ) = _
  rw [neighbors_univ, same_neighbors_positive m n hm hn p hp,
    Finset.card_union_of_disjoint (below_above_disjoint p)]
  have hdis : Disjoint (below p) (positiveAbove p) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (below_above_disjoint p)
  rw [Finset.card_union_of_disjoint hdis]
  push_cast
  ring

theorem canonical_delta_negative (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p : Point m n) (hp : canonical p = false) :
    delta (gridVertices m n) (gridEdges m n) (fun _ _ => 0) canonical p =
      ((below p).card : ℝ) - ((above p).card : ℝ) - 2*((negativeBelow p).card : ℝ) := by
  rw [pure_grid_delta]
  change ((neighborsIn Finset.univ p).card : ℝ) -
    2*((neighborsIn (sameVertices canonical p) p).card : ℝ) = _
  rw [neighbors_univ, same_neighbors_negative m n hm hn p hp,
    Finset.card_union_of_disjoint (below_above_disjoint p)]
  have hdis : Disjoint (negativeBelow p) (above p) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (below_above_disjoint p)
  rw [Finset.card_union_of_disjoint hdis]
  push_cast
  ring

/-- Exact finite rectangle imbalance at a cell center. -/
theorem rectangle_imbalance (m n : Nat) (hm : 0 < m) (hn : 0 < n) (p : Point m n) :
    ((above p).card : ℝ) - ((below p).card : ℝ) =
      ((m : ℝ)*n)*(1-u m p.1-u n p.2) +
      (n : ℝ)*u n p.2 + (m : ℝ)*u m p.1 - ((m : ℝ)+n)/2 := by
  have hm1 : 1 ≤ m := hm
  have hn1 : 1 ≤ n := hn
  have hip : p.1.val ≤ m-1 := by have h := p.1.isLt; omega
  have hjp : p.2.val ≤ n-1 := by have h := p.2.isLt; omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [above_card, below_card]
  simp only [Nat.cast_mul, Nat.cast_sub hip, Nat.cast_sub hjp,
    Nat.cast_sub hm1, Nat.cast_sub hn1, Nat.cast_one, u]
  field_simp
  ring

/-- The stronger one-sided canonical estimate needed by finite localization.
It is derived from actual counts, including all diagonal-tie choices fixed by
`canonical`, and does not use a continuum Riemann-sum premise. -/
theorem canonical_grid_delta_lower (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (p : Point m n) :
    ((m : ℝ)*n)*localProfile (u m p.1) (u n p.2) - ((m : ℝ)+n)/2 ≤
      delta (gridVertices m n) (gridEdges m n) (fun _ _ => 0) canonical p := by
  have hi := rectangle_imbalance m n hm hn p
  have hx0 := u_pos m hm p.1
  have hy0 := u_pos n hn p.2
  have hx1 := u_lt_one m hm p.1
  have hy1 := u_lt_one n hn p.2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  cases hp : canonical p
  · have hneg : 1 ≤ u m p.1+u n p.2 := by simpa [canonical] using hp
    rw [canonical_delta_negative m n hm hn p hp]
    have ht := negativeBelow_upper m n hm hn p
    have ha : |1-u m p.1-u n p.2| = u m p.1+u n p.2-1 := by
      rw [abs_of_nonpos (by linarith)]
      ring
    unfold localProfile
    rw [ha]
    have hxy : (n : ℝ)*u n p.2 + (m : ℝ)*u m p.1 ≤ (m : ℝ)+n := by nlinarith
    nlinarith
  · have hpos : u m p.1+u n p.2 < 1 := by simpa [canonical] using hp
    rw [canonical_delta_positive m n hm hn p hp]
    have ht := positiveAbove_upper m n hm hn p
    unfold localProfile
    rw [abs_of_nonneg (by linarith)]
    have hxy : (0 : ℝ) ≤ (n : ℝ)*u n p.2 + (m : ℝ)*u m p.1 := by positivity
    nlinarith

/-- The half-row/column error is exactly rho*N/2. -/
theorem half_dimensions_eq_rho (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    ((m : ℝ)+n)/2 = rho m n*((m : ℝ)*n)/2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold rho
  field_simp
  ring

/-- Actual real unary costs add only their true one-vertex difference. -/
theorem delta_add_unary (m n : Nat) (cost : Point m n → Bool → ℝ)
    (χ : Point m n → Bool) (p : Point m n) :
    delta (gridVertices m n) (gridEdges m n) cost χ p =
      delta (gridVertices m n) (gridEdges m n) (fun _ _ => 0) χ p + unaryDelta cost χ p := by
  have h1 := delta_decomposition (gridVertices m n) (gridEdges m n) cost χ p
    (Finset.nodup_toList _) (by simp [gridVertices])
  have h0 := delta_decomposition (gridVertices m n) (gridEdges m n) (fun _ _ => 0) χ p
    (Finset.nodup_toList _) (by simp [gridVertices])
  simp only [unaryDelta, sub_self, zero_add] at h0
  linarith

/-- This discharges the `hfield` interface used by GridLocalization for the
positive canonical phase. Only the actual unary difference bound is assumed. -/
theorem canonical_field_with_unaries (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Point m n → Bool → ℝ) (α a : ℝ)
    (hα : 0 ≤ α) (ha : α + rho m n ≤ a)
    (hu : ∀ p, |cost p true-cost p false| ≤ α*((m : ℝ)*n)) (p : Point m n) :
    ((m : ℝ)*n)*localProfile (u m p.1) (u n p.2) - 6*a*((m : ℝ)*n) ≤
      delta (gridVertices m n) (gridEdges m n) cost canonical p := by
  have hg := canonical_grid_delta_lower m n hm hn p
  rw [half_dimensions_eq_rho m n hm hn] at hg
  have huraw := abs_le.mp (hu p)
  have hud : -α*((m : ℝ)*n) ≤ unaryDelta cost canonical p := by
    cases hp : canonical p <;> simp [unaryDelta, hp] <;> linarith
  rw [delta_add_unary]
  have hr := rho_nonneg m n
  have hN : (0 : ℝ) ≤ (m : ℝ)*n := by positivity
  have hbudget : (α+rho m n/2)*((m : ℝ)*n) ≤ 6*a*((m : ℝ)*n) := by
    apply mul_le_mul_of_nonneg_right _ hN
    linarith
  linarith

/-- The two complementary canonical phases, including opposite diagonal ties. -/
noncomputable def phase {m n : Nat} (b : Bool) (p : Point m n) : Bool :=
  if b then !(canonical p) else canonical p

theorem phase_diagonal {m n : Nat} (b : Bool) (p : Point m n)
    (hp : u m p.1 + u n p.2 = 1) : phase b p = b := by
  cases b <;> simp [phase,canonical_diagonal p hp]

theorem phase_sameVertices (m n : Nat) (b : Bool) (p : Point m n) :
    sameVertices (phase b) p = sameVertices canonical p := by
  ext q
  cases b <;> simp [sameVertices, phase]

theorem phase_pure_delta (m n : Nat) (b : Bool) (p : Point m n) :
    delta (gridVertices m n) (gridEdges m n) (fun _ _ => 0) (phase b) p =
      delta (gridVertices m n) (gridEdges m n) (fun _ _ => 0) canonical p := by
  rw [pure_grid_delta, pure_grid_delta, phase_sameVertices]

/-- Both phases satisfy the exact lower-field interface without any
unproved geometric/counting or continuum-approximation assumption. -/
theorem phase_field_with_unaries (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Point m n → Bool → ℝ) (α a : ℝ) (b : Bool)
    (hα : 0 ≤ α) (ha : α + rho m n ≤ a)
    (hu : ∀ p, |cost p true-cost p false| ≤ α*((m : ℝ)*n)) (p : Point m n) :
    ((m : ℝ)*n)*localProfile (u m p.1) (u n p.2) - 6*a*((m : ℝ)*n) ≤
      delta (gridVertices m n) (gridEdges m n) cost (phase b) p := by
  have hg := canonical_grid_delta_lower m n hm hn p
  rw [half_dimensions_eq_rho m n hm hn] at hg
  have huraw := abs_le.mp (hu p)
  have hud : -α*((m : ℝ)*n) ≤ unaryDelta cost (phase b) p := by
    cases hp : phase b p <;> simp [unaryDelta, hp] <;> linarith
  rw [delta_add_unary, phase_pure_delta]
  have hr := rho_nonneg m n
  have hN : (0 : ℝ) ≤ (m : ℝ)*n := by positivity
  have hbudget : (α+rho m n/2)*((m : ℝ)*n) ≤ 6*a*((m : ℝ)*n) := by
    apply mul_le_mul_of_nonneg_right _ hN
    linarith
  linarith

/-- The finite localization claim now needs only the genuine initial
stability witness from the continuous part. All field, degree, strip/corner,
absorption and whole-energy steps have been discharged. -/
theorem minimizer_localization_from_initial_stability (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Point m n → Bool → ℝ) (α a : ℝ)
    (hα : 0 ≤ α) (ha : α + rho m n ≤ a) (ha_small : a ≤ 1/65536)
    (hu : ∀ p, |cost p true-cost p false| ≤ α*((m : ℝ)*n))
    (ψ : Point m n → Bool)
    (hmin : ∀ ζ, energy (gridVertices m n) (gridEdges m n) cost ψ ≤
      energy (gridVertices m n) (gridEdges m n) cost ζ)
    (hstable : ∃ b : Bool, ∃ F : Finset (Point m n),
      ψ = Q4.SimultaneousFlip.flip (phase b) (membershipMask F) ∧
      (F.card : ℝ) ≤ ((m : ℝ)*n)/1048576) :
    ∃ b : Bool, ∃ F : Finset (Point m n),
      ψ = Q4.SimultaneousFlip.flip (phase b) (membershipMask F) ∧
      (F.card : ℝ) ≤ 52*a*((m : ℝ)*n) ∧
      F ⊆ strip m n (220*a) ∪ corners m n (220*a) := by
  obtain ⟨b,F,hψ,hFsmall⟩ := hstable
  let N : ℝ := (m : ℝ)*n
  let μ : ℝ := (F.card : ℝ)/N
  have hN : 0 < N := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  have hμ : 0 ≤ μ := div_nonneg (Nat.cast_nonneg _) (le_of_lt hN)
  have hμsmall : μ ≤ 1/1048576 := by
    apply (div_le_iff₀ hN).mpr
    dsimp [N] at *
    linarith
  have hμdef : (F.card : ℝ) = μ*((m : ℝ)*n) := by
    dsimp [μ,N]
    exact (div_mul_cancel₀ _ (ne_of_gt hN)).symm
  have hrho : rho m n ≤ a := by linarith
  have ha0 : 0 ≤ a := le_trans (rho_nonneg m n) hrho
  have hlocal := minimizer_grid_localization m n hm hn F a μ cost (phase b)
    ha0 ha_small hμ hμsmall hrho hμdef
    (phase_field_with_unaries m n hm hn cost α a b hα ha hu)
    (by simpa only [← hψ] using hmin)
  exact ⟨b,F,hψ,hlocal⟩

/-- A prescribed phase's negative-delta witness and upper estimate require no
initial stability hypothesis. -/
theorem canonical_phase_upper (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Point m n → Bool → ℝ) (α a : ℝ) (b : Bool)
    (hα : 0 ≤ α) (ha : α + rho m n ≤ a) (ha_small : a ≤ 1/65536)
    (hu : ∀ p, |cost p true-cost p false| ≤ α*((m : ℝ)*n)) :
    ((negativeVertices m n cost (phase b)).card : ℝ) ≤ 52*a*((m : ℝ)*n) ∧
    energy (gridVertices m n) (gridEdges m n) cost
      (Q4.SimultaneousFlip.flip (phase b)
        (negativeMask (gridVertices m n) (gridEdges m n) cost (phase b))) ≤
      phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase b) +
      2^32*a^3*((m : ℝ)*n)^2 := by
  have hrho : rho m n ≤ a := by linarith
  exact prescribed_phase_upper m n hm hn a cost (phase b)
    (le_trans (rho_nonneg m n) hrho) ha_small hrho
    (phase_field_with_unaries m n hm hn cost α a b hα ha hu)

/-- The two-sided finite-grid optimum estimate with the manuscript constant
2^32. The outstanding analytic premise is exactly the initial stability
witness; no final localization, canonical field, or energy bound is assumed. -/
theorem finite_grid_optimum_interval (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (cost : Point m n → Bool → ℝ) (α a : ℝ)
    (hα : 0 ≤ α) (ha : α + rho m n ≤ a) (ha_small : a ≤ 1/65536)
    (hu : ∀ p, |cost p true-cost p false| ≤ α*((m : ℝ)*n))
    (ψ : Point m n → Bool)
    (hmin : ∀ ζ, energy (gridVertices m n) (gridEdges m n) cost ψ ≤
      energy (gridVertices m n) (gridEdges m n) cost ζ)
    (hstable : ∃ b : Bool, ∃ F : Finset (Point m n),
      ψ = Q4.SimultaneousFlip.flip (phase b) (membershipMask F) ∧
      (F.card : ℝ) ≤ ((m : ℝ)*n)/1048576) :
    let L := min (phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase false))
      (phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase true))
    L - 2^32*a^3*((m : ℝ)*n)^2 ≤ energy (gridVertices m n) (gridEdges m n) cost ψ ∧
    energy (gridVertices m n) (gridEdges m n) cost ψ ≤ L + 2^32*a^3*((m : ℝ)*n)^2 := by
  dsimp only
  have hrho : rho m n ≤ a := by linarith
  have ha0 : 0 ≤ a := le_trans (rho_nonneg m n) hrho
  constructor
  · obtain ⟨b,F,hψ,_,hF⟩ := minimizer_localization_from_initial_stability m n hm hn
      cost α a hα ha ha_small hu ψ hmin hstable
    have hl := localized_grid_energy_lower m n hm hn F a cost (phase b) ha0 ha_small hrho hF
    rw [← hψ] at hl
    cases b
    · have hh := min_le_left
        (phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase false))
        (phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase true))
      linarith
    · have hh := min_le_right
        (phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase false))
        (phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase true))
      linarith
  · have hup (b : Bool) := (canonical_phase_upper m n hm hn cost α a b hα ha ha_small hu).2
    have hcompare (b : Bool) := hmin (Q4.SimultaneousFlip.flip (phase b)
      (negativeMask (gridVertices m n) (gridEdges m n) cost (phase b)))
    by_cases hL : phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase false) ≤
        phaseEstimate (gridVertices m n) (gridEdges m n) cost (phase true)
    · rw [min_eq_left hL]
      linarith [hup false, hcompare false]
    · rw [min_eq_right (le_of_not_ge hL)]
      linarith [hup true, hcompare true]

end Q4.Candidate.CanonicalField

#print axioms Q4.Candidate.CanonicalField.positive_ranks_sum
#print axioms Q4.Candidate.CanonicalField.canonical_diagonal
#print axioms Q4.Candidate.CanonicalField.phase_diagonal
#print axioms Q4.Candidate.CanonicalField.triangle_lattice_upper

#print axioms Q4.Candidate.CanonicalField.positiveAbove_upper
#print axioms Q4.Candidate.CanonicalField.negativeBelow_upper

#print axioms Q4.Candidate.CanonicalField.canonical_grid_delta_lower
#print axioms Q4.Candidate.CanonicalField.canonical_field_with_unaries

#print axioms Q4.Candidate.CanonicalField.phase_field_with_unaries
#print axioms Q4.Candidate.CanonicalField.minimizer_localization_from_initial_stability
#print axioms Q4.Candidate.CanonicalField.canonical_phase_upper

#print axioms Q4.Candidate.CanonicalField.finite_grid_optimum_interval
