import Q4.SimultaneousFlip
import Q4.Candidate.GridCounts
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Finite-energy layer for candidate Theorem 3.1. Unary costs are arbitrary reals;
the pair cost is the actual monochromatic count of an explicit finite edge list.
Geometric/grid counting and the initial continuum stability estimate are
separate interfaces. No localization conclusion is assumed in this layer.
-/

namespace Q4.Candidate.GridLocalization
open Q4.SimultaneousFlip
variable {α : Type u} {β : Type v}

def realSum : List α → (α → ℝ) → ℝ
  | [], _ => 0
  | a :: as, f => f a + realSum as f

theorem realSum_zero (xs : List α) : realSum xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [realSum, ih]

theorem realSum_add (xs : List α) (f g : α → ℝ) :
    realSum xs (fun a => f a + g a) = realSum xs f + realSum xs g := by
  induction xs with
  | nil => simp [realSum]
  | cons a xs ih => simp only [realSum, ih]; ring

theorem realSum_sub (xs : List α) (f g : α → ℝ) :
    realSum xs (fun a => f a - g a) = realSum xs f - realSum xs g := by
  induction xs with
  | nil => simp [realSum]
  | cons a xs ih => simp only [realSum, ih]; ring

theorem realSum_congr (xs : List α) (f g : α → ℝ)
    (h : ∀ a, a ∈ xs → f a = g a) : realSum xs f = realSum xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [realSum]
    rw [h a (by simp), ih (fun a ha => h a (by simp [ha]))]

theorem realSum_le (xs : List α) (f g : α → ℝ)
    (h : ∀ a, a ∈ xs → f a ≤ g a) : realSum xs f ≤ realSum xs g := by
  induction xs with
  | nil => exact le_rfl
  | cons a xs ih =>
    exact add_le_add (h a (by simp)) (ih (fun a ha => h a (by simp [ha])))

theorem cast_intSum (xs : List α) (f : α → Int) :
    (intSum xs f : ℝ) = realSum xs (fun a => (f a : ℝ)) := by
  induction xs with
  | nil => simp [intSum, realSum]
  | cons a xs ih => simp [intSum, realSum, ih]

variable [DecidableEq α]

theorem realSum_point (xs : List α) (a : α) (w : ℝ)
    (hn : xs.Nodup) (ha : a ∈ xs) :
    realSum xs (fun x => if x = a then w else 0) = w := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hba : b = a
    · subst b
      simp only [realSum, ite_true]
      have hz : realSum xs (fun x => if x = a then w else 0) = 0 := by
        calc
          _ = realSum xs (fun _ => 0) := by
            apply realSum_congr
            intro x hx
            have hxa : x ≠ a := by intro h; subst x; exact hn'.1 hx
            simp [hxa]
          _ = 0 := realSum_zero xs
      rw [hz, add_zero]
    · simp only [realSum, hba, ite_false, zero_add]
      exact ih hn'.2 (by simpa [hba, Ne.symm hba] using ha)

def energy (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ : α → Bool) : ℝ :=
  realSum vs (fun v => u v (χ v)) + (Q4.monoCount es χ : ℝ)

def delta (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ : α → Bool) (v : α) : ℝ :=
  energy vs es u (flipOne χ v) - energy vs es u χ

def unaryDelta (u : α → Bool → ℝ) (χ : α → Bool) (v : α) : ℝ :=
  u v (!(χ v)) - u v (χ v)

/-- Actual single-flip energy includes its unary and all listed pair costs. -/
theorem delta_decomposition (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ : α → Bool) (v : α)
    (hn : vs.Nodup) (hv : v ∈ vs) :
    delta vs es u χ v = unaryDelta u χ v +
      ((Q4.monoCount es (flipOne χ v) : ℝ) - (Q4.monoCount es χ : ℝ)) := by
  have hu : realSum vs (fun x => u x (flipOne χ v x)) -
      realSum vs (fun x => u x (χ x)) = unaryDelta u χ v := by
    rw [← realSum_sub]
    have heq : realSum vs (fun x => u x (flipOne χ v x) - u x (χ x)) =
        realSum vs (fun x => if x = v then unaryDelta u χ v else 0) := by
      apply realSum_congr
      intro x _
      by_cases hx : x = v
      · subst x; simp [flipOne, unaryDelta]
      · simp [flipOne, hx]
    rw [heq, realSum_point vs v _ hn hv]
  unfold delta energy
  linarith

/-- Formula (3.7), with arbitrary real unary costs and the actual full pair
objective. The integer correction is 0 off F×F and ±2 on each internal edge. -/
theorem energy_flip_identity (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ mask : α → Bool)
    (hn : vs.Nodup)
    (hends : ∀ e, e ∈ es → e.1 ∈ vs ∧ e.2 ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    energy vs es u (flip χ mask) - energy vs es u χ =
      realSum vs (fun v => if mask v then delta vs es u χ v else 0) +
      (intSum es (correction χ mask) : ℝ) := by
  have hi := totalEnergy_flip_identity vs es (fun _ _ => 0) χ mask hn hends hloop
  simp only [totalEnergy, intSum_zero, zero_add, singleDelta,
    edgeEnergy_eq_monoCount] at hi
  have hc := congrArg (fun z : Int => (z : ℝ)) hi
  push_cast at hc
  rw [cast_intSum] at hc
  have hselected : realSum vs (fun v =>
      (selected (mask v) ((Q4.monoCount es (flipOne χ v) : Int) -
        (Q4.monoCount es χ : Int)) : ℝ)) =
      realSum vs (fun v => if mask v then
        (Q4.monoCount es (flipOne χ v) : ℝ) - (Q4.monoCount es χ : ℝ) else 0) := by
    apply realSum_congr
    intro v _
    cases mask v <;> simp [selected]
  rw [hselected] at hc
  have hu : realSum vs (fun v => u v (flip χ mask v)) -
      realSum vs (fun v => u v (χ v)) =
      realSum vs (fun v => if mask v then unaryDelta u χ v else 0) := by
    rw [← realSum_sub]
    apply realSum_congr
    intro v _
    cases hv : mask v <;> simp [Q4.SimultaneousFlip.flip, unaryDelta, hv]
  have hd : realSum vs (fun v => if mask v then delta vs es u χ v else 0) =
      realSum vs (fun v => if mask v then unaryDelta u χ v else 0) +
      realSum vs (fun v => if mask v then
        (Q4.monoCount es (flipOne χ v) : ℝ) - (Q4.monoCount es χ : ℝ) else 0) := by
    rw [← realSum_add]
    apply realSum_congr
    intro v hv
    rw [delta_decomposition vs es u χ v hn hv]
    cases mask v <;> simp
  unfold energy
  linarith

def internalEdges (es : List (α × α)) (mask : α → Bool) : List (α × α) :=
  es.filter (fun e => mask e.1 && mask e.2)

omit [DecidableEq α] in
/-- Every actual internal edge has correction ±2, with no missing edge class. -/
theorem correction_bounds (es : List (α × α)) (χ mask : α → Bool) :
    -2 * ((internalEdges es mask).length : Int) ≤ intSum es (correction χ mask) ∧
    intSum es (correction χ mask) ≤ 2 * ((internalEdges es mask).length : Int) := by
  induction es with
  | nil => simp [internalEdges, intSum]
  | cons e es ih =>
    cases hm1 : mask e.1 <;> cases hm2 : mask e.2 <;>
      cases hc1 : χ e.1 <;> cases hc2 : χ e.2 <;>
      simp [internalEdges, intSum, correction, same, hm1, hm2, hc1, hc2] at * <;> omega

def linearFloor (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ : α → Bool) : ℝ :=
  realSum vs (fun v => min 0 (delta vs es u χ v))

def phaseEstimate (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ : α → Bool) : ℝ :=
  energy vs es u χ + linearFloor vs es u χ

noncomputable def negativeMask (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ : α → Bool) (v : α) : Bool :=
  decide (delta vs es u χ v < 0)

theorem linear_floor_lower (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ mask : α → Bool) :
    linearFloor vs es u χ ≤ realSum vs (fun v => if mask v then delta vs es u χ v else 0) := by
  apply realSum_le
  intro v _
  cases mask v
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem negative_mask_attains_linear (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ : α → Bool) :
    realSum vs (fun v => if negativeMask vs es u χ v then delta vs es u χ v else 0) =
      linearFloor vs es u χ := by
  apply realSum_congr
  intro v _
  unfold negativeMask
  by_cases hd : delta vs es u χ v < 0
  · simp [hd, min_eq_right (le_of_lt hd)]
  · simp [hd, min_eq_left (le_of_not_gt hd)]

/-- Actual lower estimate for any flip set, not only minimisers. -/
theorem energy_lower_by_internal_edges (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ mask : α → Bool)
    (hn : vs.Nodup)
    (hends : ∀ e, e ∈ es → e.1 ∈ vs ∧ e.2 ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    phaseEstimate vs es u χ - 2 * ((internalEdges es mask).length : ℝ) ≤
      energy vs es u (Q4.SimultaneousFlip.flip χ mask) := by
  have h := energy_flip_identity vs es u χ mask hn hends hloop
  have hl := linear_floor_lower vs es u χ mask
  have hc : -2 * ((internalEdges es mask).length : ℝ) ≤ (intSum es (correction χ mask) : ℝ) := by
    exact_mod_cast (correction_bounds es χ mask).1
  unfold phaseEstimate
  linarith

/-- Flipping all negative one-vertex differences attains the independent
linear minimum, with an actual pair-error at most twice its induced edge count. -/
theorem negative_mask_upper (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ : α → Bool)
    (hn : vs.Nodup)
    (hends : ∀ e, e ∈ es → e.1 ∈ vs ∧ e.2 ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    energy vs es u (Q4.SimultaneousFlip.flip χ (negativeMask vs es u χ)) ≤
      phaseEstimate vs es u χ +
      2 * ((internalEdges es (negativeMask vs es u χ)).length : ℝ) := by
  have h := energy_flip_identity vs es u χ (negativeMask vs es u χ) hn hends hloop
  rw [negative_mask_attains_linear] at h
  have hc : (intSum es (correction χ (negativeMask vs es u χ)) : ℝ) ≤
      2 * ((internalEdges es (negativeMask vs es u χ)).length : ℝ) := by
    exact_mod_cast (correction_bounds es χ (negativeMask vs es u χ)).2
  unfold phaseEstimate
  linarith

def incidentSelected (v : α) (mask : α → Bool) (e : α × α) : Bool :=
  (decide (v = e.1) && mask e.2) || (decide (v = e.2) && mask e.1)

def internalDegree (es : List (α × α)) (mask : α → Bool) (v : α) : Nat :=
  (es.filter (incidentSelected v mask)).length

/-- The two actual single-edge flip differences are bounded by two precisely
when the other endpoint belongs to F. -/
theorem edge_flipback_bound (χ mask : α → Bool) (v : α) (e : α × α)
    (hloop : e.1 ≠ e.2) (hm : mask v = true) :
    same (flipOne (Q4.SimultaneousFlip.flip χ mask) v e.1)
        (flipOne (Q4.SimultaneousFlip.flip χ mask) v e.2) -
      same (Q4.SimultaneousFlip.flip χ mask e.1) (Q4.SimultaneousFlip.flip χ mask e.2) +
      (same (flipOne χ v e.1) (flipOne χ v e.2) - same (χ e.1) (χ e.2)) ≤
      if incidentSelected v mask e then 2 else 0 := by
  rcases e with ⟨a,b⟩
  dsimp only at hloop ⊢
  by_cases hva : v = a
  · subst v
    cases hca : χ a <;> cases hcb : χ b <;> cases hmb : mask b <;>
      simp [flipOne, Q4.SimultaneousFlip.flip, incidentSelected, same,
        hloop, Ne.symm hloop, hm, hca, hcb, hmb]
  · by_cases hvb : v = b
    · subst v
      cases hca : χ a <;> cases hcb : χ b <;> cases hma : mask a <;>
        simp [flipOne, Q4.SimultaneousFlip.flip, incidentSelected, same,
          hloop, Ne.symm hloop, hm, hca, hcb, hma]
    · simp [flipOne, incidentSelected, hva, hvb, Ne.symm hva, Ne.symm hvb]

theorem pair_flipback_bound (es : List (α × α)) (χ mask : α → Bool) (v : α)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) (hm : mask v = true) :
    ((Q4.monoCount es (flipOne (Q4.SimultaneousFlip.flip χ mask) v) : Int) -
      (Q4.monoCount es (Q4.SimultaneousFlip.flip χ mask) : Int)) +
      ((Q4.monoCount es (flipOne χ v) : Int) - (Q4.monoCount es χ : Int)) ≤
      2 * (internalDegree es mask v : Int) := by
  induction es with
  | nil => simp [Q4.monoCount, internalDegree]
  | cons e es ih =>
    have he := edge_flipback_bound χ mask v e (hloop e (by simp)) hm
    have hi := ih (fun e he => hloop e (by simp [he]))
    have hs : ∀ a b : Bool, (if a = b then (1 : Int) else 0) = same a b := by
      intro a b; rfl
    simp only [Q4.monoCount, Nat.cast_add] at *
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hs] at *
    cases hh : incidentSelected v mask e <;>
      simp [internalDegree, List.filter, hh] at * <;> omega

/-- Local optimality yields (3.5)'s crucial bound before any geometric estimate:
a canonical single-flip difference is at most twice the actual F-degree. -/
theorem minimizer_flipback_bound (vs : List α) (es : List (α × α))
    (u : α → Bool → ℝ) (χ mask : α → Bool) (v : α)
    (hn : vs.Nodup) (hv : v ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) (hm : mask v = true)
    (hmin : ∀ ψ, energy vs es u (Q4.SimultaneousFlip.flip χ mask) ≤ energy vs es u ψ) :
    delta vs es u χ v ≤ 2 * (internalDegree es mask v : ℝ) := by
  have hcurr := hmin (flipOne (Q4.SimultaneousFlip.flip χ mask) v)
  have hd₁ := delta_decomposition vs es u χ v hn hv
  have hd₂ := delta_decomposition vs es u (Q4.SimultaneousFlip.flip χ mask) v hn hv
  have hu : unaryDelta u (Q4.SimultaneousFlip.flip χ mask) v = - unaryDelta u χ v := by
    simp [unaryDelta, Q4.SimultaneousFlip.flip, hm]
  have hp : ((Q4.monoCount es (flipOne (Q4.SimultaneousFlip.flip χ mask) v) : ℝ) -
      (Q4.monoCount es (Q4.SimultaneousFlip.flip χ mask) : ℝ)) +
      ((Q4.monoCount es (flipOne χ v) : ℝ) - (Q4.monoCount es χ : ℝ)) ≤
      2 * (internalDegree es mask v : ℝ) := by
    exact_mod_cast pair_flipback_bound es χ mask v hloop hm
  rw [hu] at hd₂
  unfold delta at *
  linarith

/-! The scalar localization bootstrap, before its finite grid instantiation. -/

def localProfile (x y : ℝ) : ℝ := |1-x-y| * (1-|1-x-y|)

/-- The two low-field regions are derived, not supplied as a localization
hypothesis. This is the elementary observation after manuscript (3.3). -/
theorem low_profile_regions (x y z : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hp : localProfile x y ≤ z) :
    |x+y-1| ≤ 2*z ∨ x+y ≤ 2*z ∨ 2-2*z ≤ x+y := by
  have habs : |1-x-y| = |x+y-1| := by
    have he : 1-x-y = -(x+y-1) := by ring
    rw [he, abs_neg]
  let t := |x+y-1|
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht1 : t ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hp' : t*(1-t) ≤ z := by simpa [localProfile, habs, t] using hp
  have hregion : t ≤ 2*z ∨ 1-t ≤ 2*z := by
    by_cases ht : t ≤ 1/2
    · left; nlinarith
    · right; nlinarith
  rcases hregion with hs | hc
  · exact Or.inl hs
  · right
    by_cases hsum : 0 ≤ x+y-1
    · have ht : t = x+y-1 := abs_of_nonneg hsum
      right; linarith
    · have ht : t = -(x+y-1) := abs_of_nonpos (le_of_not_ge hsum)
      left; linarith

/-- The improved strip degree becomes a thinner strip. -/
theorem refined_strip_profile (x y a w : ℝ)
    (hw : w ≤ 1/2) (ht : |x+y-1| ≤ w)
    (hp : localProfile x y ≤ 6*a + 52*w^2) :
    |x+y-1| ≤ 12*a + 104*w^2 := by
  have habs : |1-x-y| = |x+y-1| := by
    have he : 1-x-y = -(x+y-1) := by ring
    rw [he, abs_neg]
  have ht0 := abs_nonneg (x+y-1)
  unfold localProfile at hp
  rw [habs] at hp
  nlinarith

/-- The manuscript's absorption step from an initial small disagreement
fraction. Its hypotheses precede the conclusion μ≤52a. -/
theorem absorb_disagreement (a μ : ℝ)
    (ha : 0 ≤ a) (ha_small : a ≤ 1/65536)
    (hμ : 0 ≤ μ) (hμ_small : μ ≤ 1/1048576)
    (hcount : μ ≤ 25*a + 216*(4*μ+12*a)^2) : μ ≤ 52*a := by
  have hs : (4*μ+12*a)^2 ≤ 32*μ^2 + 288*a^2 := by
    nlinarith [sq_nonneg (4*μ-12*a)]
  have ha2 : 62208*a^2 ≤ a := by nlinarith
  have hμ2 : 6912*μ^2 ≤ μ/2 := by nlinarith
  nlinarith

open GridCounts

noncomputable def gridDegree {m n : Nat} (F : Finset (Point m n)) (p : Point m n) : Nat := by
  classical
  exact (F.filter (adj p)).card

/-- Actual finite-grid first localization, derived from the local optimality
inequality and a small initial disagreement fraction. -/
theorem initial_grid_localization (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (F : Finset (Point m n)) (a μ : ℝ)
    (hμdef : (F.card : ℝ) = μ*((m : ℝ)*n))
    (hlocal : ∀ p, p ∈ F →
      ((m : ℝ)*n) * localProfile (u m p.1) (u n p.2) ≤
      6*a*((m : ℝ)*n) + 2*(gridDegree F p : ℝ)) :
    F ⊆ strip m n (4*μ+12*a) ∪ corners m n (4*μ+12*a) := by
  classical
  intro p hp
  have hdeg : (gridDegree F p : ℝ) ≤ (F.card : ℝ) := by
    dsimp [gridDegree]
    exact_mod_cast Finset.card_filter_le F (adj p)
  have hN : (0 : ℝ) < (m : ℝ)*n := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  have hprof : localProfile (u m p.1) (u n p.2) ≤ 6*a+2*μ := by
    have hh := hlocal p hp
    rw [hμdef] at hdeg
    nlinarith
  have hreg := low_profile_regions (u m p.1) (u n p.2) (6*a+2*μ)
    ⟨le_of_lt (u_pos m hm p.1), le_of_lt (u_lt_one m hm p.1)⟩
    ⟨le_of_lt (u_pos n hn p.2), le_of_lt (u_lt_one n hn p.2)⟩ hprof
  rcases hreg with hs | hc | hc
  · apply Finset.mem_union_left
    simp only [strip, Finset.mem_filter, Finset.mem_univ, true_and]
    linarith
  · apply Finset.mem_union_right
    simp only [corners, Finset.mem_filter, Finset.mem_univ, true_and]
    left; linarith
  · apply Finset.mem_union_right
    simp only [corners, Finset.mem_filter, Finset.mem_univ, true_and]
    right; linarith

theorem gridDegree_mono {m n : Nat} (F G : Finset (Point m n)) (p : Point m n)
    (hFG : F ⊆ G) : gridDegree F p ≤ gridDegree G p := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ hFG)

/-- Refine only the strip part; corner vertices never receive the false
O(w²N) strip-degree assumption. -/
theorem refined_grid_localization (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (F : Finset (Point m n)) (a μ : ℝ)
    (hμdef : (F.card : ℝ) = μ*((m : ℝ)*n))
    (hw : 4*μ+12*a ≤ 1/2)
    (hlocal : ∀ p, p ∈ F →
      ((m : ℝ)*n) * localProfile (u m p.1) (u n p.2) ≤
      6*a*((m : ℝ)*n) + 2*(gridDegree F p : ℝ))
    (hdegree : ∀ p, p ∈ strip m n (4*μ+12*a) →
      (gridDegree (strip m n (4*μ+12*a) ∪ corners m n (4*μ+12*a)) p : ℝ) ≤
      26*(4*μ+12*a)^2*((m : ℝ)*n)) :
    F ⊆ strip m n (12*a+104*(4*μ+12*a)^2) ∪ corners m n (4*μ+12*a) := by
  classical
  have hinit := initial_grid_localization m n hm hn F a μ hμdef hlocal
  have hN : (0 : ℝ) < (m : ℝ)*n := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  intro p hp
  rcases Finset.mem_union.mp (hinit hp) with hs | hc
  · have hdmono : (gridDegree F p : ℝ) ≤
        (gridDegree (strip m n (4*μ+12*a) ∪ corners m n (4*μ+12*a)) p : ℝ) := by
      exact_mod_cast gridDegree_mono F _ p hinit
    have hd := hdegree p hs
    have hpfield := hlocal p hp
    have hprof : localProfile (u m p.1) (u n p.2) ≤ 6*a+52*(4*μ+12*a)^2 := by
      nlinarith
    have ht := refined_strip_profile (u m p.1) (u n p.2) a (4*μ+12*a) hw
      (Finset.mem_filter.mp hs).2 hprof
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  · exact Finset.mem_union_right _ hc

/-- Actual finite row/corner counts imply the scalar bootstrap inequality.
The degree estimate is supplied separately for the actual comparison graph. -/
theorem disagreement_count_bootstrap (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (F : Finset (Point m n)) (a μ : ℝ)
    (ha : 0 ≤ a) (hμ : 0 ≤ μ) (hrho : rho m n ≤ a)
    (hμdef : (F.card : ℝ) = μ*((m : ℝ)*n))
    (hw : 4*μ+12*a ≤ 1/2)
    (hlocal : ∀ p, p ∈ F →
      ((m : ℝ)*n) * localProfile (u m p.1) (u n p.2) ≤
      6*a*((m : ℝ)*n) + 2*(gridDegree F p : ℝ))
    (hdegree : ∀ p, p ∈ strip m n (4*μ+12*a) →
      (gridDegree (strip m n (4*μ+12*a) ∪ corners m n (4*μ+12*a)) p : ℝ) ≤
      26*(4*μ+12*a)^2*((m : ℝ)*n)) :
    μ ≤ 25*a + 216*(4*μ+12*a)^2 := by
  classical
  let w := 4*μ+12*a
  let r := 12*a+104*w^2
  have hwρ : rho m n ≤ w := by dsimp [w]; linarith
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hsub : F ⊆ strip m n r ∪ corners m n w :=
    refined_grid_localization m n hm hn F a μ hμdef hw hlocal hdegree
  have hcardN := le_trans (Finset.card_le_card hsub)
    (Finset.card_union_le (strip m n r) (corners m n w))
  have hcard : (F.card : ℝ) ≤ ((strip m n r).card : ℝ) + ((corners m n w).card : ℝ) := by
    exact_mod_cast hcardN
  have hstrip := strip_card_rows m n hn r hr0
  have hcorner := corners_card m n hm hn w hwρ
  have hnrho := one_le_mul_rho_right m n hn
  have hma : (m : ℝ) ≤ a*((m : ℝ)*n) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hna : 1 ≤ (n : ℝ)*a := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hna (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith
  have hN : (0 : ℝ) < (m : ℝ)*n := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  rw [hμdef] at hcard
  dsimp [r] at hstrip
  have hscaled : μ*((m : ℝ)*n) ≤ (25*a+216*w^2)*((m : ℝ)*n) := by nlinarith
  have hresult : μ ≤ 25*a+216*w^2 := (mul_le_mul_iff_of_pos_right hN).mp hscaled
  exact hresult

/-- Final finite localization from local optimality, the initial stability
bound, and the actual strip-degree estimate. The conclusion is derived;
no localized final support or small final cardinality is an assumption. -/
theorem finite_grid_localization_from_degree (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (F : Finset (Point m n)) (a μ : ℝ)
    (ha : 0 ≤ a) (ha_small : a ≤ 1/65536)
    (hμ : 0 ≤ μ) (hμ_small : μ ≤ 1/1048576) (hrho : rho m n ≤ a)
    (hμdef : (F.card : ℝ) = μ*((m : ℝ)*n))
    (hlocal : ∀ p, p ∈ F →
      ((m : ℝ)*n) * localProfile (u m p.1) (u n p.2) ≤
      6*a*((m : ℝ)*n) + 2*(gridDegree F p : ℝ))
    (hdegree : ∀ p, p ∈ strip m n (4*μ+12*a) →
      (gridDegree (strip m n (4*μ+12*a) ∪ corners m n (4*μ+12*a)) p : ℝ) ≤
      26*(4*μ+12*a)^2*((m : ℝ)*n)) :
    (F.card : ℝ) ≤ 52*a*((m : ℝ)*n) ∧
      F ⊆ strip m n (220*a) ∪ corners m n (220*a) := by
  have hw : 4*μ+12*a ≤ 1/2 := by linarith
  have hc := disagreement_count_bootstrap m n hm hn F a μ ha hμ hrho hμdef hw hlocal hdegree
  have hbound := absorb_disagreement a μ ha ha_small hμ hμ_small hc
  constructor
  · rw [hμdef]
    exact mul_le_mul_of_nonneg_right hbound (by positivity)
  · have hinit := initial_grid_localization m n hm hn F a μ hμdef hlocal
    have hww : 4*μ+12*a ≤ 220*a := by linarith
    intro p hp
    rcases Finset.mem_union.mp (hinit hp) with hs | hc
    · apply Finset.mem_union_left
      have hh := (Finset.mem_filter.mp hs).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans hh hww⟩
    · apply Finset.mem_union_right
      rcases (Finset.mem_filter.mp hc).2 with hlo | hhi
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (le_trans hlo hww)⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by linarith)⟩

/-- Finite-grid localization with the 26-degree estimate now discharged from
actual comparison-grid counting. The remaining external inputs are the initial
stability estimate and the canonical local-field inequality, not localization. -/
theorem finite_grid_localization (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (F : Finset (Point m n)) (a μ : ℝ)
    (ha : 0 ≤ a) (ha_small : a ≤ 1/65536)
    (hμ : 0 ≤ μ) (hμ_small : μ ≤ 1/1048576) (hrho : rho m n ≤ a)
    (hμdef : (F.card : ℝ) = μ*((m : ℝ)*n))
    (hlocal : ∀ p, p ∈ F →
      ((m : ℝ)*n) * localProfile (u m p.1) (u n p.2) ≤
      6*a*((m : ℝ)*n) + 2*(gridDegree F p : ℝ)) :
    (F.card : ℝ) ≤ 52*a*((m : ℝ)*n) ∧
      F ⊆ strip m n (220*a) ∪ corners m n (220*a) := by
  apply finite_grid_localization_from_degree m n hm hn F a μ ha ha_small hμ hμ_small hrho hμdef hlocal
  intro p hp
  have hw : rho m n ≤ 4*μ+12*a := by linarith
  have hd := localized_degree m n hm hn (4*μ+12*a) hw
    (strip m n (4*μ+12*a) ∪ corners m n (4*μ+12*a)) (fun _ h => h) p hp
  simpa only [gridDegree, neighborsIn] using hd

/-- The pair list used by the energy is the actual strict-comparison graph,
with every undirected comparable pair represented once. -/
noncomputable def gridEdges (m n : Nat) : List (Point m n × Point m n) :=
  (orientedEdges m n).toList

noncomputable def gridVertices (m n : Nat) : List (Point m n) :=
  Finset.univ.toList

noncomputable def membershipMask {m n : Nat} (F : Finset (Point m n))
    (p : Point m n) : Bool := decide (p ∈ F)

theorem gridEdges_loopless (m n : Nat) :
    ∀ e, e ∈ gridEdges m n → e.1 ≠ e.2 := by
  intro e he heq
  have h := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
  rw [heq] at h
  exact (lt_irrefl _ h.1)

theorem gridEdges_endpoints (m n : Nat) :
    ∀ e, e ∈ gridEdges m n → e.1 ∈ gridVertices m n ∧ e.2 ∈ gridVertices m n := by
  intro e _
  simp [gridVertices]

/-- Exact finite bijection between incident selected edge occurrences and
selected adjacent grid vertices. No graph-degree estimate is assumed. -/
theorem grid_internalDegree (m n : Nat) (F : Finset (Point m n)) (p : Point m n) :
    internalDegree (gridEdges m n) (membershipMask F) p = gridDegree F p := by
  classical
  let A := (orientedEdges m n).filter (fun e => incidentSelected p (membershipMask F) e)
  let B := neighborsIn F p
  have hA (e : Point m n × Point m n) :
      e ∈ A ↔ (e.1.1 < e.2.1 ∧ e.1.2 < e.2.2) ∧
        ((p = e.1 ∧ e.2 ∈ F) ∨ (p = e.2 ∧ e.1 ∈ F)) := by
    simp [A, orientedEdges, incidentSelected, membershipMask]
  have hB (q : Point m n) : q ∈ B ↔ q ∈ F ∧ adj p q := by
    simp [B, neighborsIn]
  let other : Point m n × Point m n → Point m n := fun e => if e.1 = p then e.2 else e.1
  let orient : Point m n → Point m n × Point m n :=
    fun q => if p.1 < q.1 then (p,q) else (q,p)
  have hi (e : Point m n × Point m n) (he : e ∈ A) : other e ∈ B := by
    rcases (hA e).mp he with ⟨hlt, hinc⟩
    apply (hB _).mpr
    rcases hinc with ⟨hp,hF⟩ | ⟨hp,hF⟩
    · have heq : e.1 = p := hp.symm
      simp only [other, heq, ↓reduceIte]
      exact ⟨hF, Or.inl (hp ▸ hlt)⟩
    · have hne : e.1 ≠ p := by intro h; rw [h, ← hp] at hlt; exact lt_irrefl _ hlt.1
      simp only [other, hne, ↓reduceIte]
      exact ⟨hF, Or.inr (hp ▸ hlt)⟩
  have hj (q : Point m n) (hq : q ∈ B) : orient q ∈ A := by
    rcases (hB q).mp hq with ⟨hF,hpq⟩
    rcases hpq with hlt | hgt
    · have hh : p.1 < q.1 := hlt.1
      apply (hA _).mpr
      simp [orient, hh, hlt.2, hF]
    · have hh : ¬p.1 < q.1 := not_lt_of_gt hgt.1
      apply (hA _).mpr
      simp [orient, hh, hgt.1, hgt.2, hF]
  have hleft (e : Point m n × Point m n) (he : e ∈ A) : orient (other e) = e := by
    rcases (hA e).mp he with ⟨hlt,hinc⟩
    rcases hinc with ⟨hp,_⟩ | ⟨hp,_⟩
    · have heq : e.1 = p := hp.symm
      have hh : p.1 < e.2.1 := hp ▸ hlt.1
      simp only [other, ite_eq_left heq, orient, ite_eq_left hh]
      exact Prod.ext hp rfl
    · have hne : e.1 ≠ p := by intro h; rw [h, ← hp] at hlt; exact lt_irrefl _ hlt.1
      have hh : ¬p.1 < e.1.1 := not_lt_of_gt (hp ▸ hlt.1)
      simp only [other, ite_eq_right hne, orient, ite_eq_right hh]
      exact Prod.ext rfl hp
  have hright (q : Point m n) (hq : q ∈ B) : other (orient q) = q := by
    rcases (hB q).mp hq with ⟨_, hpq⟩
    rcases hpq with hlt | hgt
    · simp [orient, other, hlt.1]
    · have hh : ¬p.1 < q.1 := not_lt_of_gt hgt.1
      have hne : q ≠ p := by intro h; subst q; exact lt_irrefl _ hgt.1
      simp [orient, other, hh, hne]
  have hcard : A.card = B.card :=
    Finset.card_bij' (fun e _ => other e) (fun q _ => orient q) hi hj hleft hright
  have hnd := (Finset.nodup_toList (orientedEdges m n)).filter (incidentSelected p (membershipMask F))
  unfold internalDegree gridEdges
  rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter, Finset.toList_toFinset]
  exact hcard

/-- List pair counting and finite-set induced edge counting agree exactly. -/
theorem grid_internalEdges (m n : Nat) (F : Finset (Point m n)) :
    (internalEdges (gridEdges m n) (membershipMask F)).length = (inducedEdges F).card := by
  classical
  have hnd := (Finset.nodup_toList (orientedEdges m n)).filter
    (fun e => membershipMask F e.1 && membershipMask F e.2)
  unfold internalEdges gridEdges
  rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter, Finset.toList_toFinset]
  congr 1
  ext e
  simp [inducedEdges, membershipMask]

/-- An actual full minimiser of the finite grid energy localizes. The only
non-finite input here is the initial small-disagreement witness; `hfield` is
the explicit canonical local-field estimate still to be established. -/
theorem minimizer_grid_localization (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (F : Finset (Point m n)) (a μ : ℝ)
    (cost : Point m n → Bool → ℝ) (χ : Point m n → Bool)
    (ha : 0 ≤ a) (ha_small : a ≤ 1/65536)
    (hμ : 0 ≤ μ) (hμ_small : μ ≤ 1/1048576) (hrho : rho m n ≤ a)
    (hμdef : (F.card : ℝ) = μ*((m : ℝ)*n))
    (hfield : ∀ p, ((m : ℝ)*n) * localProfile (u m p.1) (u n p.2) -
      6*a*((m : ℝ)*n) ≤ delta (gridVertices m n) (gridEdges m n) cost χ p)
    (hmin : ∀ ψ, energy (gridVertices m n) (gridEdges m n) cost
      (Q4.SimultaneousFlip.flip χ (membershipMask F)) ≤
      energy (gridVertices m n) (gridEdges m n) cost ψ) :
    (F.card : ℝ) ≤ 52*a*((m : ℝ)*n) ∧
      F ⊆ strip m n (220*a) ∪ corners m n (220*a) := by
  apply finite_grid_localization m n hm hn F a μ ha ha_small hμ hμ_small hrho hμdef
  intro p hp
  have hd := minimizer_flipback_bound (gridVertices m n) (gridEdges m n) cost χ
    (membershipMask F) p (Finset.nodup_toList _) (by simp [gridVertices])
    (gridEdges_loopless m n) (by simp [membershipMask, hp]) hmin
  rw [grid_internalDegree] at hd
  have hf := hfield p
  linarith

/-- The localized lower-energy estimate uses the actual 83*w^3*N^2 edge
count. It applies to arbitrary localized colourings and arbitrary real unaries. -/
theorem localized_grid_energy_lower (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (F : Finset (Point m n)) (a : ℝ)
    (cost : Point m n → Bool → ℝ) (χ : Point m n → Bool)
    (ha : 0 ≤ a) (ha_small : a ≤ 1/65536) (hrho : rho m n ≤ a)
    (hF : F ⊆ strip m n (220*a) ∪ corners m n (220*a)) :
    phaseEstimate (gridVertices m n) (gridEdges m n) cost χ -
      2^32*a^3*((m : ℝ)*n)^2 ≤
    energy (gridVertices m n) (gridEdges m n) cost
      (Q4.SimultaneousFlip.flip χ (membershipMask F)) := by
  have hl := energy_lower_by_internal_edges (gridVertices m n) (gridEdges m n)
    cost χ (membershipMask F) (Finset.nodup_toList _)
    (gridEdges_endpoints m n) (gridEdges_loopless m n)
  rw [grid_internalEdges] at hl
  have he := localized_edges_card m n hm hn (220*a) (by linarith) (by linarith) F hF
  have hnz : 0 ≤ a^3*((m : ℝ)*n)^2 := by positivity
  nlinarith

noncomputable def negativeVertices (m n : Nat) (cost : Point m n → Bool → ℝ)
    (χ : Point m n → Bool) : Finset (Point m n) :=
  Finset.univ.filter (fun p => delta (gridVertices m n) (gridEdges m n) cost χ p < 0)

theorem negative_vertices_mask (m n : Nat) (cost : Point m n → Bool → ℝ)
    (χ : Point m n → Bool) :
    membershipMask (negativeVertices m n cost χ) =
      negativeMask (gridVertices m n) (gridEdges m n) cost χ := by
  funext p
  simp [membershipMask, negativeVertices, negativeMask]

/-- The full negative-delta set is itself localized, with no global minimum
assumption and no pre-assumed support restriction. -/
theorem negative_vertices_support (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (a : ℝ) (cost : Point m n → Bool → ℝ) (χ : Point m n → Bool)
    (hfield : ∀ p, ((m : ℝ)*n) * localProfile (u m p.1) (u n p.2) -
      6*a*((m : ℝ)*n) ≤ delta (gridVertices m n) (gridEdges m n) cost χ p) :
    negativeVertices m n cost χ ⊆ strip m n (12*a) ∪ corners m n (12*a) := by
  intro p hp
  have hd := (Finset.mem_filter.mp hp).2
  have hf := hfield p
  have hN : (0 : ℝ) < (m : ℝ)*n := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  have hprof : localProfile (u m p.1) (u n p.2) ≤ 6*a := by nlinarith
  have hreg := low_profile_regions (u m p.1) (u n p.2) (6*a)
    ⟨le_of_lt (u_pos m hm p.1), le_of_lt (u_lt_one m hm p.1)⟩
    ⟨le_of_lt (u_pos n hn p.2), le_of_lt (u_lt_one n hn p.2)⟩ hprof
  rcases hreg with hs | hc | hc
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (by linarith)⟩
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by linarith)⟩

/-- The actual negative-delta colouring gives both the 52*a*N size bound and
the prescribed-phase upper estimate of Theorem 3.1. -/
theorem prescribed_phase_upper (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (a : ℝ) (cost : Point m n → Bool → ℝ) (χ : Point m n → Bool)
    (ha : 0 ≤ a) (ha_small : a ≤ 1/65536) (hrho : rho m n ≤ a)
    (hfield : ∀ p, ((m : ℝ)*n) * localProfile (u m p.1) (u n p.2) -
      6*a*((m : ℝ)*n) ≤ delta (gridVertices m n) (gridEdges m n) cost χ p) :
    ((negativeVertices m n cost χ).card : ℝ) ≤ 52*a*((m : ℝ)*n) ∧
    energy (gridVertices m n) (gridEdges m n) cost
      (Q4.SimultaneousFlip.flip χ (negativeMask (gridVertices m n) (gridEdges m n) cost χ)) ≤
      phaseEstimate (gridVertices m n) (gridEdges m n) cost χ +
      2^32*a^3*((m : ℝ)*n)^2 := by
  have hF := negative_vertices_support m n hm hn a cost χ hfield
  have hr : rho m n ≤ 12*a := by linarith
  constructor
  · have hcN := le_trans (Finset.card_le_card hF)
      (Finset.card_union_le (strip m n (12*a)) (corners m n (12*a)))
    have hc : ((negativeVertices m n cost χ).card : ℝ) ≤
        ((strip m n (12*a)).card : ℝ) + ((corners m n (12*a)).card : ℝ) := by exact_mod_cast hcN
    have hs := strip_card m n hm hn (12*a) hr
    have ht := corners_card m n hm hn (12*a) hr
    have ha2 : 1152*a^2 ≤ 16*a := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_right ha2 (show (0:ℝ) ≤ (m:ℝ)*n by positivity)
    nlinarith
  · have hu := negative_mask_upper (gridVertices m n) (gridEdges m n) cost χ
      (Finset.nodup_toList _) (gridEdges_endpoints m n) (gridEdges_loopless m n)
    rw [← negative_vertices_mask, grid_internalEdges] at hu
    have he := localized_edges_card m n hm hn (12*a) hr (by linarith)
      (negativeVertices m n cost χ) hF
    have hnz : 0 ≤ a^3*((m : ℝ)*n)^2 := by positivity
    rw [← negative_vertices_mask]
    nlinarith

#print axioms Q4.Candidate.GridLocalization.energy_flip_identity
#print axioms Q4.Candidate.GridLocalization.energy_lower_by_internal_edges
#print axioms Q4.Candidate.GridLocalization.negative_mask_upper
#print axioms Q4.Candidate.GridLocalization.minimizer_flipback_bound
#print axioms Q4.Candidate.GridLocalization.absorb_disagreement
#print axioms Q4.Candidate.GridLocalization.initial_grid_localization
#print axioms Q4.Candidate.GridLocalization.grid_internalDegree
#print axioms Q4.Candidate.GridLocalization.finite_grid_localization_from_degree
#print axioms Q4.Candidate.GridLocalization.finite_grid_localization
#print axioms Q4.Candidate.GridLocalization.minimizer_grid_localization
#print axioms Q4.Candidate.GridLocalization.localized_grid_energy_lower
#print axioms Q4.Candidate.GridLocalization.prescribed_phase_upper

end Q4.Candidate.GridLocalization
