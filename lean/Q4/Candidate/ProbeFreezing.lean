import Q4.JointProbe

/-!
Finite-graph kernel of Proposition 3.2 in `two_colour_crossing_candidate.pdf`.

The objective below is the actual monochromatic count of the entire edge list.
Neighbors are reconstructed from that list; probe--probe edges are retained.
`F` is an explicit support for disagreement with a reference grid coloring.
The grid-localization theorem and the soft-probe cardinality estimate are input
interfaces, not conclusions claimed by this module. No geometry is formalized.

All budgets here are integral counts: if `|F| <= M`, every probe has at most D
neighbors outside the grid, and B >= 2*M+D, at most S soft probes can be frozen
at cost at most 2*B*S. The unrounded real-parameter instantiation appearing in
the manuscript requires a separate ordered-field transfer.
-/

namespace Q4.Candidate.ProbeFreezing

open Q4.SimultaneousFlip (intSum intSum_congr intSum_sub flipOne)
open Q4.JointProbe (spin neighborhood monoCount_single_difference)

variable {α : Type u} [DecidableEq α]

/-- Each real edge occurrence contributes its other endpoint. -/
def neighbors (es : List (α × α)) (p : α) : List α :=
  match es with
  | [] => []
  | (a,b) :: es =>
      if p = a then b :: neighbors es p
      else if p = b then a :: neighbors es p else neighbors es p

def energy (es : List (α × α)) (χ : α → Bool) : Int :=
  (Q4.monoCount es χ : Int)

omit [DecidableEq α] in
theorem energy_eq_totalEnergy (vs : List α) (es : List (α × α)) (χ : α → Bool) :
    energy es χ = Q4.SimultaneousFlip.totalEnergy vs es (fun _ _ => 0) χ := by
  simp [energy, Q4.SimultaneousFlip.totalEnergy,
    Q4.SimultaneousFlip.intSum_zero, Q4.SimultaneousFlip.edgeEnergy_eq_monoCount]

def gridNeighbors (es : List (α × α)) (grid : α → Bool) (p : α) : List α :=
  (neighbors es p).filter grid

def outsideNeighbors (es : List (α × α)) (grid : α → Bool) (p : α) : List α :=
  (neighbors es p).filter (fun v => !(grid v))

def gridField (es : List (α × α)) (grid : α → Bool) (c : α → Bool) (p : α) : Int :=
  intSum (gridNeighbors es grid p) (fun v => spin (c v))

def setColor (χ : α → Bool) (p : α) (b : Bool) (v : α) : Bool :=
  if v = p then b else χ v

/-- Ties may use either response; positive field requires false. -/
def BestResponse (h : Int) (b : Bool) : Prop :=
  (0 < h → b = false) ∧ (h < 0 → b = true)

theorem neighborhood_eq_sum (es : List (α × α)) (χ : α → Bool) (p : α)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    neighborhood es χ p = intSum (neighbors es p) (fun v => spin (χ v)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    have hab := hloop (a,b) (by simp)
    have ih' := ih (fun e he => hloop e (by simp [he]))
    unfold neighborhood at ih' ⊢
    simp only [intSum, neighbors]
    rw [ih']
    by_cases hpa : p = a
    · subst p
      simp [hab, intSum]
    · by_cases hpb : p = b
      · subst p
        simp [hpa, intSum]
      · simp [hpa, hpb]

omit [DecidableEq α] in
theorem sum_partition (xs : List α) (grid : α → Bool) (f : α → Int) :
    intSum xs f = intSum (xs.filter grid) f +
      intSum (xs.filter (fun v => !(grid v))) f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : grid x <;> simp [List.filter, hx, intSum, ih] <;> omega

omit [DecidableEq α] in
theorem spin_sum_bounds (xs : List α) (χ : α → Bool) :
    -(xs.length : Int) ≤ intSum xs (fun v => spin (χ v)) ∧
      intSum xs (fun v => spin (χ v)) ≤ (xs.length : Int) := by
  induction xs with
  | nil => simp [intSum]
  | cons x xs ih =>
    cases hx : χ x <;> simp [intSum, spin, hx, List.length_cons] at * <;> omega

omit [DecidableEq α] in
theorem spin_difference_bounds (xs : List α) (χ c : α → Bool) :
    -2 * ((xs.filter (fun v => decide (χ v ≠ c v))).length : Int) ≤
        intSum xs (fun v => spin (χ v)) - intSum xs (fun v => spin (c v)) ∧
      intSum xs (fun v => spin (χ v)) - intSum xs (fun v => spin (c v)) ≤
        2 * ((xs.filter (fun v => decide (χ v ≠ c v))).length : Int) := by
  induction xs with
  | nil => simp [intSum]
  | cons x xs ih =>
    cases hx : χ x <;> cases hc : c x <;>
      simp [intSum, spin, hx, hc, List.filter, List.length_cons] at * <;> omega

/-- The perturbation is derived from distinct actual neighbors, not assumed. -/
theorem grid_field_error (es : List (α × α)) (grid : α → Bool)
    (χ c : α → Bool) (F : List α) (p : α)
    (hsimple : (neighbors es p).Nodup)
    (hF : ∀ v, grid v = true → χ v ≠ c v → v ∈ F) :
    -2 * (F.length : Int) ≤ gridField es grid χ p - gridField es grid c p ∧
      gridField es grid χ p - gridField es grid c p ≤ 2 * (F.length : Int) := by
  have hb := spin_difference_bounds (gridNeighbors es grid p) χ c
  have hn : ((gridNeighbors es grid p).filter (fun v => decide (χ v ≠ c v))).Nodup :=
    (hsimple.filter grid).filter _
  have hsub : (gridNeighbors es grid p).filter (fun v => decide (χ v ≠ c v)) ⊆ F := by
    intro v hv
    have h := List.mem_filter.mp hv
    have hg := List.mem_filter.mp h.1
    exact hF v hg.2 (by simpa using h.2)
  have hlen := hn.length_le_of_subset hsub
  unfold gridField
  omega

/-- Valid for every coloring with the same grid, including after other probes flip. -/
theorem full_field_error (es : List (α × α)) (grid : α → Bool)
    (χ c ψ : α → Bool) (F : List α) (p : α) (D B : Int)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hsimple : (neighbors es p).Nodup)
    (hF : ∀ v, grid v = true → χ v ≠ c v → v ∈ F)
    (hfixed : ∀ v, grid v = true → ψ v = χ v)
    (hdeg : ((outsideNeighbors es grid p).length : Int) ≤ D)
    (hbudget : 2 * (F.length : Int) + D ≤ B) :
    -B ≤ neighborhood es ψ p - gridField es grid c p ∧
      neighborhood es ψ p - gridField es grid c p ≤ B := by
  have hFp : ∀ v, grid v = true → ψ v ≠ c v → v ∈ F := by
    intro v hv hne
    apply hF v hv
    simpa [hfixed v hv] using hne
  have hg := grid_field_error es grid ψ c F p hsimple hFp
  have ho := spin_sum_bounds (outsideNeighbors es grid p) ψ
  rw [neighborhood_eq_sum es ψ p hloop,
    sum_partition (neighbors es p) grid (fun v => spin (ψ v))]
  change -B ≤ gridField es grid ψ p +
      intSum (outsideNeighbors es grid p) (fun v => spin (ψ v)) - gridField es grid c p ∧
    gridField es grid ψ p +
      intSum (outsideNeighbors es grid p) (fun v => spin (ψ v)) - gridField es grid c p ≤ B
  omega

theorem setColor_eq_self (χ : α → Bool) (p : α) (b : Bool) (h : χ p = b) :
    setColor χ p b = χ := by
  funext v
  by_cases hv : v = p <;> simp [setColor, hv, h]

theorem setColor_eq_flip (χ : α → Bool) (p : α) (b : Bool) (h : χ p ≠ b) :
    setColor χ p b = flipOne χ p := by
  funext v
  by_cases hv : v = p
  · subst v
    cases hc : χ p <;> cases b <;> simp [setColor, flipOne, hc] at *
  · simp [setColor, flipOne, hv]

/-- Exact whole-graph accounting imported from the audited pair expansion. -/
theorem energy_single_flip (es : List (α × α)) (χ : α → Bool) (p : α)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    energy es (flipOne χ p) - energy es χ = -spin (χ p) * neighborhood es χ p :=
  monoCount_single_difference es χ p hloop

/-- The sum of neighbor spins really is color-1 cost minus color-0 cost. -/
theorem field_eq_cost_difference (es : List (α × α)) (χ : α → Bool) (p : α)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    energy es (setColor χ p true) - energy es (setColor χ p false) = neighborhood es χ p := by
  have h := energy_single_flip es χ p hloop
  cases hc : χ p
  · rw [setColor_eq_self χ p false hc,
      setColor_eq_flip χ p true (by simp [hc])]
    simpa [hc, spin] using h
  · rw [setColor_eq_self χ p true hc,
      setColor_eq_flip χ p false (by simp [hc])]
    simp [hc, spin] at h
    omega

theorem setColor_cost_bound (es : List (α × α)) (χ : α → Bool) (p : α)
    (b : Bool) (C : Int) (_hC : 0 ≤ C)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hfield : -C ≤ neighborhood es χ p ∧ neighborhood es χ p ≤ C) :
    energy es (setColor χ p b) - energy es χ ≤ C := by
  by_cases heq : χ p = b
  · rw [setColor_eq_self χ p b heq]
    omega
  · rw [setColor_eq_flip χ p b heq, energy_single_flip es χ p hloop]
    cases χ p <;> simp [spin] <;> omega

/-- A nonsoft probe is already correct at every global minimum. -/
theorem hard_probe_already_correct (es : List (α × α)) (χ : α → Bool)
    (p : α) (h B : Int) (b : Bool) (hB : 0 ≤ B)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hmin : ∀ ψ, energy es χ ≤ energy es ψ)
    (hresponse : BestResponse h b)
    (herr : -B ≤ neighborhood es χ p - h ∧ neighborhood es χ p - h ≤ B)
    (hhard : ¬ (-B ≤ h ∧ h ≤ B)) : χ p = b := by
  have hlocal := hmin (flipOne χ p)
  have hdelta := energy_single_flip es χ p hloop
  rcases hresponse with ⟨hpos,hneg⟩
  by_cases hh : 0 < h
  · have hb := hpos hh
    subst b
    cases hc : χ p
    · rfl
    · simp [spin, hc] at hdelta
      omega
  · have hh' : h < 0 := by omega
    have hb := hneg hh'
    subst b
    cases hc : χ p
    · simp [spin, hc] at hdelta
      omega
    · rfl

/-- Left-to-right recoloring, with the current colors used at each step. -/
def freeze (χ : α → Bool) (ps : List α) (y : α → Bool) : α → Bool :=
  match ps with
  | [] => χ
  | p :: ps => freeze (setColor χ p (y p)) ps y

theorem freeze_outside (ps : List α) (χ y : α → Bool) (v : α)
    (hv : v ∉ ps) : freeze χ ps y v = χ v := by
  induction ps generalizing χ with
  | nil => rfl
  | cons p ps ih =>
    have hne : v ≠ p := by intro h; subst v; exact hv (by simp)
    have hn : v ∉ ps := by intro h; exact hv (by simp [h])
    rw [freeze, ih _ hn]
    simp [setColor, hne]

theorem freeze_mem (ps : List α) (χ y : α → Bool) (v : α)
    (hv : v ∈ ps) : freeze χ ps y v = y v := by
  induction ps generalizing χ with
  | nil => simp at hv
  | cons p ps ih =>
    by_cases htail : v ∈ ps
    · exact ih _ htail
    · have hhead : v = p := by simpa [htail] using hv
      subst v
      rw [freeze, freeze_outside ps _ y p htail]
      simp [setColor]

theorem setColor_preserves_grid (χ ψ : α → Bool) (grid : α → Bool)
    (p : α) (b : Bool) (hp : grid p = false)
    (hfixed : ∀ v, grid v = true → ψ v = χ v) :
    ∀ v, grid v = true → setColor ψ p b v = χ v := by
  intro v hv
  have hne : v ≠ p := by intro heq; subst v; simp [hp] at hv
  simp [setColor, hne, hfixed v hv]

theorem freeze_preserves_grid (ps : List α) (χ y : α → Bool)
    (grid : α → Bool) (hps : ∀ p, p ∈ ps → grid p = false) :
    ∀ v, grid v = true → freeze χ ps y v = χ v := by
  intro v hv
  apply freeze_outside
  intro hmem
  have hf := hps v hmem
  simp [hf] at hv

/-- Telescoping charges are evaluated at the current coloring of all probes. -/
theorem freeze_cost_bound (es : List (α × α)) (ps : List α)
    (χ ψ y : α → Bool) (grid : α → Bool) (C : Int)
    (hfixed : ∀ v, grid v = true → ψ v = χ v)
    (hps : ∀ p, p ∈ ps → grid p = false)
    (hstep : ∀ ζ, (∀ v, grid v = true → ζ v = χ v) →
      ∀ p, p ∈ ps → energy es (setColor ζ p (y p)) - energy es ζ ≤ C) :
    energy es (freeze ψ ps y) - energy es ψ ≤ C * (ps.length : Int) := by
  induction ps generalizing ψ with
  | nil => simp [freeze]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hnext := setColor_preserves_grid χ ψ grid p (y p) hp hfixed
    have htail := ih (setColor ψ p (y p)) hnext
      (fun q hq => hps q (by simp [hq]))
      (fun ζ hz q hq => hstep ζ hz q (by simp [hq]))
    have hhead := hstep ψ hfixed p (by simp)
    simp only [freeze, List.length_cons, Int.natCast_add, Int.natCast_one, Int.mul_add,
      Int.mul_one]
    omega

def softProbes (T : List α) (h : α → Int) (B : Int) : List α :=
  T.filter (fun p => decide (-B ≤ h p ∧ h p ≤ B))

def maxOutsideDegree (es : List (α × α)) (grid : α → Bool) : List α → Nat
  | [] => 0
  | p :: ps => max (outsideNeighbors es grid p).length (maxOutsideDegree es grid ps)

theorem outsideDegree_le_max (es : List (α × α)) (grid : α → Bool)
    (T : List α) (p : α) (hp : p ∈ T) :
    (outsideNeighbors es grid p).length ≤ maxOutsideDegree es grid T := by
  induction T with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.mem_cons] at hp
    rcases hp with hp | hp
    · subst p
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hp) (Nat.le_max_right _ _)

omit [DecidableEq α] in
theorem filter_length_mono (xs : List α) (p q : α → Bool)
    (h : ∀ v, v ∈ xs → p v = true → q v = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hi := ih (fun v hv => h v (by simp [hv]))
    have hx := h x (by simp)
    cases hp : p x <;> cases hq : q x <;>
      simp [List.filter, hp, hq] at * <;> omega

/-- Every soft probe has a uniform cost bound after any preceding changes.
    The outside-neighbor list contains all probe--probe edges. -/
theorem soft_probe_step (es : List (α × α)) (grid : α → Bool)
    (χ c ψ : α → Bool) (F : List α) (p : α) (D B : Int) (b : Bool)
    (hB : 0 ≤ B)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hsimple : (neighbors es p).Nodup)
    (hF : ∀ v, grid v = true → χ v ≠ c v → v ∈ F)
    (hfixed : ∀ v, grid v = true → ψ v = χ v)
    (hdeg : ((outsideNeighbors es grid p).length : Int) ≤ D)
    (hbudget : 2 * (F.length : Int) + D ≤ B)
    (hsoft : -B ≤ gridField es grid c p ∧ gridField es grid c p ≤ B) :
    energy es (setColor ψ p b) - energy es ψ ≤ 2 * B := by
  have herr := full_field_error es grid χ c ψ F p D B hloop hsimple hF hfixed hdeg hbudget
  exact setColor_cost_bound es ψ p b (2 * B) (by omega) hloop (by omega)

/-- Complete finite-graph freezing theorem.

`hF` is the supplied grid-localization interface and `hsoftCount` is the
supplied soft-count interface. Everything between them and the final total
energy bound is proved from the actual simple graph, including hard-probe
optimality, sequential recoloring, all probe--probe interactions, and preservation
of the original grid. The graph's geometric origin is not asserted here.
-/
theorem probe_freezing (es : List (α × α)) (grid : α → Bool)
    (χ c y : α → Bool) (F T : List α) (D B S : Int)
    (hB : 0 ≤ B)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hsimple : ∀ p, p ∈ T → (neighbors es p).Nodup)
    (hdisjoint : ∀ p, p ∈ T → grid p = false)
    (hF : ∀ v, grid v = true → χ v ≠ c v → v ∈ F)
    (hdeg : ∀ p, p ∈ T → ((outsideNeighbors es grid p).length : Int) ≤ D)
    (hbudget : 2 * (F.length : Int) + D ≤ B)
    (hresponse : ∀ p, p ∈ T → BestResponse (gridField es grid c p) (y p))
    (hmin : ∀ ψ, energy es χ ≤ energy es ψ)
    (hsoftCount : ((softProbes T (gridField es grid c) B).length : Int) ≤ S) :
    ∃ ψ, (∀ p, p ∈ T → ψ p = y p) ∧
      (∀ v, v ∉ T → ψ v = χ v) ∧
      (∀ v, grid v = true → ψ v = χ v) ∧
      0 ≤ energy es ψ - energy es χ ∧
      energy es ψ - energy es χ ≤ 2 * B * S := by
  let ps := softProbes T (gridField es grid c) B
  have hsub : ∀ p, p ∈ ps → p ∈ T := by
    intro p hp
    exact (List.mem_filter.mp hp).1
  have hps : ∀ p, p ∈ ps → grid p = false :=
    fun p hp => hdisjoint p (hsub p hp)
  have hhard : ∀ p, p ∈ T → p ∉ ps → χ p = y p := by
    intro p hp hn
    apply hard_probe_already_correct es χ p (gridField es grid c p) B (y p)
      hB hloop hmin (hresponse p hp)
      (full_field_error es grid χ c χ F p D B hloop (hsimple p hp) hF
        (fun _ _ => rfl) (hdeg p hp) hbudget)
    intro hs
    apply hn
    simp [ps, softProbes, hp, hs]
  have hcost := freeze_cost_bound es ps χ χ y grid (2 * B) (fun _ _ => rfl) hps
    (by
      intro ζ hz p hp
      have hm := List.mem_filter.mp hp
      have hsoft : -B ≤ gridField es grid c p ∧ gridField es grid c p ≤ B := by
        simpa using hm.2
      exact soft_probe_step es grid χ c ζ F p D B (y p) hB hloop
        (hsimple p hm.1) hF hz (hdeg p hm.1) hbudget hsoft)
  refine ⟨freeze χ ps y, ?_, ?_, freeze_preserves_grid ps χ y grid hps, ?_, ?_⟩
  · intro p hp
    by_cases hm : p ∈ ps
    · exact freeze_mem ps χ y p hm
    · rw [freeze_outside ps χ y p hm]
      exact hhard p hp hm
  · intro v hv
    apply freeze_outside
    intro hm
    exact hv (hsub v hm)
  · have h := hmin (freeze χ ps y)
    omega
  · have hmul : 2 * B * (ps.length : Int) ≤ 2 * B * S :=
      Int.mul_le_mul_of_nonneg_left hsoftCount (by omega)
    exact Int.le_trans hcost hmul

def canonicalResponse (h : Int) : Bool := decide (h < 0)

theorem canonicalResponse_best (h : Int) : BestResponse h (canonicalResponse h) := by
  constructor <;> intro hh <;> simp [canonicalResponse] <;> omega

/-- This includes the manuscript's complemented tie convention in phase minus. -/
theorem complement_best_response (h : Int) (b : Bool) (hb : BestResponse h b) :
    BestResponse (-h) (!b) := by
  rcases hb with ⟨hpos, hneg⟩
  constructor
  · intro hh
    have h := hneg (by omega)
    simp [h]
  · intro hh
    have h := hpos (by omega)
    simp [h]

omit [DecidableEq α] in
/-- Any frozen feasible domain containing the constructed coloring has the same
    gap bound. In particular, it may allow either canonical phase. -/
theorem frozen_optimum_gap (es : List (α × α)) (χ ψ η : α → Bool)
    (frozen : (α → Bool) → Prop) (C : Int)
    (hmin : ∀ ζ, energy es χ ≤ energy es ζ)
    (hwitness : frozen ψ) (hcost : energy es ψ - energy es χ ≤ C)
    (_hη : frozen η)
    (hηmin : ∀ ζ, frozen ζ → energy es η ≤ energy es ζ) :
    0 ≤ energy es η - energy es χ ∧ energy es η - energy es χ ≤ C := by
  have hlo := hmin η
  have hup := hηmin ψ hwitness
  omega

end Q4.Candidate.ProbeFreezing

#print axioms Q4.Candidate.ProbeFreezing.energy_single_flip
#print axioms Q4.Candidate.ProbeFreezing.field_eq_cost_difference
#print axioms Q4.Candidate.ProbeFreezing.grid_field_error
#print axioms Q4.Candidate.ProbeFreezing.full_field_error
#print axioms Q4.Candidate.ProbeFreezing.hard_probe_already_correct
#print axioms Q4.Candidate.ProbeFreezing.freeze_cost_bound
#print axioms Q4.Candidate.ProbeFreezing.soft_probe_step
#print axioms Q4.Candidate.ProbeFreezing.probe_freezing
#print axioms Q4.Candidate.ProbeFreezing.canonicalResponse_best
#print axioms Q4.Candidate.ProbeFreezing.complement_best_response
#print axioms Q4.Candidate.ProbeFreezing.frozen_optimum_gap
