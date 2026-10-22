import Std

/-!
Counting facts for a finite list of interacting pairs.  For Q4 the elements of
`α` are complete-geometric-graph edges and the list must contain each proper
crossing pair exactly once.  This file does not construct or verify that list.

The identities hold even for lists with duplicates or loops; each occurrence is
counted once.  Consequently geometric correctness is a separate obligation.
-/

namespace Q4

variable {α : Type u}

/-- Number of listed pairs whose two members have equal Boolean colors. -/
def monoCount : List (α × α) → (α → Bool) → Nat
  | [], _ => 0
  | (a, b) :: ps, χ => (if χ a = χ b then 1 else 0) + monoCount ps χ

/-- Number of listed pairs whose two members have different Boolean colors. -/
def cutCount : List (α × α) → (α → Bool) → Nat
  | [], _ => 0
  | (a, b) :: ps, χ => (if χ a = χ b then 0 else 1) + cutCount ps χ

/-- Every listed interaction contributes to exactly one of the two counts. -/
theorem mono_add_cut (ps : List (α × α)) (χ : α → Bool) :
    monoCount ps χ + cutCount ps χ = ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    by_cases h : χ a = χ b <;>
      simp only [monoCount, cutCount, h, ite_true, ite_false, List.length_cons] <;>
      omega

theorem mono_eq_total_sub_cut (ps : List (α × α)) (χ : α → Bool) :
    monoCount ps χ = ps.length - cutCount ps χ := by
  have h := mono_add_cut ps χ
  omega

/-- Pairwise preferences reverse exactly, including ties. -/
theorem mono_le_iff_cut_le (ps : List (α × α)) (χ ψ : α → Bool) :
    monoCount ps χ ≤ monoCount ps ψ ↔ cutCount ps ψ ≤ cutCount ps χ := by
  have hχ := mono_add_cut ps χ
  have hψ := mono_add_cut ps ψ
  omega

theorem mono_lt_iff_cut_lt (ps : List (α × α)) (χ ψ : α → Bool) :
    monoCount ps χ < monoCount ps ψ ↔ cutCount ps ψ < cutCount ps χ := by
  have hχ := mono_add_cut ps χ
  have hψ := mono_add_cut ps ψ
  omega

/-- Global optimality, with any shared feasibility predicate (e.g. pinned colors). -/
def IsMonoMinimizer (ps : List (α × α))
    (feasible : (α → Bool) → Prop) (χ : α → Bool) : Prop :=
  feasible χ ∧ ∀ ψ, feasible ψ → monoCount ps χ ≤ monoCount ps ψ

def IsCutMaximizer (ps : List (α × α))
    (feasible : (α → Bool) → Prop) (χ : α → Bool) : Prop :=
  feasible χ ∧ ∀ ψ, feasible ψ → cutCount ps ψ ≤ cutCount ps χ

/-- A coloring is a monochromatic minimum iff it is a cut maximum. -/
theorem mono_minimizer_iff_cut_maximizer (ps : List (α × α))
    (feasible : (α → Bool) → Prop) (χ : α → Bool) :
    IsMonoMinimizer ps feasible χ ↔ IsCutMaximizer ps feasible χ := by
  constructor
  · rintro ⟨hχ, hmin⟩
    exact ⟨hχ, fun ψ hψ => (mono_le_iff_cut_le ps χ ψ).mp (hmin ψ hψ)⟩
  · rintro ⟨hχ, hmax⟩
    exact ⟨hχ, fun ψ hψ => (mono_le_iff_cut_le ps χ ψ).mpr (hmax ψ hψ)⟩

/-- Decision thresholds also correspond, with natural subtraction truncated at zero. -/
theorem mono_threshold_iff_cut_threshold (ps : List (α × α))
    (χ : α → Bool) (t : Nat) :
    monoCount ps χ ≤ t ↔ ps.length - t ≤ cutCount ps χ := by
  have h := mono_add_cut ps χ
  omega

end Q4
