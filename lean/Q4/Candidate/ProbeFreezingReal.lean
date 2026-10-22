import Q4.Candidate.ProbeFreezing
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Unrounded real-parameter form of the finite-graph freezing theorem.

The localization support `F`, its bound `52*a*N`, and the soft-field counting
bound are explicit input interfaces. The actual maximal outside degree is used
internally, so no rounding error changes the manuscript's stated coefficient.
This file does not prove finite-grid localization or geometric realizability.
-/

namespace Q4.Candidate.ProbeFreezing

variable {α : Type u} [DecidableEq α]

theorem maxOutsideDegree_real_bound (es : List (α × α)) (grid : α → Bool)
    (T : List α) (d : ℝ) (hd : 0 ≤ d)
    (hdeg : ∀ p, p ∈ T → ((outsideNeighbors es grid p).length : ℝ) ≤ d) :
    (maxOutsideDegree es grid T : ℝ) ≤ d := by
  induction T with
  | nil => simpa [maxOutsideDegree] using hd
  | cons p ps ih =>
    have hp := hdeg p (by simp)
    have hi := ih (fun q hq => hdeg q (by simp [hq]))
    simp only [maxOutsideDegree, Nat.cast_max]
    exact max_le hp hi

noncomputable def realSoftProbes (T : List α) (h : α → Int) (B : ℝ) : List α :=
  T.filter (fun p => decide (|(h p : ℝ)| ≤ B))

omit [DecidableEq α] in
theorem softProbes_le_realSoftProbes (T : List α) (h : α → Int)
    (B : Int) (R : ℝ) (hBR : (B : ℝ) ≤ R) :
    (softProbes T h B).length ≤ (realSoftProbes T h R).length := by
  apply filter_length_mono
  intro p _ hp
  have hb : -B ≤ h p ∧ h p ≤ B := by simpa using hp
  have hl : -(B : ℝ) ≤ (h p : ℝ) := by exact_mod_cast hb.1
  have hu : (h p : ℝ) ≤ (B : ℝ) := by exact_mod_cast hb.2
  have ha : |(h p : ℝ)| ≤ (B : ℝ) := abs_le.mpr ⟨hl, hu⟩
  simpa using le_trans ha hBR

/-- Proposition 3.2's exact numerical freezing loss, conditional only on its
    localization and soft-count interfaces. `b = 104*a + beta`.

    The energy is the complete edge-list objective. There is no independence
    hypothesis on probes; all their mutual interactions are included.
-/
theorem probe_freezing_real (es : List (α × α)) (grid : α → Bool)
    (χ c y : α → Bool) (F T : List α) (N : Nat)
    (a beta rho Q : ℝ) (ha : 0 ≤ a) (hbeta : 0 ≤ beta)
    (_hrho : 0 ≤ rho) (_hQ : 0 ≤ Q)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hsimple : ∀ p, p ∈ T → (neighbors es p).Nodup)
    (hdisjoint : ∀ p, p ∈ T → grid p = false)
    (hF : ∀ v, grid v = true → χ v ≠ c v → v ∈ F)
    (hFsize : (F.length : ℝ) ≤ 52 * a * N)
    (hdeg : ∀ p, p ∈ T → ((outsideNeighbors es grid p).length : ℝ) ≤ beta * N)
    (hresponse : ∀ p, p ∈ T → BestResponse (gridField es grid c p) (y p))
    (hmin : ∀ ψ, energy es χ ≤ energy es ψ)
    (hsoftCount : ((realSoftProbes T (gridField es grid c)
      ((104 * a + beta) * N)).length : ℝ) ≤ Q * (104 * a + beta + rho) * N) :
    ∃ ψ, (∀ p, p ∈ T → ψ p = y p) ∧
      (∀ v, v ∉ T → ψ v = χ v) ∧
      (∀ v, grid v = true → ψ v = χ v) ∧
      0 ≤ energy es ψ - energy es χ ∧
      ((energy es ψ - energy es χ : Int) : ℝ) ≤
        2 * Q * (104 * a + beta + rho) * (104 * a + beta) * (N : ℝ)^2 := by
  let D : Int := maxOutsideDegree es grid T
  let B : Int := 2 * (F.length : Int) + D
  let S : Int := (softProbes T (gridField es grid c) B).length
  have hD0 : 0 ≤ D := Int.natCast_nonneg _
  have hB0 : 0 ≤ B := by dsimp [B]; omega
  have hD : (D : ℝ) ≤ beta * N := by
    exact_mod_cast maxOutsideDegree_real_bound es grid T (beta * N)
      (by positivity) hdeg
  have hB : (B : ℝ) ≤ (104 * a + beta) * N := by
    dsimp [B]
    push_cast
    nlinarith [hFsize, hD]
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := by dsimp [S]; positivity
  have hS : (S : ℝ) ≤ Q * (104 * a + beta + rho) * N := by
    have hc := softProbes_le_realSoftProbes T (gridField es grid c) B
      ((104 * a + beta) * N) hB
    have hcr : ((softProbes T (gridField es grid c) B).length : ℝ) ≤
        ((realSoftProbes T (gridField es grid c) ((104 * a + beta) * N)).length : ℝ) :=
      by exact_mod_cast hc
    exact le_trans hcr hsoftCount
  obtain ⟨ψ, hy, hout, hgrid, hlo, hcost⟩ := probe_freezing es grid χ c y F T D B S hB0
    hloop hsimple hdisjoint hF
    (fun p hp => by
      dsimp [D]
      exact_mod_cast outsideDegree_le_max es grid T p hp)
    (by rfl) hresponse hmin (by rfl)
  refine ⟨ψ, hy, hout, hgrid, hlo, ?_⟩
  have hcostR : ((energy es ψ - energy es χ : Int) : ℝ) ≤ 2 * (B : ℝ) * (S : ℝ) :=
    by exact_mod_cast hcost
  have hb0 : (0 : ℝ) ≤ (104 * a + beta) * N := by positivity
  calc
    ((energy es ψ - energy es χ : Int) : ℝ) ≤ 2 * (B : ℝ) * (S : ℝ) := hcostR
    _ ≤ 2 * ((104 * a + beta) * N) * (Q * (104 * a + beta + rho) * N) := by
      apply mul_le_mul
      · linarith
      · exact hS
      · exact hS0
      · positivity
    _ = 2 * Q * (104 * a + beta + rho) * (104 * a + beta) * (N : ℝ)^2 := by ring

end Q4.Candidate.ProbeFreezing

#print axioms Q4.Candidate.ProbeFreezing.maxOutsideDegree_real_bound
#print axioms Q4.Candidate.ProbeFreezing.softProbes_le_realSoftProbes
#print axioms Q4.Candidate.ProbeFreezing.probe_freezing_real
