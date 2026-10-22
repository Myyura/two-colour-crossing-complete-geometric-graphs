import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
Candidate manuscript 0.3, §7: quantitative error composition and the actual
integer-source threshold. This module does not assume or assert that an arbitrary
geometric construction meets its energy bounds. Those connections are separate
theorems. In particular, no NP-hardness proposition is introduced as an axiom.
-/

namespace Q4.Candidate.ReductionGap

/-- The source value and threshold are integers. A gap narrower than one fourth
of the positive signal yields the manuscript's one-query decision threshold. -/
theorem threshold_equivalence
    (g t : ℤ) (K Δ step value eMinus ePlus : ℝ)
    (hΔ : 0 < Δ) (hstep : 4 * step = Δ)
    (hm : 0 ≤ eMinus) (hp : 0 ≤ ePlus)
    (herr : 4 * (eMinus + ePlus) < Δ)
    (hlo : K + Δ * (g : ℝ) - eMinus ≤ value)
    (hhi : value ≤ K + Δ * (g : ℝ) + ePlus) :
    value ≤ K + Δ * (t : ℝ) + step ↔ g ≤ t := by
  constructor
  · intro hv
    by_contra hgt
    have hg : t + 1 ≤ g := by omega
    have hgR : (t : ℝ) + 1 ≤ (g : ℝ) := by exact_mod_cast hg
    have hprod := mul_le_mul_of_nonneg_left hgR (le_of_lt hΔ)
    nlinarith
  · intro hg
    have hgR : (g : ℝ) ≤ (t : ℝ) := by exact_mod_cast hg
    have hprod := mul_le_mul_of_nonneg_left hgR (le_of_lt hΔ)
    nlinarith

/-- The paper's three independently charged errors fit strictly inside the
claimed 2^-19 signal window. No cancellation between errors is used. -/
theorem error_window
    (Δ eAlg eUnary eLocal : ℝ) (hΔ : 0 < Δ)
    (ha : eAlg ≤ Δ / (2 : ℝ)^40)
    (hu : eUnary ≤ Δ / (2 : ℝ)^40)
    (hl : eLocal ≤ Δ / (3 * (2 : ℝ)^19)) :
    (2 : ℝ)^19 * (eAlg + eUnary + eLocal) < Δ := by
  norm_num at ha hu hl ⊢
  linarith

/-- The source macro-copy count pays all local source/short constraints. -/
theorem local_error_bound
    (n q H : ℝ) (hn : 0 ≤ n) (hH : 0 ≤ H)
    (hq : q = (2 : ℝ)^20 * (n + 1)) :
    (2 / 3 : ℝ) * (n * q) * H^16 ≤
      (q^2 * H^16) / (3 * (2 : ℝ)^19) := by
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hscale : (2 : ℝ)^20 * n ≤ q := by rw [hq]; nlinarith
  have hp := mul_le_mul_of_nonneg_right hscale (mul_nonneg hq0 (pow_nonneg hH 16))
  norm_num at hp ⊢
  nlinarith

/-- First isolate the large-scale algebraic error from all geometry. This is
the precise scalar domination used by the source reduction. -/
theorem algebraic_error_bound
    (d q H : ℝ) (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hH : (2 : ℝ)^350 * d^14 ≤ H) :
    (2 : ℝ)^310 * d^14 * H^15 ≤ (q^2 * H^16) / (2 : ℝ)^40 := by
  have hd0 : 0 ≤ d := by linarith
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hq2 : 1 ≤ q^2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hH (pow_nonneg hH0 15)
  have h2 := mul_le_mul_of_nonneg_right hq2 (pow_nonneg hH0 16)
  calc
    (2 : ℝ)^310 * d^14 * H^15 =
        ((2 : ℝ)^350 * d^14 * H^15) / (2 : ℝ)^40 := by
      rw [show (350 : ℕ) = 40 + 310 by rfl, pow_add]
      set_option exponentiation.threshold 512 in ring
    _ ≤ H^16 / (2 : ℝ)^40 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      convert h1 using 1 <;> ring
    _ ≤ q^2 * H^16 / (2 : ℝ)^40 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [one_mul] using h2

/- The actual growth parameters, rather than just a hypothesis that a suitable
large scale exists. These are real casts of the integer parameters in §1.3. -/

theorem actual_scale_lower (d : ℝ) (hd : 1 ≤ d) :
    (2 : ℝ)^350 * d^14 ≤ (2 : ℝ)^20000 * d^40 := by
  exact mul_le_mul
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 350 ≤ 20000))
    (pow_le_pow_right₀ hd (by omega : 14 ≤ 40))
    (by positivity) (by positivity)

theorem actual_scale_large (d : ℝ) (hd : 1 ≤ d) :
    (2 : ℝ)^44 ≤ (2 : ℝ)^20000 * d^40 := by
  have h1 : (2 : ℝ)^44 ≤ (2 : ℝ)^20000 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hd40 : (1 : ℝ) ≤ d^40 := one_le_pow₀ hd
  apply le_trans h1
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd40
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)^20000)

theorem unary_error_bound (n q H : ℝ) (_hn : 0 ≤ n) (hnq : n ≤ q)
    (hq : 0 ≤ q) (hH : (2 : ℝ)^44 ≤ H) :
    10 * (n * q) * H^13 ≤ (q^2 * H^16) / (2 : ℝ)^40 := by
  have hH1 : 1 ≤ H := by norm_num at hH; linarith
  have hH0 : 0 ≤ H := by linarith
  have hcube : (2 : ℝ)^44 ≤ H^3 :=
    le_trans hH (by simpa using pow_le_pow_right₀ hH1 (by omega : 1 ≤ 3))
  have hnq2 := mul_le_mul_of_nonneg_right hnq hq
  have hc : 10 * (2 : ℝ)^40 ≤ H^3 := by norm_num at hcube ⊢; linarith
  have hprod := mul_le_mul_of_nonneg_left hc
    (mul_nonneg (sq_nonneg q) (pow_nonneg hH0 13))
  have hleft := mul_le_mul_of_nonneg_left hnq2
    (by positivity : 0 ≤ 10 * H^13)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^40)).2
  calc
    10 * (n * q) * H^13 * (2 : ℝ)^40 ≤
        10 * q^2 * H^13 * (2 : ℝ)^40 := by nlinarith
    _ ≤ q^2 * H^16 := by convert hprod using 1 <;> ring

/-- Instantiate all scalar scale requirements using the manuscript's actual
parameters. The three input bounds are exactly the separately counted cost
groups; this theorem does not assume their desired small ratios. -/
theorem actual_error_window (n : ℝ) (hn : 0 ≤ n)
    (eAlg eUnary eLocal : ℝ)
    (q d H : ℝ) (hq : q = (2 : ℝ)^20 * (n+1))
    (hd : d = n*q+1) (hH : H = (2 : ℝ)^20000*d^40)
    (ha : eAlg ≤ (2 : ℝ)^310*d^14*H^15)
    (hu : eUnary ≤ 10*(n*q)*H^13)
    (hl : eLocal ≤ (2/3 : ℝ)*(n*q)*H^16) :
    (2 : ℝ)^19*(eAlg+eUnary+eLocal) < q^2*H^16 := by
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith
  have hq0 : 0 ≤ q := by linarith
  have hnq : n ≤ q := by rw [hq]; nlinarith
  have hd1 : 1 ≤ d := by rw [hd]; exact le_add_of_nonneg_left (mul_nonneg hn hq0)
  have hlarge : (2 : ℝ)^44 ≤ H := by rw [hH]; exact actual_scale_large d hd1
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hlarge
  have hsignal : 0 < q^2*H^16 := mul_pos (pow_pos (by linarith) _) (pow_pos hH0 _)
  apply error_window _ _ _ _ hsignal
  · exact ha.trans (algebraic_error_bound d q H hd1 hq1
      (by rw [hH]; exact actual_scale_lower d hd1))
  · exact hu.trans (unary_error_bound n q H hn hnq hq0 hlarge)
  · exact hl.trans (local_error_bound n q H hn (le_of_lt hH0) hq)

end Q4.Candidate.ReductionGap

#print axioms Q4.Candidate.ReductionGap.threshold_equivalence
#print axioms Q4.Candidate.ReductionGap.error_window
#print axioms Q4.Candidate.ReductionGap.local_error_bound
#print axioms Q4.Candidate.ReductionGap.algebraic_error_bound
#print axioms Q4.Candidate.ReductionGap.actual_scale_lower
#print axioms Q4.Candidate.ReductionGap.actual_scale_large
#print axioms Q4.Candidate.ReductionGap.unary_error_bound
#print axioms Q4.Candidate.ReductionGap.actual_error_window
