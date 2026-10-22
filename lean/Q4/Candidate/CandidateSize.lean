import Q4.Candidate.ProgramPlacement
import Q4.Candidate.FreezingParameters

/-! Explicit polynomial point-count and coordinate-bit bounds after the
actual catalog copy-count estimate. No parameter may grow independently of
the source instance in the final two bounds. -/
namespace Q4.Candidate.CandidateSize
open Q4.Candidate.FreezingParameters Q4.Candidate.ProgramPlacement
set_option exponentiation.threshold 20000
set_option maxRecDepth 4096
attribute [local irreducible] scale originals frames

theorem scalar_encoding_budget (S D W O B P : ℕ)
    (hB : 10000≤B) (hS : S+1≤B) (hD : D≤B) (hW : W≤B)
    (hO : O≤B) (hP : P≤O) :
    O+B+P≤3*B ∧
    (10000+8*(S+1)+4*(D+1)+W+B+(O+B+P))*(602*(O+B)+2719)≤2^17*B^2 := by
  have hL : 10000+8*(S+1)+4*(D+1)+W+B+(O+B+P)≤22*B := by omega
  have hK : 602*(O+B)+2719≤3923*B := by omega
  refine ⟨by omega,?_⟩
  calc
    _ ≤ (22*B)*(3923*B) := Nat.mul_le_mul hL hK
    _ ≤ 2^17*B^2 := by norm_num; nlinarith

theorem scale_ge_sixteen (S : ℕ) : 16≤scale S := by
  have hp : (2:ℕ)^4≤2^20000 := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by decide : 4≤20000)
  have hd : 1≤(S+1)^40 := Nat.one_le_pow _ _ (by omega)
  unfold scale
  change 2^4≤2^20000*(S+1)^40
  exact hp.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^20000) hd)

theorem actual_size_bounds (S P : ℕ) (hS : 1≤S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3) :
    let H := scale S
    let O := 514*S*H^4
    let B := H^5
    let D := 512*S*H^4
    O+B+P≤3*H^5 ∧
    (10000+8*(S+1)+4*(D+1)+H^4+B+(O+B+P))*(602*(O+B)+2719)≤2^17*H^10 := by
  dsimp only
  have hb := actual_bounds S P hS hP
  have hH := scale_ge_sixteen S
  have hW1 : 1≤(scale S)^4 := Nat.one_le_pow _ _ (by omega)
  have hH5 : 16^5≤(scale S)^5 := Nat.pow_le_pow_left hH 5
  have hB : 10000≤(scale S)^5 := by norm_num at hH5; omega
  have hW : (scale S)^4≤(scale S)^5 := Nat.pow_le_pow_right (by omega) (by omega : 4≤5)
  have hSO : S+1≤514*S*(scale S)^4 := by nlinarith
  have hO : 514*S*(scale S)^4≤(scale S)^5 := by simpa only [originals,frames] using hb.2.1
  have hPO : P≤514*S*(scale S)^4 := by simpa only [originals] using hb.2.2.1
  have hD : 512*S*(scale S)^4≤(scale S)^5 :=
    (Nat.mul_le_mul_right ((scale S)^4) (Nat.mul_le_mul_right S (by omega : 512≤514))).trans hO
  have hh := scalar_encoding_budget S (512*S*(scale S)^4) ((scale S)^4)
    (514*S*(scale S)^4) ((scale S)^5) P hB (hSO.trans hO) hD hW hO hPO
  refine ⟨hh.1,?_⟩
  convert hh.2 using 1
  rw [←pow_mul]

/-- Explicit source-size polynomial envelope for H. The degree is large but
fixed, and the binary coordinate budget below is polynomial, not exponential
in the source encoding length. -/
theorem source_scale_bound (n q : ℕ) (hq : q=2^20*(n+1)) :
    scale (n*q)≤2^20840*(n+1)^80 := by
  have hd : n*q+1≤2^21*(n+1)^2 := by
    rw [hq]
    norm_num
    nlinarith
  have hp := Nat.pow_le_pow_left hd 40
  have hh := Nat.mul_le_mul_left (2^20000) hp
  unfold scale
  calc
    _ ≤ 2^20000*(2^21*(n+1)^2)^40 := hh
    _ = 2^20840*(n+1)^80 := by
      rw [mul_pow,←pow_mul,←pow_mul,←mul_assoc,←pow_add]

theorem source_polynomial_bounds (n q P : ℕ) (hn : 1≤n) (hq : q=2^20*(n+1))
    (hP : (P:ℝ)≤(2:ℝ)^80*((n*q:ℕ)+1:ℝ)^4*(scale (n*q):ℝ)^3) :
    originals (n*q)+frames (n*q)+P≤3*(2^20840*(n+1)^80)^5 ∧
    (10000+8*(n*q+1)+4*(512*(n*q)*(scale (n*q))^4+1)+(scale (n*q))^4+
      frames (n*q)+(originals (n*q)+frames (n*q)+P))*
      (602*(originals (n*q)+frames (n*q))+2719)≤2^17*(2^20840*(n+1)^80)^10 := by
  have hq0 : 0<q := by rw [hq]; positivity
  have hS : 1≤n*q := Nat.mul_pos (by omega) hq0
  have hh := actual_size_bounds (n*q) P hS hP
  have hH := source_scale_bound n q hq
  simp only [originals,frames]
  constructor
  · exact hh.1.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hH 5))
  · exact hh.2.trans (Nat.mul_le_mul_left (2^17) (Nat.pow_le_pow_left hH 10))

end Q4.Candidate.CandidateSize
#print axioms Q4.Candidate.CandidateSize.actual_size_bounds
#print axioms Q4.Candidate.CandidateSize.source_scale_bound
#print axioms Q4.Candidate.CandidateSize.source_polynomial_bounds
