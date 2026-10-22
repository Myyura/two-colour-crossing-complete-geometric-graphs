import Q4.Candidate.PaletteBounds
import Q4.Candidate.CandidateSize

/-! The exact integer ordinary-fan target parameters used by the candidate
construction, with finite bounds for every macro label. -/
namespace Q4.Candidate.CatalogTargets

def amplitude (S O : ℕ) : ℤ := 2^26*((S:ℤ)+1)*(O:ℤ)^2
def increment (O : ℕ) : ℤ := 2^13*(O:ℤ)^2

theorem margins (S O : ℕ) (hO : 0<O) :
    8*(O:ℤ)^2 ≤ amplitude S O ∧ 5*(O:ℤ)^2 < increment O ∧ 0 ≤ increment O := by
  have hs : (0:ℤ)≤S := Nat.cast_nonneg S
  have ho : (0:ℤ)<O := by exact_mod_cast hO
  constructor
  · unfold amplitude
    norm_num
    nlinarith [sq_pos_of_pos ho,mul_nonneg hs (sq_nonneg (O:ℤ))]
  constructor
  · unfold increment
    norm_num
    nlinarith [sq_pos_of_pos ho]
  · unfold increment
    positivity

theorem target_bounds (S O : ℕ) (j : Fin S) (b : ℚ) (hb : |b|≤4*(O:ℚ)^2) :
    0≤(amplitude S O:ℚ)+j.val*(increment O:ℚ)-b ∧
    (amplitude S O:ℚ)+j.val*(increment O:ℚ)-b≤2*(amplitude S O:ℚ) ∧
    0≤(amplitude S O:ℚ)+j.val*(increment O:ℚ) ∧
    (amplitude S O:ℚ)+j.val*(increment O:ℚ)≤2*(amplitude S O:ℚ) := by
  have hs : (0:ℚ)≤S := Nat.cast_nonneg S
  have hj : (j.val:ℚ)≤S := by exact_mod_cast (le_of_lt j.isLt)
  have hz := sq_nonneg (O:ℚ)
  have hjz := mul_le_mul_of_nonneg_right hj hz
  have hj0 := mul_nonneg (Nat.cast_nonneg (α:=ℚ) j.val) hz
  have hs0 := mul_nonneg hs hz
  have hb' := abs_le.mp hb
  simp only [amplitude,increment,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_add,Int.cast_natCast,Int.cast_one]
  norm_num
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

open Q4.Candidate.FreezingParameters
attribute [local irreducible] scale originals frames

theorem frame_divisible (S : ℕ) : 8∣frames S := by
  unfold frames scale
  have hd : 8∣(2:ℕ)^20000 := by
    change (2:ℕ)^3∣2^20000
    exact pow_dvd_pow 2 (by omega)
  exact dvd_pow (dvd_mul_of_dvd_left hd ((S+1)^40)) (by decide : 5≠0)

/-- The actual frame count is tiny compared with the square of the actual
original count, without assuming the program-count bound. -/
theorem frame_small (S : ℕ) (hS : 1≤S) : 1024*frames S≤(originals S)^2 := by
  have hH : 0<scale S := by unfold scale; positivity
  have hS2 : 1≤S^2 := Nat.one_le_pow 2 S (by omega)
  have hH3 : 1≤(scale S)^3 := Nat.one_le_pow 3 (scale S) hH
  have hp : 1≤S^2*(scale S)^3 := by nlinarith
  have hcoef : 1024≤514^2*S^2*(scale S)^3 := by nlinarith
  have hm := Nat.mul_le_mul_right ((scale S)^5) hcoef
  unfold frames originals
  convert hm using 1; ring

/-- The explicit H,W,D,B values discharge the dimensional hypotheses of the
actual fan theorems. This uses the P=0 case only to recover numeric O≤B. -/
theorem dimensions (n q D W B : ℕ) (hS : 0<n*q)
    (hW : W=(scale (n*q))^4) (hD : D=512*(n*q)*W) (hB : B=frames (n*q)) :
    2≤W ∧ 1000≤n*q*W+D+n*q*W ∧ n*q*W+D+n*q*W≤B ∧
    1024*B≤(n*q*W+D+n*q*W)^2 ∧ 8∣B := by
  have hOeq : n*q*W+D+n*q*W=originals (n*q) := by
    rw [hD,hW]
    unfold originals
    ring
  have hp0 : (0:ℝ)≤(2:ℝ)^80*((n*q:ℝ)+1)^4*(scale (n*q):ℝ)^3 :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by positivity) 4)) (pow_nonneg (Nat.cast_nonneg _) _)
  have hb := actual_bounds (n*q) 0 (by omega) (by convert hp0 using 1 <;> push_cast <;> ring)
  have hH := CandidateSize.scale_ge_sixteen (n*q)
  have hW2 : 2≤W := by
    rw [hW]
    have hh := Nat.pow_le_pow_right (show 0<scale (n*q) by omega) (show 1≤4 by omega)
    simp only [pow_one] at hh
    omega
  refine ⟨hW2,?_,?_,?_,?_⟩
  · simpa only [hOeq] using hb.1
  · simpa only [hOeq,hB] using hb.2.1
  · simpa only [hOeq,hB] using frame_small (n*q) (by omega)
  · rw [hB]; exact frame_divisible (n*q)

end Q4.Candidate.CatalogTargets
#print axioms Q4.Candidate.CatalogTargets.margins
#print axioms Q4.Candidate.CatalogTargets.target_bounds

#print axioms Q4.Candidate.CatalogTargets.frame_small
#print axioms Q4.Candidate.CatalogTargets.dimensions
