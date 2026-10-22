import Q4.Candidate.PaletteForcing
import Q4.Candidate.RankCorrection

/-! Numerical margins and actual rounded multiplicities for §5.  These
lemmas do not assert the geometric palette-field formula of Lemma 5.2. -/
namespace Q4.Candidate.PaletteBounds
open Q4.Candidate.PaletteForcing

theorem crossing_adverse_budget (O W B : ℚ) (hO : 0<O) (_hW : 0≤W)
    (hscale : 514*W≤O) (_hB : 0≤B) (hBscale : 1024*B≤O^2) :
    (9/2)*O^2+8*O*W+10*B<5*O^2 := by
  have hmul := mul_le_mul_of_nonneg_left hscale (le_of_lt hO)
  nlinarith [sq_pos_of_pos hO]

theorem side_adverse_budget (O W B : ℚ) (hO : 0<O) (_hW : 0≤W)
    (hscale : 514*W≤O) (_hB : 0≤B) (hBscale : 1024*B≤O^2) :
    8*O*W+8*B+O^2/2<O^2 := by
  have hmul := mul_le_mul_of_nonneg_left hscale (le_of_lt hO)
  nlinarith [sq_pos_of_pos hO]

theorem targets_positive (A theta b O : ℚ) (hO : 0<O) (hA : 8*O^2≤A)
    (htheta : 0≤theta) (hb : |b|≤4*O^2) :
    0<A+theta-b ∧ 0<A+theta ∧ A/2≤A+theta-b := by
  have hba := abs_le.mp hb
  constructor
  · nlinarith [sq_pos_of_pos hO]
  constructor
  · nlinarith [sq_pos_of_pos hO]
  · nlinarith

/-- An actual rounded family is numerous enough even when the opposite
half-frame weight differs from the weight used in the rounding. -/
theorem rounded_other_half (target weight other A B : ℚ)
    (hB : 0<B) (hA : 0≤A) (htarget : A/2≤target)
    (hw : 0<weight) (hwB : weight≤B) (hother : B/4≤other) :
    A/8≤(multiplicity target weight:ℚ)*other := by
  have ht : 0≤target := by linarith
  have hm := (multiplicity_bounds target weight ht hw).1
  have hc : (0:ℚ)≤multiplicity target weight := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hwB hc
  have hmul2 := mul_le_mul_of_nonneg_left hother hc
  have hweighted : A/2≤(multiplicity target weight:ℚ)*B := by nlinarith
  have hp := mul_nonneg (le_of_lt hB) (sub_nonneg.mpr hmul2)
  nlinarith

/-- Nonselected early-j/late-k palette sign, with actual computed ceil
multiplicities. rankField is permitted every value in its full family budget,
and degree pays for all core neighbors regardless of their colors. -/
theorem nonselected_direction (j k : ℕ) (hjk : j≠k) (A T b uL uR O W B rankField degree : ℚ)
    (hO : 0<O) (hW : 0≤W) (hscale : 514*W≤O)
    (hB : 0<B) (hBscale : 1024*B≤O^2) (hA : 8*O^2≤A) (hT : 5*O^2<T)
    (hb : |b|≤4*O^2) (huL : 0<uL) (huLB : uL≤B) (huR : 0<uR) (huRB : uR≤B)
    (hrank : |rankField|≤8*O*W+8*B) (hdegree : degree≤O^2/2) :
    let C_L := multiplicity (A+(j:ℚ)*T-b) uL
    let C_R := multiplicity (A+(k:ℚ)*T) uR
    if j<k then (C_L:ℚ)*uL-(C_R:ℚ)*uR+rankField< -degree
    else degree<(C_L:ℚ)*uL-(C_R:ℚ)*uR+rankField := by
  dsimp only
  have hT0 : 0<T := by nlinarith [sq_pos_of_pos hO]
  have htargetL := (targets_positive A ((j:ℚ)*T) b O hO hA (by positivity) hb).1
  have htargetR : 0≤A+(k:ℚ)*T := by nlinarith [sq_nonneg O,mul_nonneg (Nat.cast_nonneg k) (le_of_lt hT0)]
  have heL := roundingError_bounds (A+(j:ℚ)*T-b) uL B (le_of_lt htargetL) huL huLB
  have heR := roundingError_bounds (A+(k:ℚ)*T) uR B htargetR huR huRB
  have hbudget := crossing_adverse_budget O W B hO hW hscale (le_of_lt hB) hBscale
  have hba := abs_le.mp hb
  have hra := abs_le.mp hrank
  unfold roundingError at heL heR
  by_cases hjlt : j<k
  · simp only [hjlt,ite_true]
    have hjk' : (j:ℚ)+1≤k := by exact_mod_cast hjlt
    have hm := mul_le_mul_of_nonneg_right hjk' (le_of_lt hT0)
    nlinarith
  · simp only [hjlt,ite_false]
    have hkj : k<j := by omega
    have hkj' : (k:ℚ)+1≤j := by exact_mod_cast hkj
    have hm := mul_le_mul_of_nonneg_right hkj' (le_of_lt hT0)
    nlinarith


/-- The combined actual greedy rank-copy family has the manuscript's bound,
without adding one copy per unused internal gap. -/
theorem rank_copy_budget (slopeL slopeR B n O W : ℕ) (weightL weightR : ℕ → ℕ)
    (hB : 0<B) (hL : slopeL≤O) (hR : slopeR≤O) (hn : n≤W)
    (hwL : ∀i<n, 0<weightL i ∧ weightL i≤B ∧ B≤4*weightL i)
    (hwR : ∀i<n, 0<weightR i ∧ weightR i≤B ∧ B≤4*weightR i) :
    B*(Q4.Candidate.RankCorrection.copyCount slopeL weightL n+
      Q4.Candidate.RankCorrection.copyCount slopeR weightR n)<8*O*W+8*B := by
  have h1 := (Q4.Candidate.RankCorrection.greedy_correction slopeL B n weightL hB hwL).2
  have h2 := (Q4.Candidate.RankCorrection.greedy_correction slopeR B n weightR hB hwR).2
  have h3 := Nat.mul_le_mul hL hn
  have h4 := Nat.mul_le_mul hR hn
  nlinarith

/-- Concrete residual coefficient after the two actual greedy corrections and
the two computed ordinary ceil multiplicities. The shared right-prefix offset
is included in b, and no residual smallness is assumed. -/
theorem selected_residual_bound (beta A theta uL uR : ℤ) (slopeL slopeR B n r t : ℕ)
    (weightL weightR : ℕ → ℕ) (hB : 0<B) (hr : r≤n) (ht : t≤n)
    (hwL : ∀i<n, 0<weightL i ∧ weightL i≤B)
    (hwR : ∀i<n, 0<weightR i ∧ weightR i≤B)
    (huL : 0<uL) (huLB : uL≤B) (huR : 0<uR) (huRB : uR≤B)
    (htL : 0≤A+theta-(beta-Q4.Candidate.RankCorrection.cumulative slopeR weightR n))
    (htR : 0≤A+theta) :
    let b : ℤ := beta-Q4.Candidate.RankCorrection.cumulative slopeR weightR n
    let C_L := multiplicity ((A:ℚ)+theta-b) uL
    let C_R := multiplicity ((A:ℚ)+theta) uR
    |beta-(slopeL:ℤ)*r-(slopeR:ℤ)*t+
        Q4.Candidate.RankCorrection.cumulative slopeL weightL r-
        Q4.Candidate.RankCorrection.cumulative slopeR weightR n+
        Q4.Candidate.RankCorrection.cumulative slopeR weightR t+
        (C_L:ℤ)*uL-(C_R:ℤ)*uR|<4*(B:ℤ) := by
  let b : ℤ := beta-Q4.Candidate.RankCorrection.cumulative slopeR weightR n
  let C_L := multiplicity ((A:ℚ)+theta-b) uL
  let C_R := multiplicity ((A:ℚ)+theta) uR
  have hcorr := Q4.Candidate.RankCorrection.affine_correction beta slopeL slopeR B n r t
    weightL weightR hB hr ht hwL hwR
  dsimp only at hcorr
  obtain ⟨heL,heR,hident⟩ := hcorr
  have hBq : (0:ℚ)<B := by exact_mod_cast hB
  have hrL := roundingError_bounds ((A:ℚ)+theta-b) uL B
    (by exact_mod_cast htL) (by exact_mod_cast huL) (by exact_mod_cast huLB)
  have hrR := roundingError_bounds ((A:ℚ)+theta) uR B
    (by exact_mod_cast htR) (by exact_mod_cast huR) (by exact_mod_cast huRB)
  have heLq : (Q4.Candidate.RankCorrection.error slopeL weightL r:ℚ)<B := by exact_mod_cast heL
  have heRq : (Q4.Candidate.RankCorrection.error slopeR weightR t:ℚ)<B := by exact_mod_cast heR
  have heL0 : (0:ℚ)≤Q4.Candidate.RankCorrection.error slopeL weightL r := Nat.cast_nonneg _
  have heR0 : (0:ℚ)≤Q4.Candidate.RankCorrection.error slopeR weightR t := Nat.cast_nonneg _
  change |beta-(slopeL:ℤ)*r-(slopeR:ℤ)*t+
      Q4.Candidate.RankCorrection.cumulative slopeL weightL r-
      Q4.Candidate.RankCorrection.cumulative slopeR weightR n+
      Q4.Candidate.RankCorrection.cumulative slopeR weightR t+
      (C_L:ℤ)*uL-(C_R:ℤ)*uR|<4*(B:ℤ)
  rw [hident]
  have hbound : |(b:ℚ)+Q4.Candidate.RankCorrection.error slopeL weightL r+
      Q4.Candidate.RankCorrection.error slopeR weightR t+(C_L:ℚ)*uL-(C_R:ℚ)*uR|<4*(B:ℚ) := by
    rw [abs_lt]
    unfold roundingError at hrL hrR
    change 0≤(C_L:ℚ)*uL-((A:ℚ)+theta-b) ∧
      (C_L:ℚ)*uL-((A:ℚ)+theta-b)<B at hrL
    change 0≤(C_R:ℚ)*uR-((A:ℚ)+theta) ∧
      (C_R:ℚ)*uR-((A:ℚ)+theta)<B at hrR
    constructor <;> linarith
  exact_mod_cast hbound

end Q4.Candidate.PaletteBounds
#print axioms Q4.Candidate.PaletteBounds.crossing_adverse_budget
#print axioms Q4.Candidate.PaletteBounds.side_adverse_budget
#print axioms Q4.Candidate.PaletteBounds.rounded_other_half
#print axioms Q4.Candidate.PaletteBounds.nonselected_direction

#print axioms Q4.Candidate.PaletteBounds.rank_copy_budget
#print axioms Q4.Candidate.PaletteBounds.selected_residual_bound
