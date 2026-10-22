import Q4.Candidate.PaletteBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Fin

/-! Actual finite labels for all ordinary and rank copies. The counts are the
computed ceil and greedy multiplicities, not assumed program-family sizes. -/
namespace Q4.Candidate.ProgramCount
open scoped BigOperators

structure Recipe (S : ℕ) where
  A : ℚ
  T : ℚ
  offset : Fin S → ℚ
  ordinaryLeftWeight : Fin S → ℚ
  ordinaryRightWeight : Fin S → ℚ
  leftSlope : Fin S → ℕ
  rightSlope : Fin S → ℕ
  leftWeight : Fin S → ℕ → ℕ
  rightWeight : Fin S → ℕ → ℕ

def ordinaryLeft {S : ℕ} (d : Recipe S) (j : Fin S) : ℕ :=
  PaletteForcing.multiplicity (d.A+j.val*d.T-d.offset j) (d.ordinaryLeftWeight j)
def ordinaryRight {S : ℕ} (d : Recipe S) (j : Fin S) : ℕ :=
  PaletteForcing.multiplicity (d.A+j.val*d.T) (d.ordinaryRightWeight j)
def rankLeft {S : ℕ} (d : Recipe S) (j : Fin S) (g : ℕ) : ℕ :=
  RankCorrection.multiplicity (d.leftSlope j) (d.leftWeight j) g
def rankRight {S : ℕ} (d : Recipe S) (j : Fin S) (g : ℕ) : ℕ :=
  RankCorrection.multiplicity (d.rightSlope j) (d.rightWeight j) g

/-- Each value is one point-copy label, with an explicit family, selected
macro label, internal gap (for rank), and copy number. -/
abbrev Label {S : ℕ} (d : Recipe S) (gaps : ℕ) :=
  (Σ j : Fin S, Fin (ordinaryLeft d j)) ⊕
  ((Σ j : Fin S, Fin (ordinaryRight d j)) ⊕
  ((Σ j : Fin S, Σ g : Fin gaps, Fin (rankLeft d j g.val)) ⊕
   (Σ j : Fin S, Σ g : Fin gaps, Fin (rankRight d j g.val))))

theorem copyCount_eq_sum (slope n : ℕ) (weight : ℕ → ℕ) :
    RankCorrection.copyCount slope weight n =
      ∑ g : Fin n, RankCorrection.multiplicity slope weight g.val := by
  induction n with
  | zero => simp [RankCorrection.copyCount]
  | succ n ih => simp [RankCorrection.copyCount,Fin.sum_univ_castSucc,ih]

theorem label_card {S : ℕ} (d : Recipe S) (gaps : ℕ) :
    Fintype.card (Label d gaps) = ∑ j : Fin S,
      (ordinaryLeft d j+ordinaryRight d j+
       RankCorrection.copyCount (d.leftSlope j) (d.leftWeight j) gaps+
       RankCorrection.copyCount (d.rightSlope j) (d.rightWeight j) gaps) := by
  classical
  change Fintype.card ((Σ j : Fin S, Fin (ordinaryLeft d j)) ⊕
    ((Σ j : Fin S, Fin (ordinaryRight d j)) ⊕
    ((Σ j : Fin S, Σ g : Fin gaps, Fin (rankLeft d j g.val)) ⊕
     (Σ j : Fin S, Σ g : Fin gaps, Fin (rankRight d j g.val))))) = _
  simp_rw [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,
    Finset.sum_add_distrib,copyCount_eq_sum,rankLeft,rankRight]
  omega

theorem ceil_count_bound (target weight A B : ℚ) (hB : 0<B)
    (ht : 0≤target) (htA : target≤2*A) (hw : B/4≤weight) :
    (PaletteForcing.multiplicity target weight:ℚ) ≤ 8*A/B+1 := by
  have hw0 : 0<weight := by linarith
  have hA : 0≤A := by linarith
  have hprod := mul_le_mul_of_nonneg_right htA (le_of_lt hB)
  have hprod' := mul_le_mul_of_nonneg_left hw (by positivity : (0:ℚ)≤8*A)
  have hdiv : target/weight ≤ 8*A/B :=
    (div_le_div_iff₀ hw0 hB).2 (by nlinarith)
  have hceil := Nat.ceil_lt_add_one (div_nonneg ht (le_of_lt hw0))
  unfold PaletteForcing.multiplicity
  linarith

/-- The first bound of (5.16), for the cardinality of the actual disjoint
copy-label type. Rank programs use the proved greedy count, with no additive
charge for each unused gap. The target/weight premises are checked separately
by the actual ordinary/rank geometry and palette offset construction. -/
theorem program_count_bound {S : ℕ} (d : Recipe S) (gaps O W B : ℕ)
    (hB : 0<B) (hg : gaps≤W)
    (htL : ∀ j, 0≤d.A+j.val*d.T-d.offset j ∧ d.A+j.val*d.T-d.offset j≤2*d.A)
    (htR : ∀ j : Fin S, 0≤d.A+j.val*d.T ∧ d.A+j.val*d.T≤2*d.A)
    (huL : ∀ j, (B:ℚ)/4≤d.ordinaryLeftWeight j)
    (huR : ∀ j, (B:ℚ)/4≤d.ordinaryRightWeight j)
    (hsL : ∀ j, d.leftSlope j≤O) (hsR : ∀ j, d.rightSlope j≤O)
    (hwL : ∀ j i, i<gaps → 0<d.leftWeight j i ∧ d.leftWeight j i≤B ∧ B≤4*d.leftWeight j i)
    (hwR : ∀ j i, i<gaps → 0<d.rightWeight j i ∧ d.rightWeight j i≤B ∧ B≤4*d.rightWeight j i) :
    (Fintype.card (Label d gaps):ℚ) ≤
      16*S*d.A/B+8*S*O*W/B+10*S := by
  have hBq : (0:ℚ)<B := by exact_mod_cast hB
  have hj (j : Fin S) :
      ((ordinaryLeft d j+ordinaryRight d j+
       RankCorrection.copyCount (d.leftSlope j) (d.leftWeight j) gaps+
       RankCorrection.copyCount (d.rightSlope j) (d.rightWeight j) gaps):ℚ) ≤
        16*d.A/B+8*O*W/B+10 := by
    have hL := ceil_count_bound _ _ d.A B hBq (htL j).1 (htL j).2 (huL j)
    have hR := ceil_count_bound _ _ d.A B hBq (htR j).1 (htR j).2 (huR j)
    have hr := PaletteBounds.rank_copy_budget (d.leftSlope j) (d.rightSlope j) B gaps O W
      (d.leftWeight j) (d.rightWeight j) hB (hsL j) (hsR j) hg (hwL j) (hwR j)
    have hrq : (B:ℚ)*((RankCorrection.copyCount (d.leftSlope j) (d.leftWeight j) gaps:ℚ)+
      RankCorrection.copyCount (d.rightSlope j) (d.rightWeight j) gaps)<8*O*W+8*B := by exact_mod_cast hr
    have hrdiv : (RankCorrection.copyCount (d.leftSlope j) (d.leftWeight j) gaps:ℚ)+
      RankCorrection.copyCount (d.rightSlope j) (d.rightWeight j) gaps < (8*O*W+8*B)/B :=
      (lt_div_iff₀ hBq).2 (by nlinarith only [hrq])
    change (ordinaryLeft d j:ℚ)+(ordinaryRight d j:ℚ)+_+_≤_
    unfold ordinaryLeft ordinaryRight
    have he : (8*(O:ℚ)*W+8*B)/B = 8*O*W/B+8 := by field_simp
    rw [he] at hrdiv
    ring_nf at hL hR hrdiv ⊢
    linarith
  rw [label_card,Nat.cast_sum]
  simp only [Nat.cast_add]
  have hsum := Finset.sum_le_sum (fun (j : Fin S) (_ : j∈Finset.univ) => hj j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  convert hsum using 1
  ring

end Q4.Candidate.ProgramCount
#print axioms Q4.Candidate.ProgramCount.label_card
#print axioms Q4.Candidate.ProgramCount.ceil_count_bound
#print axioms Q4.Candidate.ProgramCount.program_count_bound
