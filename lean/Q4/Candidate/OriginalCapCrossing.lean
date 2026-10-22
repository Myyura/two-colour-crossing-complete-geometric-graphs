import Q4.Candidate.DoubleCapGrid

/-! Actual source-chord geometry on the original rational cap. Shared endpoints
are included: the strict scalar test is zero and hence there is no proper crossing. -/
namespace Q4.Candidate.OriginalCapCrossing
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid

theorem separated_scalar (a b c d : ℚ) (hab : a<b) (hcd : c<d)
    (had : a<d) (hcb : c<b) :
    ProperCross (original a) (original b) (original c) (original d) ↔
      0 < (c-a)*(d-b) := by
  let p := (b-a)^2*(b-c)*(d-a)/10000
  let q := (d-c)^2*(b-c)*(d-a)/10000
  have hp : 0<p := by dsimp [p]; positivity
  have hq : 0<q := by dsimp [q]; positivity
  have he1 : orient (original a) (original b) (original c)*
      orient (original a) (original b) (original d) = -((c-a)*(d-b))*p := by
    simp only [original_vandermonde]
    dsimp [p]
    ring
  have he2 : orient (original c) (original d) (original a)*
      orient (original c) (original d) (original b) = -((c-a)*(d-b))*q := by
    simp only [original_vandermonde]
    dsimp [q]
    ring
  have hs1 : -((c-a)*(d-b))*p<0 ↔ 0<(c-a)*(d-b) := by
    rw [mul_neg_iff]
    constructor
    · intro h; rcases h with h | h <;> linarith
    · intro h; exact Or.inr ⟨by linarith,hp⟩
  have hs2 : -((c-a)*(d-b))*q<0 ↔ 0<(c-a)*(d-b) := by
    rw [mul_neg_iff]
    constructor
    · intro h; rcases h with h | h <;> linarith
    · intro h; exact Or.inr ⟨by linarith,hq⟩
  simp only [ProperCross,he1,he2,hs1,hs2,and_self]

theorem separated_order (a b c d : ℚ) (hab : a<b) (hcd : c<d)
    (had : a<d) (hcb : c<b) :
    ProperCross (original a) (original b) (original c) (original d) ↔
      (a<c ∧ b<d) ∨ (c<a ∧ d<b) := by
  rw [separated_scalar a b c d hab hcd had hcb,mul_pos_iff]
  simp only [sub_pos,sub_neg]

/-- The original endpoints lie in a common ordered sequence, with the early
part strictly before the late part. Only these endpoints are on this cap. -/
theorem indexed_separated (O : ℕ) (ys : Fin O → ℚ) (hy : StrictMono ys)
    (a b c d : Fin O) (hab : a<b) (hcd : c<d) (had : a<d) (hcb : c<b) :
    ProperCross (original (ys a)) (original (ys b))
      (original (ys c)) (original (ys d)) ↔
      (a<c ∧ b<d) ∨ (c<a ∧ d<b) := by
  rw [separated_order _ _ _ _ (hy hab) (hy hcd) (hy had) (hy hcb)]
  simp only [hy.lt_iff_lt]

end Q4.Candidate.OriginalCapCrossing
#print axioms Q4.Candidate.OriginalCapCrossing.separated_scalar
#print axioms Q4.Candidate.OriginalCapCrossing.separated_order
#print axioms Q4.Candidate.OriginalCapCrossing.indexed_separated
