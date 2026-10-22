import Q4.Candidate.RankResponse
import Q4.Candidate.OrdinaryCoreField
import Q4.Candidate.OrdinaryTablePreservation
import Q4.Candidate.ParentBlockExclusion

/-! Actual canonical responses and core coefficients of the final placed
ordinary copies, obtained from the common-radius geometry theorems. -/
namespace Q4.Candidate.PlacedOrdinaryField
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.OrdinaryFan Q4.Candidate.OrdinaryResponse
open Q4.Candidate.OrdinaryTablePreservation Q4.Candidate.OrientationPreservation
open Q4.Candidate.UniformInsertion Q4.Candidate.VirtualColumnField
open Q4.Candidate.RankSoftRows
open scoped BigOperators

@[simp] theorem ordinary_pointField {B O : ℕ} (sigma : Fin B × Fin O → ℤ)
    (ys : Fin O → ℚ) (a mu : ℚ) (k : Fin B) :
    pointField sigma ys (ordinary a mu) k=ordinaryField sigma ys a mu k := rfl

theorem ordinary_response {B O r : ℕ} (d : Geometry B O r) (k : Fin B) :
    Q4.Candidate.RankResponse.response d.ys (ordinary d.a d.mu) k=OrdinaryResponse.response d k := by
  unfold RankResponse.response OrdinaryResponse.response actualField
  rw [ordinary_pointField]
  congr 1
  norm_cast

theorem ordinary_coefficient {B O r : ℕ} (d : Geometry B O r) (c b : ℚ) :
    RankResponse.coreCoefficient (B:=B) d.ys (ordinary d.a d.mu) (original c) (original b)=
      OrdinaryCoreField.coreCoefficient d c b := by
  classical
  unfold RankResponse.coreCoefficient OrdinaryCoreField.coreCoefficient
  simp only [RankResponse.responseSpin,ordinary_response]

/-- The actual grid field of every final placed ordinary copy is exactly its
prototype field. Parent and nonparent tables are both instantiated. -/
theorem placed_field_eq {N O cut : ℕ} (d : Geometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀k, frame (frameParameter N k)∈B) (hy : ∀j, original (d.ys j)∈B)
    (hr : ordinary d.a d.mu∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (ordinary d.a d.mu) p)
    (sigma : Fin N × Fin O → ℤ) (k : Fin N) :
    pointField sigma d.ys p k=ordinaryField sigma d.ys d.a d.mu k := by
  classical
  unfold pointField pointColumn ordinaryField ordinaryColumn
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hj : j∈d.parent
  · have h1 := placed_ordinary_clone_fan M N B R d.even i k d.a (d.ys j) d.mu p
      d.unit_a (d.unit_y j) d.mu_pos d.mu_le (d.clone j hj) (hf i) (hf k) (hy j) hr hproto hp
    have h2 := ordinary_clone_indexed N d.even i k d.a (d.ys j) d.mu
      d.unit_a (d.unit_y j) d.mu_pos d.mu_le (d.clone j hj)
    simp only [h1,h2]
  · have h1 := placed_ordinary_nonparent_fan M N B R i k d.a (d.ys j) d.mu p
      d.unit_a (d.unit_y j) d.mu_pos d.mu_le (d.sep j hj) (hf i) (hf k) (hy j) hr hproto hp
    have h2 := ordinary_nonparent_indexed N i k d.a (d.ys j) d.mu
      d.unit_a (d.unit_y j) d.mu_pos d.mu_le (d.sep j hj)
    simp only [h1,h2]

theorem placed_response_eq {N O cut : ℕ} (d : Geometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀k, frame (frameParameter N k)∈B) (hy : ∀j, original (d.ys j)∈B)
    (hr : ordinary d.a d.mu∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (ordinary d.a d.mu) p) (k : Fin N) :
    RankResponse.response d.ys p k=OrdinaryResponse.response d k := by
  unfold RankResponse.response OrdinaryResponse.response actualField
  rw [placed_field_eq d M B R p hf hy hr hproto hp]
  congr 1
  norm_cast

/-- Every actual placed-copy incident coefficient equals the prototype
integer weight, independently of the copy location within the common box. -/
theorem placed_incident_coefficient {N O cut : ℕ} (d : Geometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀k, frame (frameParameter N k)∈B) (hy : ∀j, original (d.ys j)∈B)
    (hr : ordinary d.a d.mu∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (ordinary d.a d.mu) p)
    (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hclone : 3*((N:ℚ)+1)*|c-d.a|≤d.mu) (hsep : 5*d.mu≤|b-d.a|)
    (hcMem : original c∈B) (hbMem : original b∈B) :
    RankResponse.coreCoefficient (B:=N) d.ys p (original c) (original b)=
      OrdinaryCoreField.coreCoefficient d c b := by
  classical
  unfold RankResponse.coreCoefficient OrdinaryCoreField.coreCoefficient
  apply Finset.sum_congr rfl
  intro k _
  have h1 := placed_ordinary_clone_core M N B R d.even k d.a c b d.mu p
    d.unit_a hc hb d.mu_pos d.mu_le hclone hsep (hf k) hcMem hbMem hr hproto hp
  have h2 := ordinary_clone_core_indexed N d.even k d.a c b d.mu
    d.unit_a hc hb d.mu_pos d.mu_le hclone hsep
  simp only [h1,h2,RankResponse.responseSpin,placed_response_eq d M B R p hf hy hr hproto hp]

/-- Any actual program point, with any canonical response signs, contributes
at most B in absolute value to a core edge. -/
theorem point_coefficient_bound {N O : ℕ} (ys : Fin O → ℚ) (p c b : Point) :
    |RankResponse.coreCoefficient (B:=N) ys p c b|≤(N:ℤ) := by
  classical
  unfold RankResponse.coreCoefficient
  apply signed_row_bound
  intro k
  unfold RankResponse.responseSpin
  split <;> norm_num


/-- True zero coefficient for every placed ordinary fan whose core edge
avoids the parent cluster, including short edges in another cluster. -/
theorem placed_nonincident_coefficient_zero {N O cut : ℕ} (d : Geometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀k, frame (frameParameter N k)∈B)
    (hr : ordinary d.a d.mu∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (ordinary d.a d.mu) p)
    (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcurve : 1200*d.mu < |c-d.a| * |b-d.a|)
    (hcMem : original c∈B) (hbMem : original b∈B) :
    RankResponse.coreCoefficient (B:=N) d.ys p (original c) (original b)=0 := by
  classical
  unfold RankResponse.coreCoefficient
  apply Finset.sum_eq_zero
  intro k _
  have hno := OrdinaryNonincident.placed_ordinary_nonincident_no_cross M B R d.a c b d.mu
    (frameParameter N k) p d.unit_a hc hb (frameParameter_unit N k).le d.mu_pos hcurve
    (hf k) hcMem hbMem hr hproto hp
  simp [hno]

/-- Parent-block short edges are actually missed by all placed ordinary fans;
the proof uses the same-ray exclusion, not a half-frame formula. -/
theorem placed_parent_coefficient_zero {N O cut : ℕ} (d : Geometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀k, frame (frameParameter N k)∈B)
    (hr : ordinary d.a d.mu∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (ordinary d.a d.mu) p)
    (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcloneC : 3*((N:ℚ)+1)*|c-d.a|≤d.mu) (hcloneB : 3*((N:ℚ)+1)*|b-d.a|≤d.mu)
    (hcMem : original c∈B) (hbMem : original b∈B) :
    RankResponse.coreCoefficient (B:=N) d.ys p (original c) (original b)=0 := by
  classical
  unfold RankResponse.coreCoefficient
  apply Finset.sum_eq_zero
  intro k _
  have hno := ParentBlockExclusion.placed_ordinary_parent_block M N B R d.even k d.a c b d.mu p
    d.unit_a hc hb d.mu_pos d.mu_le hcloneC hcloneB (hf k) hcMem hbMem hr hproto hp
  simp [hno]

end Q4.Candidate.PlacedOrdinaryField
#print axioms Q4.Candidate.PlacedOrdinaryField.ordinary_response
#print axioms Q4.Candidate.PlacedOrdinaryField.placed_field_eq
#print axioms Q4.Candidate.PlacedOrdinaryField.placed_response_eq
#print axioms Q4.Candidate.PlacedOrdinaryField.placed_incident_coefficient
#print axioms Q4.Candidate.PlacedOrdinaryField.point_coefficient_bound

#print axioms Q4.Candidate.PlacedOrdinaryField.placed_nonincident_coefficient_zero
#print axioms Q4.Candidate.PlacedOrdinaryField.placed_parent_coefficient_zero
