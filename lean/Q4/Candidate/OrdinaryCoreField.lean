import Q4.Candidate.OrdinaryResponse
import Q4.Candidate.OrdinaryNonincident

/-! The genuine frozen ordinary-fan unary cost on original-original core
segments. All incidences below are strict rational ProperCross predicates. -/
open scoped BigOperators
namespace Q4.Candidate.OrdinaryCoreField
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.OrdinaryFan Q4.Candidate.OrdinaryNonincident
open Q4.Candidate.OrdinaryResponse
open Q4.Candidate.VirtualColumnField
attribute [local instance] Classical.propDecidable

noncomputable def coreCost {B O r : ℕ} (d : Geometry B O r) (c b : ℚ) (color : Bool) : ℤ := by
  classical
  exact ∑ k : Fin B, if ProperCross (ordinary d.a d.mu) (frame (frameParameter B k))
    (original c) (original b) then (if color=response d k then 1 else 0) else 0

noncomputable def coreCoefficient {B O r : ℕ} (d : Geometry B O r) (c b : ℚ) : ℤ := by
  classical
  exact ∑ k : Fin B, if ProperCross (ordinary d.a d.mu) (frame (frameParameter B k))
    (original c) (original b) then (if response d k then 1 else -1) else 0

theorem core_cost_difference {B O r : ℕ} (d : Geometry B O r) (c b : ℚ) :
    coreCost d c b true-coreCost d c b false=coreCoefficient d c b := by
  classical
  unfold coreCost coreCoefficient
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : ProperCross (ordinary d.a d.mu) (frame (frameParameter B k)) (original c) (original b) <;>
    cases hr : response d k <;> simp [hc]

theorem coreCoefficient_cast {B O r : ℕ} (d : Geometry B O r) (c b : ℚ) :
    (coreCoefficient d c b:ℝ) = ∑ k : Fin B,
      if ProperCross (ordinary d.a d.mu) (frame (frameParameter B k)) (original c) (original b)
      then responseSpin d k else 0 := by
  classical
  unfold coreCoefficient responseSpin
  push_cast
  rfl

theorem coefficient_bound {B O r : ℕ} (d : Geometry B O r) (c b : ℚ) :
    |coreCoefficient d c b|≤(B:ℤ) := by
  classical
  apply signed_row_bound
  intro k
  cases h : response d k <;> norm_num [h]

theorem coefficient_symm {B O r : ℕ} (d : Geometry B O r) (c b : ℚ) :
    coreCoefficient d c b=coreCoefficient d b c := by
  classical
  unfold coreCoefficient
  apply Finset.sum_congr rfl
  intro k _
  have he : ProperCross (ordinary d.a d.mu) (frame (frameParameter B k)) (original c) (original b) ↔
      ProperCross (ordinary d.a d.mu) (frame (frameParameter B k)) (original b) (original c) :=
    (properCross_swap_edges _ _ _ _).trans
      ((properCross_reverse_first _ _ _ _).trans (properCross_swap_edges _ _ _ _))
  rw [he]

theorem incident_coefficient {B O r : ℕ} (d : Geometry B O r) (c b : ℚ)
    (hc : |c|≤1) (hb : |b|≤1)
    (hclone : 3*((B:ℚ)+1)*|c-d.a|≤d.mu) (hsep : 5*d.mu≤|b-d.a|) :
    (coreCoefficient d c b:ℝ) =
      if d.a<b then (∑ k : Fin B, if k.val<B/2 then responseSpin d k else 0)
      else (∑ k : Fin B, if B/2≤k.val then responseSpin d k else 0) := by
  classical
  have hne : b≠d.a := by
    intro h
    rw [h,sub_self,abs_zero] at hsep
    linarith [d.mu_pos]
  rw [coreCoefficient_cast]
  simp_rw [ordinary_clone_core_indexed B d.even _ d.a c b d.mu d.unit_a hc hb
    d.mu_pos d.mu_le hclone hsep]
  by_cases hab : d.a<b
  · simp [hab,show ¬b<d.a by linarith]
  · have hba : b<d.a := lt_of_le_of_ne (le_of_not_gt hab) hne
    simp [hab,hba]

theorem early_incident_coefficient {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (h8 : 8∣B)
    (hW : (d.parent.card:ℝ)/O≤1/514) (hearly : (r:ℝ)/O≤1/514)
    (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hclone : 3*((B:ℚ)+1)*|c-d.a|≤d.mu) (hsep : 5*d.mu≤|b-d.a|) :
    (B:ℝ)/4≤(coreCoefficient d c b:ℝ) ∧ (coreCoefficient d c b:ℝ)≤B := by
  have hw := early_half_weights d hO hBO hr h8 hW hearly
  have hbound : |(coreCoefficient d c b:ℝ)|≤B := by exact_mod_cast coefficient_bound d c b
  constructor
  · rw [incident_coefficient d c b hc hb hclone hsep]
    split
    · exact hw.1
    · exact hw.2.1
  · exact (abs_le.mp hbound).2

theorem late_incident_coefficient {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (h8 : 8∣B)
    (hW : (d.parent.card:ℝ)/O≤1/514) (hlate : 1-1/514≤(r:ℝ)/O)
    (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hclone : 3*((B:ℚ)+1)*|c-d.a|≤d.mu) (hsep : 5*d.mu≤|b-d.a|) :
    -(B:ℝ)≤(coreCoefficient d c b:ℝ) ∧ (coreCoefficient d c b:ℝ)≤ -(B:ℝ)/4 := by
  have hw := late_half_weights d hO hBO hr h8 hW hlate
  have hbound : |(coreCoefficient d c b:ℝ)|≤B := by exact_mod_cast coefficient_bound d c b
  constructor
  · exact (abs_le.mp hbound).1
  · rw [incident_coefficient d c b hc hb hclone hsep]
    split
    · exact hw.1
    · exact hw.2.1

theorem nonincident_coefficient_zero {B O r : ℕ} (d : Geometry B O r)
    (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcurve : 1200*d.mu < |c-d.a| * |b-d.a|) :
    coreCoefficient d c b=0 := by
  classical
  unfold coreCoefficient
  apply Finset.sum_eq_zero
  intro k _
  have hno := ordinary_nonincident_no_cross d.a c b d.mu (frameParameter B k)
    d.unit_a hc hb (le_of_lt (frameParameter_unit B k)) d.mu_pos hcurve
  simp [hno]

theorem incident_rank_independent {B O r : ℕ} (d : Geometry B O r)
    (c c' b b' : ℚ) (hc : |c|≤1) (hc' : |c'|≤1) (hb : |b|≤1) (hb' : |b'|≤1)
    (hclone : 3*((B:ℚ)+1)*|c-d.a|≤d.mu) (hclone' : 3*((B:ℚ)+1)*|c'-d.a|≤d.mu)
    (hsep : 5*d.mu≤|b-d.a|) (hsep' : 5*d.mu≤|b'-d.a|)
    (hside : d.a<b ↔ d.a<b') :
    coreCoefficient d c b=coreCoefficient d c' b' := by
  have h1 := incident_coefficient d c b hc hb hclone hsep
  have h2 := incident_coefficient d c' b' hc' hb' hclone' hsep'
  simp only [hside] at h1
  exact_mod_cast h1.trans h2.symm

end Q4.Candidate.OrdinaryCoreField
#print axioms Q4.Candidate.OrdinaryCoreField.core_cost_difference
#print axioms Q4.Candidate.OrdinaryCoreField.incident_coefficient
#print axioms Q4.Candidate.OrdinaryCoreField.early_incident_coefficient
#print axioms Q4.Candidate.OrdinaryCoreField.late_incident_coefficient
#print axioms Q4.Candidate.OrdinaryCoreField.nonincident_coefficient_zero
#print axioms Q4.Candidate.OrdinaryCoreField.incident_rank_independent
