import Q4.Candidate.AntiperiodicReplacement

/-! The actual continuous strict diagonal coloring attains 1/12.
This provides the finite-grid comparison coloring with an exact reference
energy rather than an assumed sharpness statement. -/
open MeasureTheory Set

namespace Q4.Candidate.CanonicalEnergy
open Q4.Candidate.UnitIntervalMeasure Q4.Candidate.AlternationKernel
open Q4.Candidate.ComparisonEnergy Q4.Candidate.DiagonalHalves
open Q4.Candidate.AntiperiodicThreshold

theorem strict_threshold_no_alternations (o : Bool) (c : ℝ) :
    AlternatingTriples.alternating (fun x => if x<c then o else !o) = ∅ := by
  ext p
  simp only [AlternatingTriples.alternating,mem_ofPred_eq,mem_empty_iff_false,iff_false]
  rintro ⟨hxy,hyz,hxz,hxycol⟩
  by_cases hx : p.1 < c <;> by_cases hy : p.2.1 < c <;> by_cases hz : p.2.2 < c
  all_goals
    simp only [hx,hy,hz,ite_true,ite_false] at hxz hxycol
    first | exact hxycol rfl | cases o <;> contradiction | linarith

theorem strict_threshold_norm (o : Bool) (c : ℝ) :
    normSq unit (fun x => if x<c then o else !o) = 1/3 := by
  have hm : Measurable (fun x : ℝ => if x<c then o else !o) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  rw [kernel_identity unit _ hm]
  simp [AlternatingTriples.tripleMass,strict_threshold_no_alternations]

theorem canonical_row_norm (o : Bool) : rowNormSq unit (canonical o) = 1/3 := by
  have hf := AntiperiodicReplacement.canonical_measurable o
  unfold rowNormSq
  rw [integral_prod_symm _ (rowSq_integrable unit _ hf)]
  have he (v : ℝ) : (∫ u, (rowOp unit (canonical o) (u,v))^2 ∂unit) = 1/3 := by
    change normSq unit (fun u => canonical o (u,v)) = _
    have hid : (fun u => canonical o (u,v)) = (fun u => if u<1-v then o else !o) := by
      funext u
      have he : u+v<1 ↔ u<1-v := by constructor <;> intro h <;> linarith
      simp only [canonical,he]
    rw [hid]
    exact strict_threshold_norm o (1-v)
  simp_rw [he]
  simp

theorem canonical_col_norm (o : Bool) : colNormSq unit (canonical o) = 1/3 := by
  have hf := AntiperiodicReplacement.canonical_measurable o
  unfold colNormSq
  rw [integral_prod _ (colSq_integrable unit _ hf)]
  have he (u : ℝ) : (∫ v, (colOp unit (canonical o) (u,v))^2 ∂unit) = 1/3 := by
    change normSq unit (fun v => canonical o (u,v)) = _
    have hid : (fun v => canonical o (u,v)) = (fun v => if v<1-u then o else !o) := by
      funext v
      have he : u+v<1 ↔ v<1-u := by constructor <;> intro h <;> linarith
      simp only [canonical,he]
    rw [hid]
    exact strict_threshold_norm o (1-u)
  simp_rw [he]
  simp

theorem canonical_mean (o : Bool) : mean unit (canonical o) = 0 := by
  have he := anti_mean (fun _ => o) measurable_const
  change mean unit (canonical o) = _ at he
  rw [he,intervalIntegral.integral_mul_const]
  have hi : (∫ s in (0:ℝ)..1, (2*s-1)) = 0 := by
    have hlin : IntervalIntegrable (fun s : ℝ => 2*s) volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hlin
      (intervalIntegrable_const (c := (1:ℝ))),intervalIntegral.integral_const_mul,
      integral_id,intervalIntegral.integral_const]
    norm_num
  rw [hi,zero_mul]

theorem canonical_difference (o : Bool) : differenceSq unit (canonical o) = 0 := by
  have he := differenceSq_eq_twice_variance (fun _ => o) (fun _ => !o)
    measurable_const measurable_const
  change differenceSq unit (canonical o) = _ at he
  have hF : F (fun _ => o) (fun _ => !o) = fun _ => 0 := by
    funext t
    simp [F,spin_not]
  simp only [hF,integral_zero,sub_self,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
    zero_pow,mul_zero] at he
  exact he

/-- Actual attainment of the sharp continuous lower bound by both phases. -/
theorem canonical_energy (o : Bool) : energy unit (canonical o) = 1/12 := by
  have he := deficit_identity unit (canonical o) (AntiperiodicReplacement.canonical_measurable o)
  rw [canonical_mean,canonical_difference,canonical_row_norm,canonical_col_norm] at he
  linarith

end Q4.Candidate.CanonicalEnergy

#print axioms Q4.Candidate.CanonicalEnergy.strict_threshold_no_alternations
#print axioms Q4.Candidate.CanonicalEnergy.canonical_row_norm
#print axioms Q4.Candidate.CanonicalEnergy.canonical_mean
#print axioms Q4.Candidate.CanonicalEnergy.canonical_difference
#print axioms Q4.Candidate.CanonicalEnergy.canonical_energy
