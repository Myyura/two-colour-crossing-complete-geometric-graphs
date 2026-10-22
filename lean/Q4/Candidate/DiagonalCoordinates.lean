import Q4.Candidate.IntervalPoincare
import Mathlib.MeasureTheory.Group.Prod

/-! Actual measure-preserving diagonal coordinates (s,u) ↦ (u,s-u),
and the exact variable interval cut out by the interior square. No Jacobian
or short-segment normalization is postulated.
-/

open MeasureTheory Set

namespace Q4.Candidate.DiagonalCoordinates

abbrev Point := ℝ × ℝ

def diagonalEquiv : Point ≃ᵐ Point where
  toFun p := (p.2,p.1-p.2)
  invFun p := (p.1+p.2,p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := measurable_snd.prodMk (measurable_fst.sub measurable_snd)
  measurable_invFun := (measurable_fst.add measurable_snd).prodMk measurable_fst

theorem diagonal_preserving : MeasurePreserving diagonalEquiv volume volume := by
  change MeasurePreserving (fun p : Point => (p.2,p.1-p.2))
    ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume)
  simpa only [sub_eq_add_neg, add_comm] using
    (measurePreserving_prod_neg_add_swap (volume : Measure ℝ) volume)

theorem diagonal_integral (G : Point → ℝ) (hG : Integrable G) :
    (∫ p, G p) = ∫ s : ℝ, ∫ u : ℝ, G (u,s-u) := by
  have hi := (diagonal_preserving.integrable_comp hG.aestronglyMeasurable).mpr hG
  have he := diagonal_preserving.integral_comp' G
  rw [←he]
  exact integral_prod _ hi

def interior (h : ℝ) : Set Point := Icc h (1-h) ×ˢ Icc h (1-h)
def lower (h s : ℝ) : ℝ := max h (s-(1-h))
def upper (h s : ℝ) : ℝ := min (1-h) (s-h)

theorem fiber_membership (h s u : ℝ) :
    (u,s-u) ∈ interior h ↔ u ∈ Icc (lower h s) (upper h s) := by
  simp only [interior, lower, upper, mem_prod, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    exact ⟨⟨h1,by linarith⟩,⟨h2,by linarith⟩⟩
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    exact ⟨⟨h1,h3⟩,⟨by linarith,by linarith⟩⟩

theorem fiber_length_bound (h s : ℝ) (hh : 0 ≤ h) : upper h s-lower h s ≤ 1 := by
  have hl : h ≤ lower h s := le_max_left _ _
  have hu : upper h s ≤ 1-h := min_le_left _ _
  linarith

theorem interior_diagonal_integral (G : Point → ℝ) (h : ℝ)
    (hG : IntegrableOn G (interior h)) :
    (∫ p in interior h, G p) = ∫ s : ℝ, ∫ u in Icc (lower h s) (upper h s), G (u,s-u) := by
  have hQ : MeasurableSet (interior h) := measurableSet_Icc.prod measurableSet_Icc
  have hi := hG.integrable_indicator hQ
  rw [←integral_indicator hQ, diagonal_integral _ hi]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with u
  classical
  by_cases hu : u ∈ Icc (lower h s) (upper h s)
  · rw [indicator_of_mem hu,indicator_of_mem ((fiber_membership h s u).mpr hu)]
  · rw [indicator_of_notMem hu,indicator_of_notMem (mt (fiber_membership h s u).mp hu)]

end Q4.Candidate.DiagonalCoordinates

#print axioms Q4.Candidate.DiagonalCoordinates.diagonal_preserving
#print axioms Q4.Candidate.DiagonalCoordinates.diagonal_integral
#print axioms Q4.Candidate.DiagonalCoordinates.fiber_membership
#print axioms Q4.Candidate.DiagonalCoordinates.interior_diagonal_integral
