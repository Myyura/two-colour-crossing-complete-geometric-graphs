import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! The genuine atomless probability measure for candidate §2. Endpoint zero
has zero Lebesgue mass, so (0,1] and [0,1] are the same measure. -/

open MeasureTheory Set

namespace Q4.Candidate.UnitIntervalMeasure

noncomputable def unit : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

instance unit_probability : IsProbabilityMeasure unit := by
  constructor
  simp [unit]

instance unit_atomless : NullSingletonClass unit := by
  dsimp [unit]
  infer_instance

theorem unit_eq_closed_interval : unit = volume.restrict (Icc (0 : ℝ) 1) :=
  Measure.restrict_congr_set Ioc_ae_eq_Icc

theorem zero_left_mass : unit.real (Iic (0 : ℝ)) = 0 := by
  have he : Iic (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
    intro hx hxa _
    exact not_lt_of_ge hx hxa
  simp only [unit, measureReal_restrict_apply measurableSet_Iic, he, measureReal_empty]

theorem zero_right_mass : unit.real (Ioi (1 : ℝ)) = 0 := by
  have he : Ioi (1 : ℝ) ∩ Ioc (0 : ℝ) 1 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
    intro hx _ hxb
    exact not_lt_of_ge hxb hx
  simp only [unit, measureReal_restrict_apply measurableSet_Ioi, he, measureReal_empty]

end Q4.Candidate.UnitIntervalMeasure

#print axioms Q4.Candidate.UnitIntervalMeasure.unit_probability
#print axioms Q4.Candidate.UnitIntervalMeasure.unit_atomless
#print axioms Q4.Candidate.UnitIntervalMeasure.unit_eq_closed_interval
#print axioms Q4.Candidate.UnitIntervalMeasure.zero_left_mass
#print axioms Q4.Candidate.UnitIntervalMeasure.zero_right_mass
