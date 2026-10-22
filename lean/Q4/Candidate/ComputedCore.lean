import Q4.Candidate.ComputedBackground
import Q4.Candidate.CoreValueBridge

/-! Executable rational palette/free-unary baseline. No optimization over
source or dummy colorings occurs in this finite expression. -/
namespace Q4.Candidate.ComputedCore
open Q4.Candidate.CompleteDrawing Q4.Candidate.CompleteClassEnergy
open Q4.Candidate.ConvexSeparation Q4.Candidate.ProposedPalette
open Q4.Candidate.ComputedBackground
open scoped BigOperators
variable {O B P S : ℕ}

instance allowedDecidable (a b : Site S) : Decidable (allowed a b) := by
  cases a <;> cases b <;> unfold allowed <;> infer_instance

def chosen (site : Fin O → Site S) (e : Inner O) : Bool :=
  decide (allowed (site e.val.1) (site e.val.2))

theorem chosen_iff (site : Fin O → Site S) (e : Inner O) :
    chosen site e=true ↔ e∈palette site := by simp [chosen,palette]

def paletteCost (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (e : Inner O) (bit : Bool) : ℚ :=
  ∑f : Inner O, if chosen site f then atom ys ts rs (C e) (C f) bit (paletteBit site f) else 0

def fanUnary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (tau : Fin B×Fin P → Bool) (e : Inner O) (bit : Bool) : ℚ :=
  ∑t, atom ys ts rs (C e) (T t) bit (tau t)

def unary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) (e : Inner O) (bit : Bool) : ℚ :=
  paletteCost ys ts rs site e bit+fanUnary ys ts rs tau e bit

def baseline (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) : ℚ :=
  (∑e : Inner O, ∑f : Inner O, if chosen site e && chosen site f then
    atom ys ts rs (C e) (C f) (paletteBit site e) (paletteBit site f) else 0)/2+
  ∑e : Inner O, if chosen site e then fanUnary ys ts rs tau e (paletteBit site e) else 0

def baseFloor (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) : ℚ :=
  baseline ys ts rs site tau+
  ∑e : Inner O, if chosen site e then 0 else min (unary ys ts rs site tau e false) (unary ys ts rs site tau e true)

theorem paletteCost_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (e : Inner O) (bit : Bool) :
    (paletteCost ys ts rs site e bit:ℝ)=(globalCost ys site e.val.1 e.val.2 bit:ℝ) := by
  unfold paletteCost globalCost palette
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  have hx : Cross ys ts rs (C e) (C f) ↔
      OriginalCapAlternation.cross ys e.val.1 e.val.2 f.val.1 f.val.2 := Iff.rfl
  simp only [chosen,decide_eq_true_eq,ComputedBackground.atom,hx]
  split_ifs <;> simp_all [paletteBit]

theorem fanUnary_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) (e : Inner O) (bit : Bool) :
    (fanUnary ys ts rs tau e bit:ℝ)=
      coreUnary ys ts rs (CoreValueBridge.reference site tau) e bit := by
  unfold fanUnary coreUnary
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [atom_cast]
  rfl

theorem unary_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) (e : Inner O) (bit : Bool) :
    (unary ys ts rs site tau e bit:ℝ)=CoreValueBridge.unary ys ts rs site tau e bit := by
  unfold unary CoreValueBridge.unary CoreFixedPalette.freeUnary
  rw [Rat.cast_add,paletteCost_cast,fanUnary_cast]

theorem baseline_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) :
    (baseline ys ts rs site tau:ℝ)=CoreValueBridge.baseline ys ts rs site tau := by
  unfold baseline CoreValueBridge.baseline CoreFixedPalette.paletteBaseline halfSum
  rw [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat]
  congr 1
  · congr 1
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro f _
    simp only [Bool.and_eq_true,chosen_iff]
    by_cases he : e∈palette site <;> by_cases hf : f∈palette site
    · simp only [he,hf,and_self,ite_true,atom_cast]
      rfl
    · simp [he,hf]
    · simp [he,hf]
    · simp [he,hf]
  · rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [chosen_iff]
    by_cases he : e∈palette site
    · simp only [he,ite_true,fanUnary_cast ys ts rs site]
      rfl
    · simp [he]

/-- Equality of the executable rational expression with the complete-core
baseline used in the proof, including every palette and CT contribution. -/
theorem baseFloor_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) :
    (baseFloor ys ts rs site tau:ℝ)=CoreValueBridge.baseFloor ys ts rs site tau := by
  unfold baseFloor CoreValueBridge.baseFloor CoreExtension.unaryFloor
  simp only [Rat.cast_add,baseline_cast,Rat.cast_sum,chosen_iff]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e∈palette site
  · simp [he]
  · simp only [he,ite_false,not_false_eq_true,ite_true,Rat.cast_min,unary_cast]

end Q4.Candidate.ComputedCore
#print axioms Q4.Candidate.ComputedCore.paletteCost_cast
#print axioms Q4.Candidate.ComputedCore.unary_cast
#print axioms Q4.Candidate.ComputedCore.baseline_cast
#print axioms Q4.Candidate.ComputedCore.baseFloor_cast
