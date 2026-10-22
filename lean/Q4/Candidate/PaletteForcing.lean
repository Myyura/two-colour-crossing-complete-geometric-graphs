import Q4.Candidate.CoreEncoding
import Q4.Candidate.ProbeFreezing
import Q4.Candidate.OrdinaryCoreField

/-! Exact palette-forcing mechanism on the actual finite core objective.
Frozen fan costs are counted one incident neighbor at a time. All unfrozen
core colors remain arbitrary in the single-flip theorem. No optimum identity
or precolored-palette hypothesis is used to establish forcing. -/
namespace Q4.Candidate.PaletteForcing
open Q4.SimultaneousFlip
open Q4.JointProbe (spin neighborhood monoCount_single_difference)
open Q4.Candidate.ProbeFreezing (neighbors neighborhood_eq_sum spin_sum_bounds)
variable {α : Type u} {β : Type v} [DecidableEq α]

def frozenUnary (fans : List β) (inc : α → β → Bool) (τ : β → Bool) (v : α) (b : Bool) : ℤ :=
  intSum fans (fun f => if inc v f then same b (τ f) else 0)

def frozenField (fans : List β) (inc : α → β → Bool) (τ : β → Bool) (v : α) : ℤ :=
  intSum fans (fun f => if inc v f then spin (τ f) else 0)

def coreEnergy (vs : List α) (es : List (α × α)) (fans : List β)
    (inc : α → β → Bool) (τ : β → Bool) (χ : α → Bool) : ℤ :=
  totalEnergy vs es (frozenUnary fans inc τ) χ

omit [DecidableEq α] in
theorem frozenField_cost_difference (fans : List β) (inc : α → β → Bool) (τ : β → Bool) (v : α) :
    frozenUnary fans inc τ v true-frozenUnary fans inc τ v false=frozenField fans inc τ v := by
  unfold frozenUnary frozenField
  rw [←intSum_sub]
  apply intSum_congr
  intro f _
  cases hi : inc v f <;> cases ht : τ f <;> simp [same,spin]

theorem core_flip_identity (vs : List α) (es : List (α × α)) (fans : List β)
    (inc : α → β → Bool) (τ : β → Bool) (χ : α → Bool) (v : α)
    (hn : vs.Nodup) (hv : v∈vs) (hloop : ∀e∈es, e.1≠e.2) :
    coreEnergy vs es fans inc τ (flipOne χ v)-coreEnergy vs es fans inc τ χ =
      -spin (χ v)*(frozenField fans inc τ v+neighborhood es χ v) := by
  have hu := unary_single_identity vs (frozenUnary fans inc τ) χ v hn hv
  have hp := monoCount_single_difference es χ v hloop
  have hg : unaryGain (frozenUnary fans inc τ) χ v = -spin (χ v)*frozenField fans inc τ v := by
    have h := frozenField_cost_difference fans inc τ v
    cases hc : χ v <;> simp only [unaryGain,hc,Bool.not_false,Bool.not_true,spin,
      Bool.false_eq_true,ite_false,ite_true,neg_neg,one_mul,neg_mul] <;> omega
  rw [hg] at hu
  unfold coreEnergy totalEnergy
  rw [edgeEnergy_eq_monoCount,edgeEnergy_eq_monoCount]
  nlinarith

theorem core_neighbor_bound (es : List (α × α)) (χ : α → Bool) (v : α)
    (hloop : ∀e∈es, e.1≠e.2) :
    -((neighbors es v).length:ℤ)≤neighborhood es χ v ∧
      neighborhood es χ v≤(neighbors es v).length := by
  rw [neighborhood_eq_sum es χ v hloop]
  exact spin_sum_bounds _ _

/-- A wrong palette bit strictly improves regardless of every other core
color. The dominance compares actual frozen-neighbor cost difference against
all remaining actual core neighbors, rather than against a proposed palette. -/
theorem wrong_palette_improves (vs : List α) (es : List (α × α)) (fans : List β)
    (inc : α → β → Bool) (τ : β → Bool) (χ : α → Bool) (v : α) (b : Bool)
    (hn : vs.Nodup) (hv : v∈vs) (hloop : ∀e∈es, e.1≠e.2)
    (hdom : ((neighbors es v).length:ℤ)<if b then -frozenField fans inc τ v else frozenField fans inc τ v)
    (hwrong : χ v≠b) :
    coreEnergy vs es fans inc τ (flipOne χ v)<coreEnergy vs es fans inc τ χ := by
  have hid := core_flip_identity vs es fans inc τ χ v hn hv hloop
  have hb := core_neighbor_bound es χ v hloop
  cases b <;> cases hc : χ v <;> simp_all [spin] <;> omega

/-- Every minimizer agrees simultaneously on the entire designated palette.
The local argument never fixes another core color, so this is not circular. -/
theorem every_minimizer_palette (vs : List α) (es : List (α × α)) (fans : List β)
    (inc : α → β → Bool) (τ : β → Bool) (P : List α) (palette : α → Bool)
    (hn : vs.Nodup) (hP : ∀v∈P, v∈vs) (hloop : ∀e∈es, e.1≠e.2)
    (hdom : ∀v∈P, ((neighbors es v).length:ℤ)<
      if palette v then -frozenField fans inc τ v else frozenField fans inc τ v)
    (χ : α → Bool) (hmin : ∀ψ, coreEnergy vs es fans inc τ χ≤coreEnergy vs es fans inc τ ψ) :
    ∀v∈P, χ v=palette v := by
  intro v hv
  by_contra hbad
  have hstrict := wrong_palette_improves vs es fans inc τ χ v (palette v) hn (hP v hv)
    hloop (hdom v hv) hbad
  exact (not_lt_of_ge (hmin (flipOne χ v))) hstrict

/-- Computable upward rounding of a rational target by an actual positive
integer response weight (viewed as a rational). -/
def multiplicity (target weight : ℚ) : ℕ := Nat.ceil (target/weight)

theorem multiplicity_bounds (target weight : ℚ) (ht : 0≤target) (hw : 0<weight) :
    target≤(multiplicity target weight:ℚ)*weight ∧
      (multiplicity target weight:ℚ)*weight<target+weight := by
  have hlo := Nat.le_ceil (target/weight)
  have hhi := Nat.ceil_lt_add_one (div_nonneg ht (le_of_lt hw))
  constructor
  · exact (div_le_iff₀ hw).mp hlo
  · have h := mul_lt_mul_of_pos_right hhi hw
    have he : (target/weight+1)*weight=target+weight := by field_simp
    rw [he] at h
    exact h

def roundingError (target weight : ℚ) : ℚ := (multiplicity target weight:ℚ)*weight-target

theorem roundingError_bounds (target weight B : ℚ) (ht : 0≤target) (hw : 0<weight) (hwB : weight≤B) :
    0≤roundingError target weight ∧ roundingError target weight<B := by
  have h := multiplicity_bounds target weight ht hw
  unfold roundingError
  constructor <;> linarith

end Q4.Candidate.PaletteForcing
#print axioms Q4.Candidate.PaletteForcing.frozenField_cost_difference
#print axioms Q4.Candidate.PaletteForcing.core_flip_identity
#print axioms Q4.Candidate.PaletteForcing.wrong_palette_improves
#print axioms Q4.Candidate.PaletteForcing.every_minimizer_palette
#print axioms Q4.Candidate.PaletteForcing.multiplicity_bounds
