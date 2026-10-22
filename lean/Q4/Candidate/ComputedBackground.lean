import Q4.Candidate.CompleteBackground

/-! Executable rational evaluation of the common grid/TT/II background.
The grid term evaluates the canonical colouring and single-vertex differences;
it does not search colourings. The known frame optimum is a rational input,
separate from its lower-bound/attainment certificate. -/
namespace Q4.Candidate.ComputedBackground
open Q4.Candidate.CompleteDrawing Q4.Candidate.ConvexSeparation
open Q4.Candidate.CompleteClassEnergy
variable {O B P : ℕ}

instance crossDecidable (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e f : Edge O B P) : Decidable (Cross ys ts rs e f) := by
  unfold Cross ProperCross
  infer_instance

def canonical (x : Fin B × Fin O) : Bool :=
  decide ((((x.1:ℚ)+1/2)/B)+(((x.2:ℚ)+1/2)/O)<1)

def field (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e : Edge O B P) : ℤ :=
  ∑ x : Fin B × Fin O, if Cross ys ts rs e (.inl x)
    then Q4.JointProbe.spin (canonical x) else 0

def fans (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (t : Fin B × Fin P) : Bool := decide (field ys ts rs (T t)<0)

def atom (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e f : Edge O B P) (c d : Bool) : ℚ := if Cross ys ts rs e f ∧ c=d then 1 else 0

def unary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (x : Fin B × Fin O) (c : Bool) : ℚ :=
  ∑ t, atom ys ts rs (.inl x) (T t) c (τ t)

def gridMono (ξ : Fin B × Fin O → Bool) : ℚ :=
  ∑ p : (Fin B × Fin O) × (Fin B × Fin O),
    if (p.1.1<p.2.1 ∧ p.1.2<p.2.2) ∧ ξ p.1=ξ p.2 then 1 else 0

def gridValue (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (ξ : Fin B × Fin O → Bool) : ℚ :=
  (∑ x, unary ys ts rs τ x (ξ x))+gridMono ξ

def delta (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (ξ : Fin B × Fin O → Bool) (v : Fin B × Fin O) : ℚ :=
  gridValue ys ts rs τ (Q4.SimultaneousFlip.flipOne ξ v)-gridValue ys ts rs τ ξ

def phaseValue (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) : ℚ :=
  gridValue ys ts rs (fans ys ts rs) canonical+
    ∑ v, min 0 (delta ys ts rs (fans ys ts rs) canonical v)

def fanValue (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) : ℚ :=
  (∑ t, ∑ u, atom ys ts rs (T t) (T u) (fans ys ts rs t) (fans ys ts rs u))/2

def background (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) (z : ℚ) : ℚ :=
  phaseValue ys ts rs+fanValue ys ts rs+z

theorem canonical_eq (x : Fin B × Fin O) :
    canonical x=CanonicalField.phase false x := by
  have h : ((((x.1:ℚ)+1/2)/B)+(((x.2:ℚ)+1/2)/O)<1) ↔
      GridCounts.u B x.1+GridCounts.u O x.2<1 := by
    rw [← Rat.cast_lt (K:=ℝ)]
    push_cast
    rfl
  simp only [canonical,CanonicalField.phase,Bool.false_eq_true,ite_false,
    CanonicalField.canonical,h]

theorem field_eq (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e : Edge O B P) : field ys ts rs e=CompleteProbeFreezing.field ys ts rs false e := by
  rw [CompleteProbeFreezing.field_eq_sum]
  simp only [field,canonical_eq]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : Cross ys ts rs e (.inl x) <;> simp [h]

theorem fans_eq (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    fans ys ts rs=CompleteBackground.frozenFans ys ts rs false := by
  funext t
  simp only [fans,field_eq,CompleteBackground.frozenFans,
    CompleteProbeFreezing.frozenColor,Bool.false_eq_true,ite_false,ProbeFreezing.canonicalResponse]

theorem atom_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e f : Edge O B P) (c d : Bool) :
    (atom ys ts rs e f c d:ℝ)=CompleteBackground.atom ys ts rs e f c d := by
  simp only [atom,CompleteBackground.atom]
  split <;> simp

theorem unary_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (x : Fin B × Fin O) (c : Bool) :
    (unary ys ts rs τ x c:ℝ)=CompleteBackground.fanUnary ys ts rs τ x c := by
  simp only [unary,CompleteBackground.fanUnary,Rat.cast_sum,atom_cast]

theorem gridMono_cast (ξ : Fin B × Fin O → Bool) :
    (gridMono ξ:ℝ)=(Q4.monoCount (GridLocalization.gridEdges B O) ξ:ℝ) := by
  unfold gridMono GridLocalization.gridEdges
  rw [GridStepBridge.monoCount_list_sum,Finset.sum_map_toList,GridCounts.orientedEdges,
    Finset.sum_filter,Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases ho : p.1.1<p.2.1 ∧ p.1.2<p.2.2 <;>
    by_cases hc : ξ p.1=ξ p.2 <;> simp [ho,hc]

theorem gridValue_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (ξ : Fin B × Fin O → Bool) :
    (gridValue ys ts rs τ ξ:ℝ)=CompleteBackground.gridValue ys ts rs τ ξ := by
  simp only [gridValue,Rat.cast_add,Rat.cast_sum,unary_cast,gridMono_cast,
    CompleteBackground.gridValue,GridLocalization.energy,GridLocalization.gridVertices,
    CompleteGridEnergy.realSum_toList]

theorem delta_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (ξ : Fin B × Fin O → Bool) (v : Fin B × Fin O) :
    (delta ys ts rs τ ξ v:ℝ)=GridLocalization.delta
      (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
      (CompleteBackground.fanUnary ys ts rs τ) ξ v := by
  simp only [delta,Rat.cast_sub,gridValue_cast,GridLocalization.delta,CompleteBackground.gridValue]

theorem phaseValue_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    (phaseValue ys ts rs:ℝ)=CompleteBackground.phaseValue ys ts rs false := by
  simp only [phaseValue,Rat.cast_add,Rat.cast_sum,Rat.cast_min,Rat.cast_zero,
    gridValue_cast,delta_cast,fans_eq,CompleteBackground.phaseValue,
    GridLocalization.phaseEstimate,GridLocalization.linearFloor,
    GridLocalization.gridVertices,CompleteGridEnergy.realSum_toList]
  simp only [show (canonical : Fin B × Fin O → Bool)=CanonicalField.phase false from
    funext canonical_eq,CompleteBackground.gridValue,GridLocalization.gridVertices]

theorem fanValue_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    (fanValue ys ts rs:ℝ)=CompleteBackground.fanValue ys ts rs
      (CompleteBackground.frozenFans ys ts rs false) := by
  simp only [fanValue,Rat.cast_div,Rat.cast_sum,Rat.cast_ofNat,atom_cast,fans_eq,
    CompleteBackground.fanValue,halfSum]

/-- Exact agreement between the executable formula and the real common
background in the complete-graph lower and upper bounds. -/
theorem background_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) (z : ℚ) :
    (background ys ts rs z:ℝ)=CompleteBackground.background ys ts rs (z:ℝ) := by
  simp only [background,Rat.cast_add,phaseValue_cast,fanValue_cast,CompleteBackground.background]

#print axioms canonical_eq
#print axioms fans_eq
#print axioms gridValue_cast
#print axioms phaseValue_cast
#print axioms background_cast

end Q4.Candidate.ComputedBackground
