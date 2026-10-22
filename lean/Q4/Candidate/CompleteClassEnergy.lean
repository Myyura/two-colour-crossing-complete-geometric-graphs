import Q4.Candidate.CompleteGridEnergy
import Q4.JointProbe

namespace Q4.Candidate.CompleteClassEnergy

open Q4.Candidate.CompleteDrawing Q4.Candidate.CompleteGridEnergy
open Q4.Candidate.ConvexSeparation
attribute [local instance] Classical.propDecidable

noncomputable def halfSum {α : Type*} [Fintype α] (w : α → α → ℝ) : ℝ :=
  (∑ a, ∑ b, w a b)/2

noncomputable def cutSum {α β : Type*} [Fintype α] [Fintype β] (w : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, w a b

theorem halfSum_sum {α β : Type*} [Fintype α] [Fintype β] (w : α ⊕ β → α ⊕ β → ℝ)
    (hsym : ∀ a b, w a b = w b a) :
    halfSum w = halfSum (fun a b : α => w (.inl a) (.inl b)) +
      cutSum (fun (a : α) (b : β) => w (.inl a) (.inr b)) +
      halfSum (fun a b : β => w (.inr a) (.inr b)) := by
  unfold halfSum cutSum
  rw [Fintype.sum_sum_type]
  have hi (a : α ⊕ β) : (∑ b, w a b) = (∑ b : α, w a (.inl b))+(∑ b : β, w a (.inr b)) :=
    Fintype.sum_sum_type _
  simp_rw [hi]
  simp only [Finset.sum_add_distrib]
  have hc : (∑ b : β, ∑ a : α, w (.inr b) (.inl a)) = ∑ a : α, ∑ b : β, w (.inl a) (.inr b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact hsym _ _
  rw [hc]
  ring

theorem cutSum_sum_right {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (w : α → β ⊕ γ → ℝ) :
    cutSum w = cutSum (fun (a : α) (b : β) => w a (.inl b)) + cutSum (fun (a : α) (c : γ) => w a (.inr c)) := by
  unfold cutSum
  have hi (a : α) : (∑ b, w a b) = (∑ b : β, w a (.inl b))+(∑ c : γ, w a (.inr c)) :=
    Fintype.sum_sum_type _
  simp_rw [hi]
  exact Finset.sum_add_distrib

variable {O B P : Nat}

def T (t : Fin B × Fin P) : Edge O B P := .inr (.inl t)
def C (c : Inner O) : Edge O B P := .inr (.inr (.inl c))
def Y (y : YEdge O P) : Edge O B P := .inr (.inr (.inr (.inl y)))
def I (i : Inner B) : Edge O B P := .inr (.inr (.inr (.inr i)))

noncomputable def coreCost (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : ℝ :=
  halfSum (fun c d : Inner O => weight ys ts rs χ (C c) (C d)) +
  cutSum (fun (c : Inner O) (t : Fin B × Fin P) => weight ys ts rs χ (C c) (T t))

noncomputable def baseCost (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : ℝ :=
  halfSum (fun t u : Fin B × Fin P => weight ys ts rs χ (T t) (T u)) +
  halfSum (fun i j : Inner B => weight ys ts rs χ (I i) (I j))

noncomputable def yRemainder (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : ℝ :=
  cutSum (fun (t : Fin B × Fin P) (y : YEdge O P) => weight ys ts rs χ (T t) (Y y)) +
  cutSum (fun (c : Inner O) (y : YEdge O P) => weight ys ts rs χ (C c) (Y y)) +
  halfSum (fun y z : YEdge O P => weight ys ts rs χ (Y y) (Y z))

theorem weight_nonneg (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (e f : Edge O B P) : 0 ≤ weight ys ts rs χ e f := by
  unfold weight
  split_ifs <;> norm_num

theorem weight_le_one (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (e f : Edge O B P) : weight ys ts rs χ e f ≤ 1 := by
  unfold weight
  split_ifs <;> norm_num

theorem weight_I_zero (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (χ : Edge O B P → Bool) (e : Edge O B P) (he : kind e ≠ .I) (i : Inner B) :
    weight ys ts rs χ e (I i) = 0 := by
  have hz := I_no_cross_nonI ys ts rs hybox htbox hr i e he
  simp [weight,I,hz]

/-- Exact T/C/Y/I decomposition. C-Y and Y-Y terms remain actual costs in
 yRemainder; all I interactions with other classes vanish by cap geometry. -/
theorem outside_class_decomposition (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (χ : Edge O B P → Bool) :
    outsideEnergy ys ts rs (fun r => χ (.inr r)) = baseCost ys ts rs χ + coreCost ys ts rs χ + yRemainder ys ts rs χ := by
  change halfSum (fun r s : Outside O B P => weight ys ts rs χ (.inr r) (.inr s)) = _
  rw [halfSum_sum _ (fun _ _ => weight_symm _ _ _ _ _ _)]
  rw [halfSum_sum _ (fun _ _ => weight_symm _ _ _ _ _ _)]
  rw [halfSum_sum _ (fun _ _ => weight_symm _ _ _ _ _ _)]
  rw [cutSum_sum_right,cutSum_sum_right]
  rw [cutSum_sum_right (fun (c : Inner O) (r : YEdge O P ⊕ Inner B) =>
    weight ys ts rs χ (.inr (.inr (.inl c))) (.inr (.inr (.inr r))))]
  have hTI : cutSum (fun (t : Fin B × Fin P) (i : Inner B) => weight ys ts rs χ (T t) (I i)) = 0 := by
    unfold cutSum
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro i _
    exact weight_I_zero ys ts rs hybox htbox hr χ (T t) (by simp [T,kind]) i
  have hCI : cutSum (fun (c : Inner O) (i : Inner B) => weight ys ts rs χ (C c) (I i)) = 0 := by
    unfold cutSum
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro i _
    exact weight_I_zero ys ts rs hybox htbox hr χ (C c) (by simp [C,kind]) i
  have hYI : cutSum (fun (y : YEdge O P) (i : Inner B) => weight ys ts rs χ (Y y) (I i)) = 0 := by
    unfold cutSum
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro i _
    exact weight_I_zero ys ts rs hybox htbox hr χ (Y y) (by simp [Y,kind]) i
  change halfSum (fun t u : Fin B × Fin P => weight ys ts rs χ (T t) (T u)) +
    (cutSum (fun (t : Fin B × Fin P) (c : Inner O) => weight ys ts rs χ (T t) (C c)) +
      (cutSum (fun (t : Fin B × Fin P) (y : YEdge O P) => weight ys ts rs χ (T t) (Y y)) +
        cutSum (fun (t : Fin B × Fin P) (i : Inner B) => weight ys ts rs χ (T t) (I i)))) +
    (halfSum (fun c d : Inner O => weight ys ts rs χ (C c) (C d)) +
      (cutSum (fun (c : Inner O) (y : YEdge O P) => weight ys ts rs χ (C c) (Y y)) +
        cutSum (fun (c : Inner O) (i : Inner B) => weight ys ts rs χ (C c) (I i))) +
      (halfSum (fun y z : YEdge O P => weight ys ts rs χ (Y y) (Y z)) +
        cutSum (fun (y : YEdge O P) (i : Inner B) => weight ys ts rs χ (Y y) (I i)) +
        halfSum (fun i j : Inner B => weight ys ts rs χ (I i) (I j)))) = _
  rw [hTI,hCI,hYI]
  have hTC : cutSum (fun (t : Fin B × Fin P) (c : Inner O) => weight ys ts rs χ (T t) (C c)) =
      cutSum (fun (c : Inner O) (t : Fin B × Fin P) => weight ys ts rs χ (C c) (T t)) := by
    unfold cutSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro t _
    exact weight_symm _ _ _ _ _ _
  rw [hTC]
  unfold baseCost coreCost yRemainder
  ring

noncomputable def yUnary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (y : YEdge O P) (b : Bool) : ℝ :=
  ∑ t : Fin B × Fin P, if Cross ys ts rs (Y y) (T t) ∧ b = χ (T t) then 1 else 0

noncomputable def yFloor (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : ℝ :=
  ∑ y : YEdge O P, min (yUnary ys ts rs χ y false) (yUnary ys ts rs χ y true)

noncomputable def yPreferred (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (y : YEdge O P) : Bool :=
  decide (yUnary ys ts rs χ y true ≤ yUnary ys ts rs χ y false)

noncomputable def yResidual (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : ℝ :=
  cutSum (fun (c : Inner O) (y : YEdge O P) => weight ys ts rs χ (C c) (Y y)) +
  halfSum (fun y z : YEdge O P => weight ys ts rs χ (Y y) (Y z))

noncomputable def residualBudget (O P : Nat) : ℝ :=
  (Fintype.card (Inner O):ℝ)*Fintype.card (YEdge O P)+(Fintype.card (YEdge O P):ℝ)^2/2

theorem cutSum_nonneg {α β : Type*} [Fintype α] [Fintype β] (w : α → β → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) : 0 ≤ cutSum w :=
  Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hw a b))

theorem halfSum_nonneg {α : Type*} [Fintype α] (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) : 0 ≤ halfSum w :=
  div_nonneg (cutSum_nonneg w hw) (by norm_num)

theorem cutSum_le_card {α β : Type*} [Fintype α] [Fintype β] (w : α → β → ℝ)
    (hw : ∀ a b, w a b ≤ 1) : cutSum w ≤ (Fintype.card α:ℝ)*Fintype.card β := by
  calc
    _ ≤ ∑ _a : α, ∑ _b : β, (1:ℝ) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hw a b))
    _ = _ := by simp

theorem halfSum_le_card {α : Type*} [Fintype α] (w : α → α → ℝ)
    (hw : ∀ a b, w a b ≤ 1) : halfSum w ≤ (Fintype.card α:ℝ)^2/2 := by
  have hh := div_le_div_of_nonneg_right (cutSum_le_card w hw) (by norm_num : (0:ℝ)≤2)
  simpa only [halfSum,cutSum,pow_two] using hh

/-- Manuscript-compatible bound on all interactions touching Y, including
the full TY term. The optional unary-floor refinement is not needed here. -/
theorem yRemainder_bounds (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) :
    0 ≤ yRemainder ys ts rs χ ∧
    yRemainder ys ts rs χ ≤ (Fintype.card (YEdge O P):ℝ)*
      ((B:ℝ)*P+Fintype.card (Inner O))+(Fintype.card (YEdge O P):ℝ)^2/2 := by
  have hT := cutSum_le_card (fun (t : Fin B × Fin P) (y : YEdge O P) => weight ys ts rs χ (T t) (Y y))
    (fun _ _ => weight_le_one _ _ _ _ _ _)
  have hC := cutSum_le_card (fun (c : Inner O) (y : YEdge O P) => weight ys ts rs χ (C c) (Y y))
    (fun _ _ => weight_le_one _ _ _ _ _ _)
  have hY := halfSum_le_card (fun y z : YEdge O P => weight ys ts rs χ (Y y) (Y z))
    (fun _ _ => weight_le_one _ _ _ _ _ _)
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at hT
  constructor
  · unfold yRemainder
    exact add_nonneg (add_nonneg
      (cutSum_nonneg _ (fun _ _ => weight_nonneg _ _ _ _ _ _))
      (cutSum_nonneg _ (fun _ _ => weight_nonneg _ _ _ _ _ _)))
      (halfSum_nonneg _ (fun _ _ => weight_nonneg _ _ _ _ _ _))
  · unfold yRemainder
    nlinarith

/-- Residual terms are the actual C-Y and Y-Y monochromatic crossings. -/
theorem yResidual_bounds (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : 0 ≤ yResidual ys ts rs χ ∧ yResidual ys ts rs χ ≤ residualBudget O P := by
  unfold yResidual residualBudget
  exact ⟨add_nonneg (cutSum_nonneg _ (fun _ _ => weight_nonneg _ _ _ _ _ _))
    (halfSum_nonneg _ (fun _ _ => weight_nonneg _ _ _ _ _ _)),
    add_le_add (cutSum_le_card _ (fun _ _ => weight_le_one _ _ _ _ _ _))
      (halfSum_le_card _ (fun _ _ => weight_le_one _ _ _ _ _ _))⟩

theorem yRemainder_eq_unary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) :
    yRemainder ys ts rs χ = (∑ y : YEdge O P, yUnary ys ts rs χ y (χ (Y y))) + yResidual ys ts rs χ := by
  have hTY : cutSum (fun (t : Fin B × Fin P) (y : YEdge O P) => weight ys ts rs χ (T t) (Y y)) =
      ∑ y : YEdge O P, yUnary ys ts rs χ y (χ (Y y)) := by
    unfold cutSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    unfold yUnary
    apply Finset.sum_congr rfl
    intro t _
    exact weight_symm _ _ _ _ _ _
  unfold yRemainder yResidual
  rw [hTY]
  ring

theorem yUnary_floor_le (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : yFloor ys ts rs χ ≤ ∑ y : YEdge O P, yUnary ys ts rs χ y (χ (Y y)) := by
  apply Finset.sum_le_sum
  intro y _
  cases χ (Y y)
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem yPreferred_attains (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (y : YEdge O P) :
    yUnary ys ts rs χ y (yPreferred ys ts rs χ y) =
      min (yUnary ys ts rs χ y false) (yUnary ys ts rs χ y true) := by
  unfold yPreferred
  by_cases h : yUnary ys ts rs χ y true ≤ yUnary ys ts rs χ y false
  · simp [h]
  · simp [h,min_eq_left (le_of_not_ge h)]

/-- The actual lower estimate after deleting only C-Y/Y-Y interactions. -/
theorem outside_lower (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (χ : Edge O B P → Bool) :
    baseCost ys ts rs χ + coreCost ys ts rs χ + yFloor ys ts rs χ ≤
      outsideEnergy ys ts rs (fun r => χ (.inr r)) := by
  rw [outside_class_decomposition ys ts rs hybox htbox hr,yRemainder_eq_unary]
  linarith [yUnary_floor_le ys ts rs χ,(yResidual_bounds ys ts rs χ).1]

def replaceY (χ : Edge O B P → Bool) (ζ : YEdge O P → Bool) : Edge O B P → Bool
  | .inr (.inr (.inr (.inl y))) => ζ y
  | e => χ e

theorem replaceY_nonY (χ : Edge O B P → Bool) (ζ : YEdge O P → Bool) (e : Edge O B P)
    (he : kind e ≠ .Y) : replaceY χ ζ e = χ e := by
  rcases e with x | (t | (c | (y | i))) <;> simp_all [replaceY,kind]

theorem baseCost_replaceY (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (ζ : YEdge O P → Bool) :
    baseCost ys ts rs (replaceY χ ζ) = baseCost ys ts rs χ := by
  rfl

theorem coreCost_replaceY (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (ζ : YEdge O P → Bool) :
    coreCost ys ts rs (replaceY χ ζ) = coreCost ys ts rs χ := by
  rfl

theorem yUnary_replaceY (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (ζ : YEdge O P → Bool) (y : YEdge O P) (b : Bool) :
    yUnary ys ts rs (replaceY χ ζ) y b = yUnary ys ts rs χ y b := by
  rfl

/-- A concrete extension keeps the same C/T/I and X colors and attains all
Y unary minima simultaneously. The only restoration cost is bounded by the
actual number of C-Y/Y-Y pairs; there is no BP-sized unary error. -/
theorem outside_attainment (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (χ : Edge O B P → Bool) :
    ∃ ψ : Edge O B P → Bool,
      (∀ e, kind e ≠ .Y → ψ e = χ e) ∧
      outsideEnergy ys ts rs (fun r => ψ (.inr r)) ≤
        baseCost ys ts rs χ + coreCost ys ts rs χ + yFloor ys ts rs χ + residualBudget O P := by
  let ψ := replaceY χ (yPreferred ys ts rs χ)
  refine ⟨ψ,replaceY_nonY _ _,?_⟩
  rw [outside_class_decomposition ys ts rs hybox htbox hr,yRemainder_eq_unary]
  change baseCost ys ts rs (replaceY χ _) + coreCost ys ts rs (replaceY χ _) +
    ((∑ y : YEdge O P, yUnary ys ts rs (replaceY χ _) y ((replaceY χ _) (Y y))) +
      yResidual ys ts rs ψ) ≤ _
  simp only [baseCost_replaceY,coreCost_replaceY,yUnary_replaceY]
  change baseCost ys ts rs χ + coreCost ys ts rs χ +
    ((∑ y : YEdge O P, yUnary ys ts rs χ y (yPreferred ys ts rs χ y)) + yResidual ys ts rs ψ) ≤ _
  simp only [yPreferred_attains]
  change baseCost ys ts rs χ + coreCost ys ts rs χ + (yFloor ys ts rs χ + yResidual ys ts rs ψ) ≤ _
  linarith [(yResidual_bounds ys ts rs ψ).2]

noncomputable def coreUnary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (c : Inner O) (b : Bool) : ℝ :=
  ∑ t : Fin B × Fin P, if Cross ys ts rs (C c) (T t) ∧ b = χ (T t) then 1 else 0

noncomputable def coreField (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (c : Inner O) : Int :=
  ∑ t : Fin B × Fin P, if Cross ys ts rs (C c) (T t) then Q4.JointProbe.spin (χ (T t)) else 0

/-- The palette coefficient is the actual T-neighbor spin sum of a C edge. -/
theorem coreUnary_difference (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (c : Inner O) :
    coreUnary ys ts rs χ c true-coreUnary ys ts rs χ c false = (coreField ys ts rs χ c : ℝ) := by
  unfold coreUnary coreField
  rw [←Finset.sum_sub_distrib]
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : Cross ys ts rs (C c) (T t) <;> cases χ (T t) <;> simp [hc,Q4.JointProbe.spin]

theorem coreCost_eq_pair_unary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) :
    coreCost ys ts rs χ = halfSum (fun c d : Inner O => weight ys ts rs χ (C c) (C d)) +
      ∑ c : Inner O, coreUnary ys ts rs χ c (χ (C c)) := rfl

noncomputable def gridCost (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : ℝ :=
  GridLocalization.energy (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
    (unary ys ts rs (fun r => χ (.inr r))) (fun x => χ (.inl x))

theorem energy_gridCost_outside (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (χ : Edge O B P → Bool) :
    energy ys ts rs χ = gridCost ys ts rs χ + outsideEnergy ys ts rs (fun r => χ (.inr r)) := by
  have hd := energy_grid_decomposition ys ts rs hy ht hybox htbox
    (fun x => χ (.inl x)) (fun r => χ (.inr r))
  simpa only [combine_restrictions,gridCost] using hd

theorem gridCost_replaceY (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (χ : Edge O B P → Bool) (ζ : YEdge O P → Bool) :
    gridCost ys ts rs (replaceY χ ζ) = gridCost ys ts rs χ := by
  have hu : unary ys ts rs (fun r => replaceY χ ζ (.inr r)) = unary ys ts rs (fun r => χ (.inr r)) := by
    funext x b
    rw [unary_eq_T ys ts rs hybox htbox hr,unary_eq_T ys ts rs hybox htbox hr]
    rfl
  unfold gridCost
  rw [hu]
  rfl

/-- Full objective lower bound with actual C-C and C-T costs and the true
independent Y unary floor, retaining arbitrary coloring of every class. -/
theorem full_lower (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (χ : Edge O B P → Bool) :
    gridCost ys ts rs χ + baseCost ys ts rs χ + coreCost ys ts rs χ + yFloor ys ts rs χ ≤
      energy ys ts rs χ := by
  rw [energy_gridCost_outside ys ts rs hy ht hybox htbox]
  linarith [outside_lower ys ts rs hybox htbox hr χ]

/-- A single explicit Y extension attains the matching full-objective upper
bound while keeping every C/T/I/X color, including the selected source code. -/
theorem full_attainment (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (χ : Edge O B P → Bool) :
    ∃ ψ : Edge O B P → Bool,
      (∀ e, kind e ≠ .Y → ψ e = χ e) ∧
      energy ys ts rs ψ ≤ gridCost ys ts rs χ + baseCost ys ts rs χ + coreCost ys ts rs χ +
        yFloor ys ts rs χ + residualBudget O P := by
  let ψ := replaceY χ (yPreferred ys ts rs χ)
  refine ⟨ψ,replaceY_nonY _ _,?_⟩
  rw [energy_gridCost_outside ys ts rs hy ht hybox htbox]
  change gridCost ys ts rs (replaceY χ _) + _ ≤ _
  rw [gridCost_replaceY ys ts rs hybox htbox hr]
  have hout : outsideEnergy ys ts rs (fun r => ψ (.inr r)) ≤
      baseCost ys ts rs χ + coreCost ys ts rs χ + yFloor ys ts rs χ + residualBudget O P := by
    rw [outside_class_decomposition ys ts rs hybox htbox hr,yRemainder_eq_unary]
    change baseCost ys ts rs (replaceY χ _) + coreCost ys ts rs (replaceY χ _) +
      ((∑ y : YEdge O P, yUnary ys ts rs (replaceY χ _) y ((replaceY χ _) (Y y))) + yResidual ys ts rs ψ) ≤ _
    simp only [baseCost_replaceY,coreCost_replaceY,yUnary_replaceY]
    change baseCost ys ts rs χ + coreCost ys ts rs χ +
      ((∑ y : YEdge O P, yUnary ys ts rs χ y (yPreferred ys ts rs χ y)) + yResidual ys ts rs ψ) ≤ _
    simp only [yPreferred_attains]
    change baseCost ys ts rs χ + coreCost ys ts rs χ + (yFloor ys ts rs χ + yResidual ys ts rs ψ) ≤ _
    linarith [(yResidual_bounds ys ts rs ψ).2]
  linarith

/-- The original whole-Y residual convention, with no unary-floor change to
the baseline. This holds for every coloring, without any minimization. -/
theorem full_Y_interval (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (χ : Edge O B P → Bool) :
    let L := gridCost ys ts rs χ + baseCost ys ts rs χ + coreCost ys ts rs χ
    L ≤ energy ys ts rs χ ∧ energy ys ts rs χ ≤ L +
      (Fintype.card (YEdge O P):ℝ)*((B:ℝ)*P+Fintype.card (Inner O))+
        (Fintype.card (YEdge O P):ℝ)^2/2 := by
  dsimp only
  rw [energy_gridCost_outside ys ts rs hy ht hybox htbox,
    outside_class_decomposition ys ts rs hybox htbox hr]
  have hh := yRemainder_bounds ys ts rs χ
  constructor <;> linarith [hh.1,hh.2]

theorem yUnary_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (y : YEdge O P) (b : Bool) :
    yUnary ys ts rs (fun e => !(χ e)) y b = yUnary ys ts rs χ y (!b) := by
  unfold yUnary
  apply Finset.sum_congr rfl
  intro t _
  cases b <;> cases hc : χ (T t) <;> simp [hc]

/-- The optional sharper unary floor depends only on frozen T colors. -/
theorem yFloor_congr_T (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ ψ : Edge O B P → Bool) (hT : ∀ t, χ (T t) = ψ (T t)) :
    yFloor ys ts rs χ = yFloor ys ts rs ψ := by
  unfold yFloor yUnary
  simp only [hT]

/-- Complementary frozen phases have exactly the same optional Y floor. -/
theorem yFloor_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) :
    yFloor ys ts rs (fun e => !(χ e)) = yFloor ys ts rs χ := by
  unfold yFloor
  simp only [yUnary_complement,Bool.not_false,Bool.not_true,min_comm]

end Q4.Candidate.CompleteClassEnergy

#print axioms Q4.Candidate.CompleteClassEnergy.outside_class_decomposition
#print axioms Q4.Candidate.CompleteClassEnergy.yResidual_bounds
#print axioms Q4.Candidate.CompleteClassEnergy.outside_lower
#print axioms Q4.Candidate.CompleteClassEnergy.outside_attainment
#print axioms Q4.Candidate.CompleteClassEnergy.coreUnary_difference
#print axioms Q4.Candidate.CompleteClassEnergy.full_lower
#print axioms Q4.Candidate.CompleteClassEnergy.full_attainment
#print axioms Q4.Candidate.CompleteClassEnergy.yRemainder_bounds
#print axioms Q4.Candidate.CompleteClassEnergy.full_Y_interval
#print axioms Q4.Candidate.CompleteClassEnergy.yFloor_complement
