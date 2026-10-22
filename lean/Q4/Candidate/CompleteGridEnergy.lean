import Q4.Candidate.CompleteDrawing

/-! The objective is the actual monochromatic crossing-pair count of every
edge of the exhaustive complete drawing. Outside colors are kept freely
variable; fixing them induces explicit unary costs on the actual X grid. -/
namespace Q4.Candidate.CompleteGridEnergy

open Q4.Candidate.CompleteDrawing Q4.Candidate.ConvexSeparation
attribute [local instance] Classical.propDecidable

variable {O B P : Nat}

noncomputable def crossingPairs (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    Finset (Edge O B P × Edge O B P) := by
  classical
  exact Finset.univ.filter (fun p => Fintype.equivFin _ p.1 < Fintype.equivFin _ p.2 ∧ Cross ys ts rs p.1 p.2)

noncomputable def energy (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) : ℝ := (Q4.monoCount (crossingPairs ys ts rs).toList χ : ℝ)

noncomputable def weight (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (e f : Edge O B P) : ℝ := by
  classical
  exact if Cross ys ts rs e f ∧ χ e = χ f then 1 else 0

theorem weight_symm (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (e f : Edge O B P) :
    weight ys ts rs χ e f = weight ys ts rs χ f e := by
  classical
  simp only [weight,cross_symm ys ts rs e f,eq_comm (a:=χ e)]

@[simp] theorem weight_self (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) (e : Edge O B P) : weight ys ts rs χ e e = 0 := by
  simp [weight,cross_irrefl]

/-- Every actual crossing pair is counted once in the finite edge list and
twice in the symmetric double sum. No quotient or limiting energy is used. -/
theorem energy_double_sum (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (χ : Edge O B P → Bool) :
    2*energy ys ts rs χ = ∑ e, ∑ f, weight ys ts rs χ e f := by
  classical
  have hs (e f : Edge O B P) : weight ys ts rs χ e f =
      (if Fintype.equivFin _ e < Fintype.equivFin _ f then weight ys ts rs χ e f else 0)+
      (if Fintype.equivFin _ f < Fintype.equivFin _ e then weight ys ts rs χ f e else 0) := by
    rcases lt_trichotomy (Fintype.equivFin _ e) (Fintype.equivFin _ f) with h | h | h
    · simp [h,not_lt_of_ge (le_of_lt h)]
    · have hef := (Fintype.equivFin _).injective h
      subst f
      simp
    · simp [h,not_lt_of_ge (le_of_lt h),weight_symm ys ts rs χ e f]
  have he : energy ys ts rs χ =
      ∑ e, ∑ f, if Fintype.equivFin _ e < Fintype.equivFin _ f then weight ys ts rs χ e f else 0 := by
    unfold energy crossingPairs
    rw [GridStepBridge.monoCount_list_sum,Finset.sum_map_toList,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    unfold weight
    by_cases ho : Fintype.equivFin _ e < Fintype.equivFin _ f <;>
      by_cases hc : Cross ys ts rs e f <;> by_cases he : χ e = χ f <;> simp [ho,hc,he]
  rw [he]
  conv_rhs => arg 2; ext e; arg 2; ext f; rw [hs]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun e f => if Fintype.equivFin _ f < Fintype.equivFin _ e then weight ys ts rs χ f e else 0)]
  ring

noncomputable def unary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (η : Outside O B P → Bool) (x : Fin B × Fin O) (b : Bool) : ℝ := by
  classical
  exact ∑ r, if Cross ys ts rs (.inl x) (.inr r) ∧ b = η r then 1 else 0

noncomputable def outsideEnergy (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (η : Outside O B P → Bool) : ℝ := by
  classical
  exact (∑ r, ∑ s, if Cross ys ts rs (.inr r) (.inr s) ∧ η r = η s then (1:ℝ) else 0)/2

def combine (ξ : Fin B × Fin O → Bool) (η : Outside O B P → Bool) : Edge O B P → Bool :=
  Sum.elim ξ η

theorem full_sum_partition (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (ξ : Fin B × Fin O → Bool) (η : Outside O B P → Bool) :
    energy ys ts rs (combine ξ η) =
      (∑ x, ∑ y, weight ys ts rs (combine ξ η) (.inl x) (.inl y))/2 +
      (∑ x, unary ys ts rs η x (ξ x)) + outsideEnergy ys ts rs η := by
  classical
  have he := energy_double_sum ys ts rs (combine ξ η)
  rw [Fintype.sum_sum_type] at he
  have hinner (e : Edge O B P) : (∑ f, weight ys ts rs (combine ξ η) e f) =
      (∑ x : Fin B × Fin O, weight ys ts rs (combine ξ η) e (.inl x)) +
      ∑ r : Outside O B P, weight ys ts rs (combine ξ η) e (.inr r) := Fintype.sum_sum_type _
  simp_rw [hinner] at he
  have hm : (∑ r : Outside O B P, ∑ x : Fin B × Fin O,
      weight ys ts rs (combine ξ η) (.inr r) (.inl x)) =
      ∑ x : Fin B × Fin O, ∑ r : Outside O B P, weight ys ts rs (combine ξ η) (.inl x) (.inr r) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro r _
    exact weight_symm _ _ _ _ _ _
  simp only [Finset.sum_add_distrib] at he
  rw [hm] at he
  have hu : (∑ x : Fin B × Fin O, ∑ r : Outside O B P,
      weight ys ts rs (combine ξ η) (.inl x) (.inr r)) =
      ∑ x, unary ys ts rs η x (ξ x) := rfl
  have ho : (∑ r : Outside O B P, ∑ s : Outside O B P,
      weight ys ts rs (combine ξ η) (.inr r) (.inr s)) = 2*outsideEnergy ys ts rs η := by
    unfold weight combine outsideEnergy
    simp only [Sum.elim_inr]
    ring_nf
    rfl
  rw [hu,ho] at he
  linarith only [he]

/-- Exact bridge from the X-X crossing sum to the existing actual finite
comparison-grid edge list, including both directions and diagonal ties. -/
theorem X_double_sum (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (ξ : Fin B × Fin O → Bool) (η : Outside O B P → Bool) :
    (∑ x, ∑ y, weight ys ts rs (combine ξ η) (.inl x) (.inl y))/2 =
      (Q4.monoCount (GridLocalization.gridEdges B O) ξ : ℝ) := by
  classical
  have hp (x y : Fin B × Fin O) : weight ys ts rs (combine ξ η) (.inl x) (.inl y) =
      GridStepExtension.discreteIndicator ξ x y + GridStepExtension.discreteIndicator ξ y x := by
    simp only [weight,X_cross_X ys ts rs hy ht hybox htbox,combine,Sum.elim_inl]
    unfold GridCounts.adj GridStepExtension.discreteIndicator
    by_cases hc : ξ x = ξ y
    · simp only [hc,and_true]
      by_cases hxy : x.1 < y.1 ∧ x.2 < y.2
      · have hyx : ¬ (y.1 < x.1 ∧ y.2 < x.2) := fun h => lt_asymm h.1 hxy.1
        simp [hxy,hyx]
      · by_cases hyx : y.1 < x.1 ∧ y.2 < x.2 <;> simp [hxy,hyx]
    · have hcy : ξ y ≠ ξ x := Ne.symm hc
      simp [hc,hcy]
  have hm : (∑ x, ∑ y, GridStepExtension.discreteIndicator ξ x y) =
      (Q4.monoCount (GridLocalization.gridEdges B O) ξ : ℝ) := by
    unfold GridLocalization.gridEdges
    rw [GridStepBridge.monoCount_list_sum,Finset.sum_map_toList,GridCounts.orientedEdges,Finset.sum_filter]
    conv_rhs => rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    unfold GridStepExtension.discreteIndicator
    by_cases h1 : x.1 < y.1 <;> by_cases h2 : x.2 < y.2 <;> by_cases hc : ξ x = ξ y <;>
      simp [h1,h2,hc]
  simp_rw [hp,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun x y => GridStepExtension.discreteIndicator ξ y x),hm]
  ring

theorem realSum_toList {α : Type*} (s : Finset α) (f : α → ℝ) :
    GridLocalization.realSum s.toList f = ∑ x ∈ s, f x := by
  have hl (xs : List α) : GridLocalization.realSum xs f = (xs.map f).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [GridLocalization.realSum,ih]
  rw [hl,Finset.sum_map_toList]

/-- Exact complete-graph objective decomposition after fixing outside colors.
All C, Y, I, T interactions remain in the actual outsideEnergy term. -/
theorem energy_grid_decomposition (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (ξ : Fin B × Fin O → Bool) (η : Outside O B P → Bool) :
    energy ys ts rs (combine ξ η) =
      GridLocalization.energy (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
        (unary ys ts rs η) ξ + outsideEnergy ys ts rs η := by
  rw [full_sum_partition,X_double_sum ys ts rs hy ht hybox htbox]
  simp only [GridLocalization.energy,GridLocalization.gridVertices,realSum_toList]
  ring

/-- Geometry removes exactly the non-T terms from the actual unary field. -/
theorem unary_eq_T (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (η : Outside O B P → Bool) (x : Fin B × Fin O) (b : Bool) :
    unary ys ts rs η x b =
      ∑ t : Fin B × Fin P, if Cross ys ts rs (.inl x) (.inr (.inl t)) ∧ b = η (.inl t) then 1 else 0 := by
  classical
  have hz (r : Inner O ⊕ (YEdge O P ⊕ Inner B)) :
      ¬ Cross ys ts rs (.inl x) (.inr (.inr r)) := by
    intro hc
    obtain ⟨t,he⟩ := X_cross_outside_only_T ys ts rs hybox htbox hr x (.inr r) hc
    cases he
  unfold unary
  rw [Fintype.sum_sum_type]
  simp only [hz,false_and,ite_false,Finset.sum_const_zero,add_zero]

theorem unary_bounds (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (η : Outside O B P → Bool) (x : Fin B × Fin O) (b : Bool) :
    0 ≤ unary ys ts rs η x b ∧ unary ys ts rs η x b ≤ (B:ℝ)*P := by
  classical
  rw [unary_eq_T ys ts rs hybox htbox hr]
  constructor
  · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ _t : Fin B × Fin P, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
      _ = (B:ℝ)*P := by simp

/-- No outside coloring is fixed by this theorem: every coloring gives an
actual unary field of oscillation at most the total number BP of T edges. -/
theorem unary_amplitude (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (η : Outside O B P → Bool) (x : Fin B × Fin O) :
    |unary ys ts rs η x true-unary ys ts rs η x false| ≤ (B:ℝ)*P := by
  have ht := unary_bounds ys ts rs hybox htbox hr η x true
  have hf := unary_bounds ys ts rs hybox htbox hr η x false
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem combine_restrictions (χ : Edge O B P → Bool) :
    combine (fun x => χ (.inl x)) (fun r => χ (.inr r)) = χ := by
  funext e
  cases e <;> rfl

/-- Global optimality of all freely colored complete-graph edges implies
optimality of its actual grid section, with its outside colors held fixed. -/
theorem grid_section_minimizer (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (χ : Edge O B P → Bool) (hmin : ∀ ζ, energy ys ts rs χ ≤ energy ys ts rs ζ) :
    ∀ ξ, GridLocalization.energy (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
      (unary ys ts rs (fun r => χ (.inr r))) (fun x => χ (.inl x)) ≤
      GridLocalization.energy (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
        (unary ys ts rs (fun r => χ (.inr r))) ξ := by
  intro ξ
  have hh := hmin (combine ξ (fun r => χ (.inr r)))
  rw [←combine_restrictions χ] at hh
  rw [energy_grid_decomposition ys ts rs hy ht hybox htbox,
      energy_grid_decomposition ys ts rs hy ht hybox htbox] at hh
  exact (add_le_add_iff_right _).mp hh

/-- Full original/frame/program crossing-graph minimizers obey finite-grid
localization, with the external amplitude derived from actual geometry. -/
theorem complete_minimizer_localization (hO : 0 < O) (hB : 0 < B)
    (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (a : ℝ) (ha : (P:ℝ)/O + GridCounts.rho B O ≤ a) (hsmall : a ≤ 1/(2:ℝ)^4096)
    (χ : Edge O B P → Bool) (hmin : ∀ ζ, energy ys ts rs χ ≤ energy ys ts rs ζ) :
    ∃ b : Bool, ∃ F : Finset (Fin B × Fin O),
      (fun x => χ (.inl x)) = Q4.SimultaneousFlip.flip (CanonicalField.phase b) (GridLocalization.membershipMask F) ∧
      (F.card : ℝ) ≤ 52*a*((B:ℝ)*O) ∧
      F ⊆ GridCounts.strip B O (220*a) ∪ GridCounts.corners B O (220*a) := by
  have hO0 : (O:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hO
  have hamp (x : Fin B × Fin O) :
      |unary ys ts rs (fun r => χ (.inr r)) x true-unary ys ts rs (fun r => χ (.inr r)) x false| ≤
      ((P:ℝ)/O)*((B:ℝ)*O) := by
    have he : ((P:ℝ)/O)*((B:ℝ)*O) = (B:ℝ)*P := by field_simp
    rw [he]
    exact unary_amplitude ys ts rs hybox htbox hr _ x
  exact GridStepBridge.minimizer_localization B O hB hO
    (unary ys ts rs (fun r => χ (.inr r))) ((P:ℝ)/O) a (by positivity) ha hsmall hamp
    (fun x => χ (.inl x)) (grid_section_minimizer ys ts rs hy ht hybox htbox χ hmin)

noncomputable def gridOutsideNeighbors (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (x : Fin B × Fin O) : Finset (Outside O B P) :=
  Finset.univ.filter (fun r => Cross ys ts rs (.inl x) (.inr r))

/-- The bound counts actual neighbors in the complete crossing graph; it is
not a degree parameter supplied by a caller. -/
theorem gridOutsideDegree_le (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid) (x : Fin B × Fin O) :
    (gridOutsideNeighbors ys ts rs x).card ≤ B*P := by
  have hsub : gridOutsideNeighbors ys ts rs x ⊆
      (Finset.univ : Finset (Fin B × Fin P)).image Sum.inl := by
    intro r hr'
    obtain ⟨t,rfl⟩ := X_cross_outside_only_T ys ts rs hybox htbox hr x r (Finset.mem_filter.mp hr').2
    exact Finset.mem_image.mpr ⟨t,Finset.mem_univ t,rfl⟩
  calc
    _ ≤ ((Finset.univ : Finset (Fin B × Fin P)).image (Sum.inl : _ → Outside O B P)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin B × Fin P)).card := Finset.card_image_le
    _ = B*P := by simp

/-- The complete objective is bracketed around the actual outside objective
plus the minimum of its two explicitly induced grid phase estimates. -/
theorem complete_minimizer_interval (hO : 0 < O) (hB : 0 < B)
    (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (a : ℝ) (ha : (P:ℝ)/O + GridCounts.rho B O ≤ a) (hsmall : a ≤ 1/(2:ℝ)^4096)
    (χ : Edge O B P → Bool) (hmin : ∀ ζ, energy ys ts rs χ ≤ energy ys ts rs ζ) :
    let η := fun r => χ (.inr r)
    let L := outsideEnergy ys ts rs η + min
      (GridLocalization.phaseEstimate (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
        (unary ys ts rs η) (CanonicalField.phase false))
      (GridLocalization.phaseEstimate (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
        (unary ys ts rs η) (CanonicalField.phase true))
    L - 2^32*a^3*((B:ℝ)*O)^2 ≤ energy ys ts rs χ ∧
      energy ys ts rs χ ≤ L + 2^32*a^3*((B:ℝ)*O)^2 := by
  dsimp only
  have hO0 : (O:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hO
  have hamp (x : Fin B × Fin O) :
      |unary ys ts rs (fun r => χ (.inr r)) x true-unary ys ts rs (fun r => χ (.inr r)) x false| ≤
      ((P:ℝ)/O)*((B:ℝ)*O) := by
    have he : ((P:ℝ)/O)*((B:ℝ)*O) = (B:ℝ)*P := by field_simp
    rw [he]
    exact unary_amplitude ys ts rs hybox htbox hr _ x
  have hg := GridStepBridge.finite_grid_optimum_interval B O hB hO
    (unary ys ts rs (fun r => χ (.inr r))) ((P:ℝ)/O) a (by positivity) ha hsmall hamp
    (fun x => χ (.inl x)) (grid_section_minimizer ys ts rs hy ht hybox htbox χ hmin)
  have hd := energy_grid_decomposition ys ts rs hy ht hybox htbox
    (fun x => χ (.inl x)) (fun r => χ (.inr r))
  rw [combine_restrictions] at hd
  dsimp only at hg
  constructor <;> linarith [hg.1,hg.2]

end Q4.Candidate.CompleteGridEnergy

#print axioms Q4.Candidate.CompleteGridEnergy.energy_double_sum
#print axioms Q4.Candidate.CompleteGridEnergy.energy_grid_decomposition
#print axioms Q4.Candidate.CompleteGridEnergy.unary_amplitude
#print axioms Q4.Candidate.CompleteGridEnergy.complete_minimizer_localization
#print axioms Q4.Candidate.CompleteGridEnergy.gridOutsideDegree_le
#print axioms Q4.Candidate.CompleteGridEnergy.complete_minimizer_interval
