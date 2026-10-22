import Q4.Candidate.CompleteGridEnergy
import Q4.Candidate.ProbeFreezingReal

namespace Q4.Candidate.CompleteProbeFreezing

open Q4.Candidate.CompleteDrawing Q4.Candidate.CompleteGridEnergy
open Q4.Candidate.ConvexSeparation
open Q4.Candidate.ProbeFreezing (neighbors outsideNeighbors)
attribute [local instance] Classical.propDecidable

variable {O B P : Nat}

/-- Membership in the actual edge-list neighborhood, allowing either stored
orientation and retaining every probe-probe edge. -/
theorem mem_neighbors {α : Type*} [DecidableEq α] (es : List (α×α)) (p q : α) :
    q ∈ neighbors es p ↔ (p,q) ∈ es ∨ (q,p) ∈ es := by
  induction es with
  | nil => simp [neighbors]
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    by_cases hpa : p = a
    · subst a
      simp only [neighbors,ite_true,List.mem_cons,ih,Prod.mk.injEq,true_and]
      constructor
      · rintro (rfl | h | h) <;> simp_all
      · rintro ((h | h) | (h | h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inl (h.1.trans h.2)
        · exact Or.inr (Or.inr h)
    · by_cases hpb : p = b
      · subst b
        simp only [neighbors,hpa,ite_false,ite_true,List.mem_cons,ih,Prod.mk.injEq,and_true]
        constructor
        · rintro (rfl | h | h) <;> simp_all
        · rintro ((h | h) | (h | h))
          · exact h.1.elim
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      · simp [neighbors,hpa,hpb,ih,Prod.mk.injEq]

/-- A list with no repeated pair and a single strict rank orientation gives
actual simple neighborhoods, proved directly from the list definition. -/
theorem neighbors_nodup_of_order {α : Type*} [DecidableEq α] (rank : α → Nat)
    (es : List (α×α)) (hd : es.Nodup)
    (ho : ∀ e ∈ es, rank e.1 < rank e.2) (p : α) : (neighbors es p).Nodup := by
  induction es with
  | nil => simp [neighbors]
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    have hd' := List.nodup_cons.mp hd
    have hab := ho (a,b) (by simp)
    have htail : ∀ e ∈ es, rank e.1 < rank e.2 := fun e he => ho e (by simp [he])
    have hi := ih hd'.2 htail
    by_cases hpa : p = a
    · subst a
      simp only [neighbors,ite_true]
      refine List.nodup_cons.mpr ⟨?_,hi⟩
      intro hb
      rcases (mem_neighbors es p b).mp hb with h | h
      · exact hd'.1 h
      · exact lt_asymm hab (htail _ h)
    · by_cases hpb : p = b
      · subst b
        simp only [neighbors,hpa,ite_false,ite_true]
        refine List.nodup_cons.mpr ⟨?_,hi⟩
        intro ha
        rcases (mem_neighbors es p a).mp ha with h | h
        · exact lt_asymm hab (htail _ h)
        · exact hd'.1 h
      · simpa only [neighbors,hpa,hpb,ite_false] using hi

theorem crossingPairs_loopless (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    ∀ e ∈ (crossingPairs ys ts rs).toList, e.1 ≠ e.2 := by
  intro e he heq
  have h := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2.1
  rw [heq] at h
  exact lt_irrefl _ h

theorem crossingPairs_neighbors_nodup (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (p : Edge O B P) : (neighbors (crossingPairs ys ts rs).toList p).Nodup := by
  apply neighbors_nodup_of_order (fun e => (Fintype.equivFin _ e).val) _ (Finset.nodup_toList _) _ p
  intro e he
  exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2.1

theorem mem_crossingPairs_neighbors (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (p q : Edge O B P) : q ∈ neighbors (crossingPairs ys ts rs).toList p ↔ Cross ys ts rs p q := by
  rw [mem_neighbors]
  simp only [Finset.mem_toList,crossingPairs,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro (h | h)
    · exact h.2
    · exact (cross_symm ys ts rs q p).mp h.2
  · intro hc
    have hpq : p ≠ q := by intro he; subst q; exact cross_irrefl ys ts rs p hc
    rcases lt_or_gt_of_ne (fun he => hpq ((Fintype.equivFin _).injective he)) with h | h
    · exact Or.inl ⟨h,hc⟩
    · exact Or.inr ⟨h,(cross_symm ys ts rs p q).mp hc⟩

def grid : Edge O B P → Bool
  | .inl _ => true
  | .inr _ => false

abbrev NonGridNonI (O B P : Nat) := (Fin B × Fin P) ⊕ (Inner O ⊕ YEdge O P)

def nonIEmbedding : NonGridNonI O B P → Edge O B P
  | .inl t => .inr (.inl t)
  | .inr (.inl c) => .inr (.inr (.inl c))
  | .inr (.inr y) => .inr (.inr (.inr (.inl y)))

theorem nonIEmbedding_injective : Function.Injective (@nonIEmbedding O B P) := by
  intro e f h
  rcases e with t | (c | y) <;> rcases f with t' | (c' | y') <;> simp_all [nonIEmbedding]

theorem inner_card_bound (n : Nat) : 2*Fintype.card (Inner n) ≤ n*n := by
  let f : Bool × Inner n → Fin n × Fin n := fun p => if p.1 then p.2.val.swap else p.2.val
  have hf : Function.Injective f := by
    rintro ⟨b,p⟩ ⟨c,q⟩ he
    cases b <;> cases c
    · simp only [f,Bool.false_eq_true,ite_false,Prod.mk.injEq,true_and] at he ⊢
      exact Subtype.ext he
    · simp only [f,Bool.false_eq_true,ite_false,ite_true] at he
      have h1 := p.property
      have h2 := q.property
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      dsimp at he1 he2
      exact (lt_asymm (he1 ▸ he2 ▸ h1) h2).elim
    · simp only [f,Bool.false_eq_true,ite_false,ite_true] at he
      have h1 := p.property
      have h2 := q.property
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      dsimp at he1 he2
      rw [←he2,←he1] at h2
      exact (lt_asymm h1 h2).elim
    · simp only [f,ite_true,Prod.mk.injEq,true_and] at he ⊢
      exact Subtype.ext (Prod.swap_injective he)
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod] using hc

/-- Every actual non-grid neighbor of a T probe is a T, C, or Y edge.
The entire I class is removed by the proved geometric isolation theorem. -/
theorem outside_neighbors_card_le (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid) (t : Fin B × Fin P) :
    ((outsideNeighbors (crossingPairs ys ts rs).toList grid (.inr (.inl t))).length : ℝ) ≤
      (B:ℝ)*P+((O:ℝ)+P)^2/2 := by
  have hsimple := crossingPairs_neighbors_nodup ys ts rs (.inr (.inl t))
  have hnodup := hsimple.filter (fun v => !(grid v))
  have hsub : (outsideNeighbors (crossingPairs ys ts rs).toList grid (.inr (.inl t))).toFinset ⊆
      (Finset.univ : Finset (NonGridNonI O B P)).image nonIEmbedding := by
    intro e he
    have hmem := List.mem_filter.mp (List.mem_toFinset.mp he)
    have hc := (mem_crossingPairs_neighbors ys ts rs (.inr (.inl t)) e).mp hmem.1
    rcases e with x | (t' | (c | (y | i)))
    · simp [grid] at hmem
    · exact Finset.mem_image.mpr ⟨.inl t',Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨.inr (.inl c),Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨.inr (.inr y),Finset.mem_univ _,rfl⟩
    · exact (I_no_cross_nonI ys ts rs hybox htbox hr i (.inr (.inl t)) (by simp [kind]) hc).elim
  have hc := Finset.card_le_card hsub
  unfold outsideNeighbors at hc
  rw [List.toFinset_card_of_nodup hnodup,Finset.card_image_of_injective _ nonIEmbedding_injective] at hc
  simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at hc
  have hcR : ((outsideNeighbors (crossingPairs ys ts rs).toList grid (.inr (.inl t))).length : ℝ) ≤
      (B:ℝ)*P+(Fintype.card (Inner O):ℝ)+(O:ℝ)*P+(Fintype.card (Inner P):ℝ) := by
    have hc' : (outsideNeighbors (crossingPairs ys ts rs).toList grid (.inr (.inl t))).length ≤
        B*P+Fintype.card (Inner O)+O*P+Fintype.card (Inner P) := by
      simpa only [outsideNeighbors,add_assoc] using hc
    exact_mod_cast hc'
  have hO : 2*(Fintype.card (Inner O):ℝ) ≤ (O:ℝ)*O := by exact_mod_cast inner_card_bound O
  have hP : 2*(Fintype.card (Inner P):ℝ) ≤ (P:ℝ)*P := by exact_mod_cast inner_card_bound P
  nlinarith

noncomputable def probes (O B P : Nat) : List (Edge O B P) :=
  (Finset.univ : Finset (Fin B × Fin P)).toList.map (fun t => .inr (.inl t))

@[simp] theorem mem_probes (e : Edge O B P) :
    e ∈ probes O B P ↔ ∃ t : Fin B × Fin P, e = .inr (.inl t) := by
  simp [probes,eq_comm]

noncomputable def reference (b : Bool) (e : Edge O B P) : Bool :=
  if b then !(combine (CanonicalField.phase false) (fun _ => false) e)
  else combine (CanonicalField.phase false) (fun _ => false) e

@[simp] theorem reference_X (b : Bool) (x : Fin B × Fin O) :
    reference b (.inl x : Edge O B P) = CanonicalField.phase b x := by
  cases b <;> rfl

noncomputable def field (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) (e : Edge O B P) : Int :=
  ProbeFreezing.gridField (crossingPairs ys ts rs).toList grid (reference b) e

theorem field_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e : Edge O B P) : field ys ts rs true e = -field ys ts rs false e := by
  unfold field ProbeFreezing.gridField reference
  simp only [ite_true,Bool.false_eq_true,ite_false,Q4.JointProbe.spin_not]
  exact Q4.JointProbe.intSum_neg _ _

/-- The phase-minus tie is the complement of the phase-plus tie. -/
noncomputable def frozenColor (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) (e : Edge O B P) : Bool :=
  if b then !(ProbeFreezing.canonicalResponse (field ys ts rs false e))
  else ProbeFreezing.canonicalResponse (field ys ts rs false e)

theorem frozenColor_best (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) (e : Edge O B P) : ProbeFreezing.BestResponse (field ys ts rs b e) (frozenColor ys ts rs b e) := by
  cases b
  · exact ProbeFreezing.canonicalResponse_best _
  · rw [field_complement]
    exact ProbeFreezing.complement_best_response _ _ (ProbeFreezing.canonicalResponse_best _)

noncomputable def outsideBudget (O B P : Nat) : ℝ :=
  ((B:ℝ)*P+((O:ℝ)+P)^2/2)/((B:ℝ)*O)

theorem outsideBudget_nonneg : 0 ≤ outsideBudget O B P := by
  unfold outsideBudget
  positivity

theorem outsideBudget_mul (hO : 0 < O) (hB : 0 < B) :
    outsideBudget O B P*((B:ℝ)*O) = (B:ℝ)*P+((O:ℝ)+P)^2/2 := by
  unfold outsideBudget
  exact div_mul_cancel₀ _ (ne_of_gt (mul_pos (by exact_mod_cast hB) (by exact_mod_cast hO)))

/-- Actual complete-graph version of sequential probe freezing. The genuine
soft-field count is the sole remaining counting interface here. Geometry,
all edge classes, full-objective localization, degree bounds and sequential
probe-probe costs are proved in the dependency chain. -/
theorem complete_probe_freezing (hO : 0 < O) (hB : 0 < B)
    (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (a Q : ℝ) (ha : (P:ℝ)/O + GridCounts.rho B O ≤ a) (hsmall : a ≤ 1/(2:ℝ)^4096)
    (hQ : 0 ≤ Q)
    (hsoft : ∀ b : Bool,
      ((ProbeFreezing.realSoftProbes (probes O B P) (field ys ts rs b)
        ((104*a+outsideBudget O B P)*((B:ℝ)*O))).length : ℝ) ≤
        Q*(104*a+outsideBudget O B P+GridCounts.rho B O)*((B:ℝ)*O))
    (χ : Edge O B P → Bool) (hmin : ∀ ζ, energy ys ts rs χ ≤ energy ys ts rs ζ) :
    ∃ b : Bool, ∃ ψ : Edge O B P → Bool,
      (∀ t : Fin B × Fin P, ψ (.inr (.inl t)) = frozenColor ys ts rs b (.inr (.inl t))) ∧
      (∀ e, (∀ t : Fin B × Fin P, e ≠ .inr (.inl t)) → ψ e = χ e) ∧
      (∀ x : Fin B × Fin O, ψ (.inl x) = χ (.inl x)) ∧
      0 ≤ energy ys ts rs ψ-energy ys ts rs χ ∧
      energy ys ts rs ψ-energy ys ts rs χ ≤
        2*Q*(104*a+outsideBudget O B P+GridCounts.rho B O)*
          (104*a+outsideBudget O B P)*((B:ℝ)*O)^2 := by
  obtain ⟨b,F,hχ,hF,_⟩ := complete_minimizer_localization hO hB ys ts rs hy ht hybox htbox hr a ha hsmall χ hmin
  let fs : List (Edge O B P) := F.toList.map Sum.inl
  have ha0 : 0 ≤ a := le_trans (add_nonneg (by positivity) (GridCounts.rho_nonneg B O)) ha
  have hsupp : ∀ e, grid e = true → χ e ≠ reference b e → e ∈ fs := by
    intro e he hc
    rcases e with x | r
    · have hx : x ∈ F := by
        by_contra hx
        have hh := congrFun hχ x
        simp only [Q4.SimultaneousFlip.flip,GridLocalization.membershipMask,decide_eq_false hx] at hh
        exact hc (hh.trans (reference_X b x).symm)
      exact List.mem_map.mpr ⟨x,Finset.mem_toList.mpr hx,rfl⟩
    · simp [grid] at he
  have hsize : (fs.length : ℝ) ≤ 52*a*(B*O : Nat) := by
    simpa only [fs,List.length_map,Finset.length_toList,Nat.cast_mul] using hF
  have hdeg : ∀ e, e ∈ probes O B P →
      ((outsideNeighbors (crossingPairs ys ts rs).toList grid e).length : ℝ) ≤ outsideBudget O B P*(B*O : Nat) := by
    intro e he
    obtain ⟨t,rfl⟩ := (mem_probes e).mp he
    simpa only [Nat.cast_mul,outsideBudget_mul hO hB] using outside_neighbors_card_le ys ts rs hybox htbox hr t
  have hminimum : ∀ ζ, ProbeFreezing.energy (crossingPairs ys ts rs).toList χ ≤
      ProbeFreezing.energy (crossingPairs ys ts rs).toList ζ := by
    intro ζ
    have hh := hmin ζ
    unfold energy ProbeFreezing.energy at *
    exact_mod_cast hh
  have hsoft' : ((ProbeFreezing.realSoftProbes (probes O B P) (field ys ts rs b)
      ((104*a+outsideBudget O B P)*(B*O : Nat))).length : ℝ) ≤
      Q*(104*a+outsideBudget O B P+GridCounts.rho B O)*(B*O : Nat) := by
    simpa only [Nat.cast_mul] using hsoft b
  obtain ⟨ψ,hψ,hout,hgrid,hlo,hcost⟩ := ProbeFreezing.probe_freezing_real
    (crossingPairs ys ts rs).toList grid χ (reference b) (frozenColor ys ts rs b) fs (probes O B P) (B*O)
    a (outsideBudget O B P) (GridCounts.rho B O) Q ha0 outsideBudget_nonneg (GridCounts.rho_nonneg B O) hQ
    (crossingPairs_loopless ys ts rs)
    (fun e _ => crossingPairs_neighbors_nodup ys ts rs e)
    (by intro e he; obtain ⟨t,rfl⟩ := (mem_probes e).mp he; rfl)
    hsupp hsize hdeg (fun e _ => frozenColor_best ys ts rs b e) hminimum hsoft'
  refine ⟨b,ψ,?_,?_,?_,?_,?_⟩
  · intro t
    exact hψ _ ((mem_probes _).mpr ⟨t,rfl⟩)
  · intro e he
    apply hout e
    rintro hm
    obtain ⟨t,ht⟩ := (mem_probes e).mp hm
    exact he t ht
  · intro x
    exact hgrid _ rfl
  · unfold ProbeFreezing.energy at hlo
    unfold energy
    exact_mod_cast hlo
  · unfold ProbeFreezing.energy at hcost
    push_cast at hcost
    simpa only [energy,Nat.cast_mul] using hcost

theorem intSum_list_sum {α : Type*} (xs : List α) (f : α → Int) :
    Q4.SimultaneousFlip.intSum xs f = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Q4.SimultaneousFlip.intSum,ih]

/-- The field used in freezing is exactly the sum over all actual grid
crossings, in the finite form used by the geometric fan-response modules. -/
theorem field_eq_sum (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) (e : Edge O B P) :
    field ys ts rs b e = ∑ x : Fin B × Fin O,
      if Cross ys ts rs e (.inl x) then Q4.JointProbe.spin (CanonicalField.phase b x) else 0 := by
  let s : Finset (Fin B × Fin O) := Finset.univ.filter (fun x => Cross ys ts rs e (.inl x))
  have hp : (ProbeFreezing.gridNeighbors (crossingPairs ys ts rs).toList grid e).Perm
      (s.toList.map (Sum.inl : Fin B × Fin O → Edge O B P)) := by
    apply (List.perm_ext_iff_of_nodup
      ((crossingPairs_neighbors_nodup ys ts rs e).filter grid)
      ((Finset.nodup_toList s).map Sum.inl_injective)).mpr
    intro f
    rcases f with x | r
    · simp [mem_crossingPairs_neighbors,grid,s]
    · simp [grid]
  unfold field ProbeFreezing.gridField
  rw [intSum_list_sum,(hp.map (fun v => Q4.JointProbe.spin (reference b v))).sum_eq]
  simp only [List.map_map]
  rw [Finset.sum_map_toList]
  exact Finset.sum_filter _ _

noncomputable def softRows (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) (z : ℝ) (k : Fin P) : Finset (Fin B) :=
  Finset.univ.filter (fun i => |(field ys ts rs b (.inr (.inl (i,k))) : ℝ)| ≤ z*((B:ℝ)*O))

/-- Complementing the canonical phase preserves every actual soft-row set,
including zero fields and both tie conventions. -/
theorem softRows_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (z : ℝ) (k : Fin P) : softRows ys ts rs true z k = softRows ys ts rs false z k := by
  ext i
  simp only [softRows,Finset.mem_filter,Finset.mem_univ,true_and,field_complement,Int.cast_neg,abs_neg]

theorem softProbe_count (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) (z : ℝ) :
    (ProbeFreezing.realSoftProbes (probes O B P) (field ys ts rs b) (z*((B:ℝ)*O))).length =
      ∑ k : Fin P, (softRows ys ts rs b z k).card := by
  unfold ProbeFreezing.realSoftProbes probes
  rw [List.filter_map,List.length_map]
  rw [←List.toFinset_card_of_nodup ((Finset.nodup_toList _).filter _)]
  rw [List.toFinset_filter,Finset.toList_toFinset]
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [softRows,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp

/-- Per-program actual soft-row estimates aggregate to the genuine global
soft-probe input. The phase-minus estimate follows by proved complementation. -/
theorem global_soft_from_rows (hO : 0 < O) (hB : 0 < B)
    (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (z C : ℝ) (hC : 0 ≤ C)
    (hrows : ∀ k : Fin P, ((softRows ys ts rs false z k).card : ℝ) ≤ C*((B:ℝ)*z+1))
    (b : Bool) :
    ((ProbeFreezing.realSoftProbes (probes O B P) (field ys ts rs b) (z*((B:ℝ)*O))).length : ℝ) ≤
      (C*P/O)*(z+GridCounts.rho B O)*((B:ℝ)*O) := by
  rw [softProbe_count,Nat.cast_sum]
  have hr (k : Fin P) : ((softRows ys ts rs b z k).card : ℝ) ≤ C*((B:ℝ)*z+1) := by
    cases b
    · exact hrows k
    · simpa only [softRows_complement] using hrows k
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin P))) => hr k)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hO0 : (O:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hO
  have hB0 : (B:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have he : (C*P/O)*(z+GridCounts.rho B O)*((B:ℝ)*O) = C*P*((B:ℝ)*z+1+(B:ℝ)/O) := by
    unfold GridCounts.rho
    field_simp
    ring
  rw [he]
  have hb : 0 ≤ C*P*((B:ℝ)/O) := by positivity
  nlinarith

/-- End-to-end all-probe freezing from per-program soft-row bounds. Its
inputs contain only the actual rows of each program fan, not a final global
freezing conclusion or an independence assumption. -/
theorem complete_probe_freezing_from_rows (hO : 0 < O) (hB : 0 < B)
    (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (a C : ℝ) (ha : (P:ℝ)/O + GridCounts.rho B O ≤ a) (hsmall : a ≤ 1/(2:ℝ)^4096)
    (hC : 0 ≤ C)
    (hrows : ∀ k : Fin P,
      ((softRows ys ts rs false (104*a+outsideBudget O B P) k).card : ℝ) ≤
        C*((B:ℝ)*(104*a+outsideBudget O B P)+1))
    (χ : Edge O B P → Bool) (hmin : ∀ ζ, energy ys ts rs χ ≤ energy ys ts rs ζ) :
    ∃ b : Bool, ∃ ψ : Edge O B P → Bool,
      (∀ t : Fin B × Fin P, ψ (.inr (.inl t)) = frozenColor ys ts rs b (.inr (.inl t))) ∧
      (∀ e, (∀ t : Fin B × Fin P, e ≠ .inr (.inl t)) → ψ e = χ e) ∧
      (∀ x : Fin B × Fin O, ψ (.inl x) = χ (.inl x)) ∧
      0 ≤ energy ys ts rs ψ-energy ys ts rs χ ∧
      energy ys ts rs ψ-energy ys ts rs χ ≤
        2*(C*P/O)*(104*a+outsideBudget O B P+GridCounts.rho B O)*
          (104*a+outsideBudget O B P)*((B:ℝ)*O)^2 := by
  exact complete_probe_freezing hO hB ys ts rs hy ht hybox htbox hr a (C*P/O) ha hsmall
    (by positivity) (global_soft_from_rows hO hB ys ts rs (104*a+outsideBudget O B P) C hC hrows) χ hmin

end Q4.Candidate.CompleteProbeFreezing

#print axioms Q4.Candidate.CompleteProbeFreezing.crossingPairs_neighbors_nodup
#print axioms Q4.Candidate.CompleteProbeFreezing.mem_crossingPairs_neighbors
#print axioms Q4.Candidate.CompleteProbeFreezing.outside_neighbors_card_le
#print axioms Q4.Candidate.CompleteProbeFreezing.field_complement
#print axioms Q4.Candidate.CompleteProbeFreezing.complete_probe_freezing
#print axioms Q4.Candidate.CompleteProbeFreezing.field_eq_sum
#print axioms Q4.Candidate.CompleteProbeFreezing.global_soft_from_rows
#print axioms Q4.Candidate.CompleteProbeFreezing.complete_probe_freezing_from_rows
