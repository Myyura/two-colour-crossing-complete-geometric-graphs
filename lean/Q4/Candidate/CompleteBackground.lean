import Q4.Candidate.CompleteFanFields
import Q4.Candidate.CompleteClassEnergy

/-! The common actual grid/TT/II background, complement symmetry, and
simultaneous witnesses. The known convex-frame optimum is an explicit theorem
interface; it is neither a custom axiom nor an exponential evaluation routine. -/
namespace Q4.Candidate.CompleteBackground
open Q4.Candidate.CompleteDrawing Q4.Candidate.CompleteGridEnergy
open Q4.Candidate.CompleteClassEnergy Q4.Candidate.CompleteProbeFreezing
open Q4.Candidate.ConvexSeparation
attribute [local instance] Classical.propDecidable
variable {O B P : ℕ}

def assemble (ξ : Fin B × Fin O → Bool) (τ : Fin B × Fin P → Bool)
    (κ : Inner O → Bool) (η : YEdge O P → Bool) (ι : Inner B → Bool) : Edge O B P → Bool
  | .inl x => ξ x
  | .inr (.inl t) => τ t
  | .inr (.inr (.inl c)) => κ c
  | .inr (.inr (.inr (.inl y))) => η y
  | .inr (.inr (.inr (.inr i))) => ι i

noncomputable def atom (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e f : Edge O B P) (c d : Bool) : ℝ := if Cross ys ts rs e f ∧ c=d then 1 else 0
noncomputable def fanUnary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (x : Fin B × Fin O) (c : Bool) : ℝ :=
  ∑ t, atom ys ts rs (.inl x) (T t) c (τ t)
noncomputable def gridValue (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (ξ : Fin B × Fin O → Bool) : ℝ :=
  GridLocalization.energy (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
    (fanUnary ys ts rs τ) ξ
noncomputable def fanValue (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) : ℝ := halfSum (fun t u => atom ys ts rs (T t) (T u) (τ t) (τ u))
noncomputable def frameValue (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (ι : Inner B → Bool) : ℝ := halfSum (fun i j => atom ys ts rs (I i) (I j) (ι i) (ι j))
noncomputable def coreValue (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (κ : Inner O → Bool) : ℝ :=
  halfSum (fun c d => atom ys ts rs (C c) (C d) (κ c) (κ d))+
  cutSum (fun c t => atom ys ts rs (C c) (T t) (κ c) (τ t))
noncomputable def frozenFans (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) (t : Fin B × Fin P) : Bool := frozenColor ys ts rs b (T t)
noncomputable def phaseValue (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) : ℝ :=
  GridLocalization.phaseEstimate (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
    (fanUnary ys ts rs (frozenFans ys ts rs b)) (CanonicalField.phase b)
noncomputable def background (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (z : ℝ) : ℝ := phaseValue ys ts rs false+fanValue ys ts rs (frozenFans ys ts rs false)+z

/-- The external known convex optimum supplies this finite lower-bound and
attainment certificate. No axiom is declared and no optimizer is used to
compute the baseline. -/
structure MinimumWitness {α : Type*} (f : α → ℝ) (v : ℝ) : Prop where
  lower : ∀ x, v≤f x
  attained : ∃ x, f x=v

theorem assemble_restrictions (χ : Edge O B P → Bool) :
    assemble (fun x => χ (.inl x)) (fun t => χ (T t)) (fun c => χ (C c))
      (fun y => χ (Y y)) (fun i => χ (I i)) = χ := by
  funext e
  rcases e with x | (t | (c | (y | i))) <;> rfl

theorem atom_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e f : Edge O B P) (c d : Bool) : atom ys ts rs e f (!c) (!d)=atom ys ts rs e f c d := by
  simp [atom]

theorem fanUnary_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (x : Fin B × Fin O) (c : Bool) :
    fanUnary ys ts rs (fun t => !(τ t)) x (!c)=fanUnary ys ts rs τ x c := by
  simp only [fanUnary,atom_complement]

theorem monoCount_complement {α : Type*} (es : List (α × α)) (χ : α → Bool) :
    Q4.monoCount es (fun x => !(χ x))=Q4.monoCount es χ := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Q4.monoCount,ih]

theorem gridValue_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (ξ : Fin B × Fin O → Bool) :
    gridValue ys ts rs (fun t => !(τ t)) (fun x => !(ξ x))=gridValue ys ts rs τ ξ := by
  simp only [gridValue,GridLocalization.energy,fanUnary_complement,monoCount_complement]

theorem flipOne_complement {α : Type*} [DecidableEq α] (χ : α → Bool) (v : α) :
    Q4.SimultaneousFlip.flipOne (fun x => !(χ x)) v=(fun x => !(Q4.SimultaneousFlip.flipOne χ v x)) := by
  funext x
  by_cases h : x=v <;> simp [Q4.SimultaneousFlip.flipOne,h]

theorem delta_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (ξ : Fin B × Fin O → Bool) (v : Fin B × Fin O) :
    GridLocalization.delta (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
      (fanUnary ys ts rs (fun t => !(τ t))) (fun x => !(ξ x)) v =
    GridLocalization.delta (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
      (fanUnary ys ts rs τ) ξ v := by
  unfold GridLocalization.delta
  rw [flipOne_complement]
  change gridValue _ _ _ _ _-gridValue _ _ _ _ _=gridValue _ _ _ _ _-gridValue _ _ _ _ _
  rw [gridValue_complement,gridValue_complement]

theorem phaseValue_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    phaseValue ys ts rs true=phaseValue ys ts rs false := by
  have hf : frozenFans ys ts rs true=(fun t => !(frozenFans ys ts rs false t)) := rfl
  have hc : (CanonicalField.phase true : Fin B × Fin O → Bool)=(fun x => !(CanonicalField.phase false x)) := rfl
  unfold phaseValue GridLocalization.phaseEstimate GridLocalization.linearFloor
  rw [hf,hc]
  change gridValue _ _ _ _ _+_=gridValue _ _ _ _ _+_
  rw [gridValue_complement]
  simp only [delta_complement]

theorem fanValue_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) : fanValue ys ts rs (fun t => !(τ t))=fanValue ys ts rs τ := by
  simp only [fanValue,atom_complement]

theorem coreValue_complement (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (κ : Inner O → Bool) :
    coreValue ys ts rs (fun t => !(τ t)) (fun c => !(κ c))=coreValue ys ts rs τ κ := by
  simp only [coreValue,atom_complement]

theorem common_background (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (b : Bool) (z : ℝ) :
    phaseValue ys ts rs b+fanValue ys ts rs (frozenFans ys ts rs b)+z=background ys ts rs z := by
  cases b
  · rfl
  · rw [phaseValue_complement]
    have hf : frozenFans ys ts rs true=(fun t => !(frozenFans ys ts rs false t)) := rfl
    rw [hf,fanValue_complement]
    rfl

theorem unary_eq_fanUnary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j|≤1) (htbox : ∀ i, |ts i|≤1)
    (hr : ∀ k, (Vertex.program (rs k)).valid) (χ : Edge O B P → Bool) :
    unary ys ts rs (fun r => χ (.inr r))=fanUnary ys ts rs (fun t => χ (T t)) := by
  funext x c
  rw [unary_eq_T ys ts rs hybox htbox hr]
  rfl

theorem full_decomposition (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j|≤1) (htbox : ∀ i, |ts i|≤1)
    (hr : ∀ k, (Vertex.program (rs k)).valid) (χ : Edge O B P → Bool) :
    energy ys ts rs χ = gridValue ys ts rs (fun t => χ (T t)) (fun x => χ (.inl x))+
      fanValue ys ts rs (fun t => χ (T t))+frameValue ys ts rs (fun i => χ (I i))+
      coreValue ys ts rs (fun t => χ (T t)) (fun c => χ (C c))+yRemainder ys ts rs χ := by
  have he := energy_grid_decomposition ys ts rs hy ht hybox htbox
    (fun x => χ (.inl x)) (fun r => χ (.inr r))
  rw [combine_restrictions] at he
  rw [outside_class_decomposition ys ts rs hybox htbox hr χ,unary_eq_fanUnary ys ts rs hybox htbox hr χ] at he
  change energy ys ts rs χ = gridValue _ _ _ _ _+((fanValue _ _ _ _+frameValue _ _ _ _)+
    coreValue _ _ _ _ _+yRemainder _ _ _ _) at he
  linarith

theorem core_minimum_phase (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (Mc : ℝ) (hMc : MinimumWitness (coreValue ys ts rs (frozenFans ys ts rs false)) Mc) (b : Bool) :
    MinimumWitness (coreValue ys ts rs (frozenFans ys ts rs b)) Mc := by
  cases b
  · exact hMc
  · have hf : frozenFans ys ts rs true=(fun t => !(frozenFans ys ts rs false t)) := rfl
    rw [hf]
    constructor
    · intro κ
      have hh := coreValue_complement ys ts rs (frozenFans ys ts rs false) (fun c => !(κ c))
      simp only [Bool.not_not] at hh
      rw [hh]
      exact hMc.lower _
    · obtain ⟨κ,hκ⟩ := hMc.attained
      exact ⟨fun c => !(κ c),(coreValue_complement ys ts rs _ κ).trans hκ⟩

theorem fanUnary_bounds (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (x : Fin B × Fin O) (c : Bool) :
    0≤fanUnary ys ts rs τ x c ∧ fanUnary ys ts rs τ x c≤(B:ℝ)*P := by
  unfold fanUnary atom
  constructor
  · exact Finset.sum_nonneg (by intro t _; split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ _t : Fin B × Fin P, (1:ℝ) := Finset.sum_le_sum (by intro t _; split_ifs <;> norm_num)
      _ = _ := by simp

theorem fanUnary_amplitude (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (x : Fin B × Fin O) :
    |fanUnary ys ts rs τ x true-fanUnary ys ts rs τ x false|≤(B:ℝ)*P := by
  have ht := fanUnary_bounds ys ts rs τ x true
  have hf := fanUnary_bounds ys ts rs τ x false
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Lower bound for any fixed-fan coloring whose grid retains the localized
support in that same phase. Optimality of the recolored grid is not assumed. -/
theorem frozen_lower (hO : 0<O) (hB : 0<B)
    (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j|≤1) (htbox : ∀ i, |ts i|≤1)
    (hr : ∀ k, (Vertex.program (rs k)).valid)
    (a z Mc : ℝ) (ha0 : 0≤a) (hasmall : a≤1/65536) (hrho : GridCounts.rho B O≤a)
    (hz : MinimumWitness (frameValue ys ts rs) z)
    (hMc : MinimumWitness (coreValue ys ts rs (frozenFans ys ts rs false)) Mc)
    (b : Bool) (F : Finset (Fin B × Fin O)) (ψ : Edge O B P → Bool)
    (hF : F⊆GridCounts.strip B O (220*a)∪GridCounts.corners B O (220*a))
    (hgrid : (fun x => ψ (.inl x))=Q4.SimultaneousFlip.flip (CanonicalField.phase b) (GridLocalization.membershipMask F))
    (hfrozen : ∀ t, ψ (T t)=frozenFans ys ts rs b t) :
    background ys ts rs z+Mc-2^32*a^3*((B:ℝ)*O)^2≤energy ys ts rs ψ := by
  have hτ : (fun t => ψ (T t))=frozenFans ys ts rs b := funext hfrozen
  have he := full_decomposition ys ts rs hy ht hybox htbox hr ψ
  rw [hτ] at he
  have hg := GridLocalization.localized_grid_energy_lower B O hB hO F a
    (fanUnary ys ts rs (frozenFans ys ts rs b)) (CanonicalField.phase b) ha0 hasmall hrho hF
  rw [←hgrid] at hg
  change phaseValue ys ts rs b-2^32*a^3*((B:ℝ)*O)^2≤gridValue ys ts rs (frozenFans ys ts rs b) _ at hg
  have hi := hz.lower (fun i => ψ (I i))
  have hc := (core_minimum_phase ys ts rs Mc hMc b).lower (fun c => ψ (C c))
  have hY := (yRemainder_bounds ys ts rs ψ).1
  have hcommon := common_background ys ts rs b z
  linarith

/-- One actual full coloring simultaneously realizes the prescribed grid
witness, a minimizing core coloring and a minimizing isolated frame coloring.
Y is assigned an explicit arbitrary bit and its full cost is charged. -/
theorem simultaneous_upper (hO : 0<O) (hB : 0<B)
    (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j|≤1) (htbox : ∀ i, |ts i|≤1)
    (hr : ∀ k, (Vertex.program (rs k)).valid)
    (a z Mc : ℝ) (ha : (P:ℝ)/O+GridCounts.rho B O≤a) (hasmall : a≤1/65536)
    (hz : MinimumWitness (frameValue ys ts rs) z)
    (hMc : MinimumWitness (coreValue ys ts rs (frozenFans ys ts rs false)) Mc) :
    ∃ ψ : Edge O B P → Bool,
      (∀ t, ψ (T t)=frozenFans ys ts rs false t) ∧
      energy ys ts rs ψ≤background ys ts rs z+Mc+2^32*a^3*((B:ℝ)*O)^2+
        (Fintype.card (YEdge O P):ℝ)*((B:ℝ)*P+Fintype.card (Inner O))+
        (Fintype.card (YEdge O P):ℝ)^2/2 := by
  let τ := frozenFans ys ts rs false
  let ξ := Q4.SimultaneousFlip.flip (CanonicalField.phase false)
    (GridLocalization.negativeMask (GridLocalization.gridVertices B O) (GridLocalization.gridEdges B O)
      (fanUnary ys ts rs τ) (CanonicalField.phase false))
  obtain ⟨κ,hκ⟩ := hMc.attained
  obtain ⟨ι,hι⟩ := hz.attained
  let ψ := assemble ξ τ κ (fun _ => false) ι
  have hO0 : (O:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hO
  have hg := (CanonicalField.canonical_phase_upper B O hB hO (fanUnary ys ts rs τ)
    ((P:ℝ)/O) a false (by positivity) ha hasmall (by
      intro x
      have he : ((P:ℝ)/O)*((B:ℝ)*O)=(B:ℝ)*P := by field_simp
      rw [he]
      exact fanUnary_amplitude ys ts rs τ x)).2
  change gridValue ys ts rs τ ξ≤phaseValue ys ts rs false+2^32*a^3*((B:ℝ)*O)^2 at hg
  have he := full_decomposition ys ts rs hy ht hybox htbox hr ψ
  change energy ys ts rs ψ=gridValue ys ts rs τ ξ+fanValue ys ts rs τ+frameValue ys ts rs ι+
    coreValue ys ts rs τ κ+yRemainder ys ts rs ψ at he
  have hycost := (yRemainder_bounds ys ts rs ψ).2
  refine ⟨ψ,fun _ => rfl,?_⟩
  change coreValue ys ts rs τ κ=Mc at hκ
  unfold background
  dsimp only [τ] at he hg hκ
  linarith

/-- The sequential real-cost freezing kernel with a specified phase and
specified disagreement set. Keeping these witnesses is essential: a later
independent existential phase would not justify the frozen lower bound. -/
theorem freeze_in_phase (hO : 0<O) (hB : 0<B)
    (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hybox : ∀ j, |ys j|≤1) (htbox : ∀ i, |ts i|≤1)
    (hr : ∀ k, (Vertex.program (rs k)).valid)
    (a Q : ℝ) (ha0 : 0≤a) (hQ : 0≤Q) (b : Bool) (F : Finset (Fin B × Fin O))
    (χ : Edge O B P → Bool) (hmin : ∀ ζ, energy ys ts rs χ≤energy ys ts rs ζ)
    (hχ : (fun x => χ (.inl x))=Q4.SimultaneousFlip.flip (CanonicalField.phase b) (GridLocalization.membershipMask F))
    (hF : (F.card:ℝ)≤52*a*((B:ℝ)*O))
    (hsoft : ((ProbeFreezing.realSoftProbes (probes O B P) (field ys ts rs b)
      ((104*a+outsideBudget O B P)*((B:ℝ)*O))).length:ℝ)≤
      Q*(104*a+outsideBudget O B P+GridCounts.rho B O)*((B:ℝ)*O)) :
    ∃ ψ : Edge O B P → Bool,
      (∀ t, ψ (T t)=frozenFans ys ts rs b t) ∧
      (∀ x : Fin B × Fin O, ψ (.inl x)=χ (.inl x)) ∧
      energy ys ts rs ψ-energy ys ts rs χ≤
        2*Q*(104*a+outsideBudget O B P+GridCounts.rho B O)*
          (104*a+outsideBudget O B P)*((B:ℝ)*O)^2 := by
  let fs : List (Edge O B P) := F.toList.map Sum.inl
  have hsupp : ∀ e, grid e=true → χ e≠reference b e → e∈fs := by
    intro e he hc
    rcases e with x | r
    · have hx : x∈F := by
        by_contra hx
        have hh := congrFun hχ x
        simp only [Q4.SimultaneousFlip.flip,GridLocalization.membershipMask,decide_eq_false hx] at hh
        exact hc (hh.trans (reference_X b x).symm)
      exact List.mem_map.mpr ⟨x,Finset.mem_toList.mpr hx,rfl⟩
    · simp [grid] at he
  have hsize : (fs.length:ℝ)≤52*a*(B*O:Nat) := by
    simpa only [fs,List.length_map,Finset.length_toList,Nat.cast_mul] using hF
  have hdeg : ∀ e, e∈probes O B P →
      ((ProbeFreezing.outsideNeighbors (crossingPairs ys ts rs).toList grid e).length:ℝ)≤outsideBudget O B P*(B*O:Nat) := by
    intro e he
    obtain ⟨t,rfl⟩ := (mem_probes e).mp he
    simpa only [Nat.cast_mul,outsideBudget_mul hO hB] using outside_neighbors_card_le ys ts rs hybox htbox hr t
  have hminimum : ∀ ζ, ProbeFreezing.energy (crossingPairs ys ts rs).toList χ≤
      ProbeFreezing.energy (crossingPairs ys ts rs).toList ζ := by
    intro ζ
    have hh := hmin ζ
    unfold energy ProbeFreezing.energy at *
    exact_mod_cast hh
  have hsoft' : ((ProbeFreezing.realSoftProbes (probes O B P) (field ys ts rs b)
      ((104*a+outsideBudget O B P)*(B*O:Nat))).length:ℝ)≤
      Q*(104*a+outsideBudget O B P+GridCounts.rho B O)*(B*O:Nat) := by
    simpa only [Nat.cast_mul] using hsoft
  obtain ⟨ψ,hψ,_,hgrid,_,hcost⟩ := ProbeFreezing.probe_freezing_real
    (crossingPairs ys ts rs).toList grid χ (reference b) (frozenColor ys ts rs b) fs (probes O B P) (B*O)
    a (outsideBudget O B P) (GridCounts.rho B O) Q ha0 outsideBudget_nonneg (GridCounts.rho_nonneg B O) hQ
    (crossingPairs_loopless ys ts rs) (fun e _ => crossingPairs_neighbors_nodup ys ts rs e)
    (by intro e he; obtain ⟨t,rfl⟩ := (mem_probes e).mp he; rfl)
    hsupp hsize hdeg (fun e _ => frozenColor_best ys ts rs b e) hminimum hsoft'
  refine ⟨ψ,fun t => hψ _ ((mem_probes _).mpr ⟨t,rfl⟩),fun x => hgrid _ rfl,?_⟩
  unfold ProbeFreezing.energy at hcost
  push_cast at hcost
  simpa only [energy,Nat.cast_mul] using hcost

open Q4.Candidate.DoubleCapGrid in
/-- Actual complete-graph optimum interval around one common background.
Every probe count is derived from the actual program geometry. The two finite
minimum certificates concern disjoint I and C variables after T is fixed. -/
theorem complete_minimum_interval
    (ys : Fin O → ℚ) (M : Nat) (base prototypes : Finset Point) (rs : Fin P → Point)
    (hw : ∀ k, CompleteFanFields.ProgramWitness (B:=B) ys M base prototypes (rs k))
    (hf : ∀ i, frame (frameParameter B i)∈base) (hybase : ∀ j, original (ys j)∈base)
    (hproto : ∀ q∈prototypes, phi q<0 ∧ |q.2|<2)
    (hO : 1000≤O) (hBO : O≤B) (hys : StrictMono ys) (hybox : ∀ j, |ys j|≤1)
    (a z Mc : ℝ) (ha : (P:ℝ)/O+GridCounts.rho B O≤a) (hsmall : a≤1/(2:ℝ)^4096)
    (hz1 : 104*a+outsideBudget O B P≤1/100)
    (hz : MinimumWitness (frameValue ys (frameParameter B) rs) z)
    (hMc : MinimumWitness (coreValue ys (frameParameter B) rs (frozenFans ys (frameParameter B) rs false)) Mc)
    (χ : Edge O B P → Bool)
    (hmin : ∀ ζ, energy ys (frameParameter B) rs χ≤energy ys (frameParameter B) rs ζ) :
    background ys (frameParameter B) rs z+Mc-2^32*a^3*((B:ℝ)*O)^2-
      2*(12*P/O)*(104*a+outsideBudget O B P+GridCounts.rho B O)*
        (104*a+outsideBudget O B P)*((B:ℝ)*O)^2≤energy ys (frameParameter B) rs χ ∧
    energy ys (frameParameter B) rs χ≤background ys (frameParameter B) rs z+Mc+
      2^32*a^3*((B:ℝ)*O)^2+(Fintype.card (YEdge O P):ℝ)*((B:ℝ)*P+Fintype.card (Inner O))+
        (Fintype.card (YEdge O P):ℝ)^2/2 := by
  have hO0 : 0<O := by omega
  have hB0 : 0<B := by omega
  have hr : ∀ k, (Vertex.program (rs k)).valid :=
    fun k => CompleteFanFields.witnessed_valid ys M base prototypes (rs k) (hw k)
  have htbox : ∀ i, |frameParameter B i|≤1 := fun i => (frameParameter_unit B i).le
  have hrho : GridCounts.rho B O≤a := by
    have hp : (0:ℝ)≤P/O := by positivity
    linarith
  have ha0 : 0≤a := (GridCounts.rho_nonneg B O).trans hrho
  have hasmall : a≤1/65536 := hsmall.trans (by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ)<65536)
    have hh : (2:ℝ)^16≤2^4096 := pow_le_pow_right₀ (by norm_num) (by omega : 16≤4096)
    norm_num at hh ⊢
    exact hh)
  constructor
  · obtain ⟨b,F,hχ,hF,hFloc⟩ := complete_minimizer_localization hO0 hB0 ys (frameParameter B) rs
      hys (frameParameter_antitone B) hybox htbox hr a ha hsmall χ hmin
    have hrows (k : Fin P) : ((softRows ys (frameParameter B) rs false (104*a+outsideBudget O B P) k).card:ℝ)≤
        12*((B:ℝ)*(104*a+outsideBudget O B P)+1) := by
      have hh := CompleteFanFields.witnessed_soft_card ys M base prototypes rs k (hw k) hf hybase hproto
        hO hBO (104*a+outsideBudget O B P) (add_nonneg (by positivity) outsideBudget_nonneg) hz1
      linarith
    have hsoft := global_soft_from_rows hO0 hB0 ys (frameParameter B) rs (104*a+outsideBudget O B P) 12 (by norm_num) hrows b
    obtain ⟨ψ,hψ,hgrid,hcost⟩ := freeze_in_phase hO0 hB0 ys (frameParameter B) rs hybox htbox hr
      a (12*P/O) ha0 (by positivity) b F χ hmin hχ hF hsoft
    have hgrid' : (fun x => ψ (.inl x))=Q4.SimultaneousFlip.flip (CanonicalField.phase b) (GridLocalization.membershipMask F) := by
      funext x
      exact (hgrid x).trans (congrFun hχ x)
    have hl := frozen_lower hO0 hB0 ys (frameParameter B) rs hys (frameParameter_antitone B) hybox htbox hr
      a z Mc ha0 hasmall hrho hz hMc b F ψ hFloc hgrid' hψ
    linarith
  · obtain ⟨ψ,_,hu⟩ := simultaneous_upper hO0 hB0 ys (frameParameter B) rs hys (frameParameter_antitone B)
      hybox htbox hr a z Mc ha hasmall hz hMc
    exact (hmin ψ).trans hu

end Q4.Candidate.CompleteBackground
#print axioms Q4.Candidate.CompleteBackground.phaseValue_complement
#print axioms Q4.Candidate.CompleteBackground.common_background
#print axioms Q4.Candidate.CompleteBackground.full_decomposition
#print axioms Q4.Candidate.CompleteBackground.core_minimum_phase
#print axioms Q4.Candidate.CompleteBackground.frozen_lower
#print axioms Q4.Candidate.CompleteBackground.simultaneous_upper
#print axioms Q4.Candidate.CompleteBackground.freeze_in_phase
#print axioms Q4.Candidate.CompleteBackground.complete_minimum_interval
