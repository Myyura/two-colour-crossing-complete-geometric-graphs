import Q4.Candidate.CompleteProbeFreezing
import Q4.Candidate.RankSoftRows
import Q4.Candidate.OrdinarySoftRows
import Q4.Candidate.OrdinaryTablePreservation

namespace Q4.Candidate.CompleteFanFields

open Q4.Candidate.CompleteDrawing Q4.Candidate.CompleteProbeFreezing
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.VirtualColumnField Q4.Candidate.RankSoftRows
open Q4.Candidate.OrientationPreservation Q4.Candidate.UniformInsertion
attribute [local instance] Classical.propDecidable

variable {O B P : Nat}

/-- The actual complete crossing-list field is precisely the physical point
field used by both ordinary and rank fan calculations. T-edge orientation and
both finite summation orders are reconciled explicitly. -/
theorem full_field_eq_pointField (ys : Fin O → ℚ) (rs : Fin P → Point)
    (k : Fin P) (i : Fin B) :
    field ys (frameParameter B) rs false (.inr (.inl (i,k))) =
      pointField (spin : Fin B × Fin O → ℤ) ys (rs k) i := by
  rw [field_eq_sum,Fintype.sum_prod_type,Finset.sum_comm]
  unfold pointField
  apply Finset.sum_congr rfl
  intro j _
  unfold pointColumn
  apply Finset.sum_congr rfl
  intro t _
  have hc : Cross ys (frameParameter B) rs (.inr (.inl (i,k))) (.inl (t,j)) ↔
      ProperCross (rs k) (frame (frameParameter B i)) (original (ys j)) (frame (frameParameter B t)) := by
    exact (properCross_reverse_first _ _ _ _).symm
  simp only [hc]
  rfl

theorem full_softRows_eq_point (ys : Fin O → ℚ) (rs : Fin P → Point) (k : Fin P) (z : ℝ) :
    CompleteProbeFreezing.softRows ys (frameParameter B) rs false z k =
      actualSoftRows (B:=B) ys (rs k) z := by
  ext i
  simp only [CompleteProbeFreezing.softRows,actualSoftRows,Finset.mem_filter,Finset.mem_univ,
    true_and,full_field_eq_pointField]

theorem pointField_ordinary {r : Nat} (d : OrdinaryResponse.Geometry B O r) (k : Fin B) :
    pointField (spin : Fin B × Fin O → ℤ) d.ys (ordinary d.a d.mu) k =
      ordinaryField (spin : Fin B × Fin O → ℤ) d.ys d.a d.mu k := rfl

theorem pointSoftRows_ordinary {r : Nat} (d : OrdinaryResponse.Geometry B O r) (z : ℝ) :
    actualSoftRows (B:=B) d.ys (ordinary d.a d.mu) z = OrdinaryResponse.ordinarySoftRows d z := by
  rfl

/-- Ordinary prototype soft rows instantiated at a concrete program label. -/
theorem full_ordinary_soft_card {r : Nat} (d : OrdinaryResponse.Geometry B O r)
    (rs : Fin P → Point) (k : Fin P) (hk : rs k = ordinary d.a d.mu)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
    (hside : (r:ℝ)/O≤1/514 ∨ 1-1/514≤(r:ℝ)/O)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((CompleteProbeFreezing.softRows d.ys (frameParameter B) rs false z k).card:ℝ) ≤ 12*(B:ℝ)*z+3 := by
  rw [full_softRows_eq_point,hk,pointSoftRows_ordinary]
  exact OrdinaryResponse.ordinary_soft_card d hO hBO hr hW hside z hz hz1

/-- The placed ordinary point has exactly its prototype's full grid crossing
field, including parent clones and nonparent columns. -/
theorem placed_ordinary_field {r : Nat} (d : OrdinaryResponse.Geometry B O r)
    (M : Nat) (base prototypes : Finset Point) (p : Point)
    (hf : ∀ i, frame (frameParameter B i) ∈ base)
    (hy : ∀ j, original (d.ys j) ∈ base)
    (hp0 : ordinary d.a d.mu ∈ prototypes)
    (hproto : ∀ q ∈ prototypes, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius base prototypes) (ordinary d.a d.mu) p)
    (k : Fin B) :
    pointField (spin : Fin B × Fin O → ℤ) d.ys p k =
      ordinaryField (spin : Fin B × Fin O → ℤ) d.ys d.a d.mu k := by
  have hc (i : Fin B) (j : Fin O) :
      ProperCross p (frame (frameParameter B k)) (original (d.ys j)) (frame (frameParameter B i)) ↔
        ProperCross (ordinary d.a d.mu) (frame (frameParameter B k))
          (original (d.ys j)) (frame (frameParameter B i)) := by
    by_cases hj : j ∈ d.parent
    · exact (OrdinaryTablePreservation.placed_ordinary_clone_fan M B base prototypes d.even i k d.a (d.ys j) d.mu p
        d.unit_a (d.unit_y j) d.mu_pos d.mu_le (d.clone j hj) (hf i) (hf k) (hy j) hp0 hproto hp).trans
        (OrdinaryFan.ordinary_clone_indexed B d.even i k d.a (d.ys j) d.mu d.unit_a (d.unit_y j)
          d.mu_pos d.mu_le (d.clone j hj)).symm
    · exact (OrdinaryTablePreservation.placed_ordinary_nonparent_fan M B base prototypes i k d.a (d.ys j) d.mu p
        d.unit_a (d.unit_y j) d.mu_pos d.mu_le (d.sep j hj) (hf i) (hf k) (hy j) hp0 hproto hp).trans
        (OrdinaryFan.ordinary_nonparent_indexed B i k d.a (d.ys j) d.mu d.unit_a (d.unit_y j)
          d.mu_pos d.mu_le (d.sep j hj)).symm
  unfold pointField pointColumn ordinaryField ordinaryColumn
  simp_rw [hc]

/-- Actual final ordinary copies satisfy the same soft count; no crossing
preservation table or field estimate is taken as a premise. -/
theorem full_placed_ordinary_soft_card {r : Nat} (d : OrdinaryResponse.Geometry B O r)
    (M : Nat) (base prototypes : Finset Point) (rs : Fin P → Point) (k : Fin P)
    (hf : ∀ i, frame (frameParameter B i) ∈ base)
    (hy : ∀ j, original (d.ys j) ∈ base)
    (hp0 : ordinary d.a d.mu ∈ prototypes)
    (hproto : ∀ q ∈ prototypes, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius base prototypes) (ordinary d.a d.mu) (rs k))
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
    (hside : (r:ℝ)/O≤1/514 ∨ 1-1/514≤(r:ℝ)/O)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((CompleteProbeFreezing.softRows d.ys (frameParameter B) rs false z k).card:ℝ) ≤ 12*(B:ℝ)*z+3 := by
  rw [full_softRows_eq_point]
  have hset : actualSoftRows (B:=B) d.ys (rs k) z = OrdinaryResponse.ordinarySoftRows d z := by
    ext i
    simp only [actualSoftRows,OrdinaryResponse.ordinarySoftRows,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [placed_ordinary_field d M base prototypes (rs k) hf hy hp0 hproto hp]
    rfl
  rw [hset]
  exact OrdinaryResponse.ordinary_soft_card d hO hBO hr hW hside z hz hz1

/-- Left rank prototype instantiated in the actual full crossing graph. -/
theorem full_left_rank_soft_card {cut : Nat} (d : LeftGeometry B O cut)
    (rs : Fin P → Point) (k : Fin P) (hk : rs k = leftPoint d)
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((CompleteProbeFreezing.softRows d.ys (frameParameter B) rs false z k).card:ℝ) ≤ 12*(B:ℝ)*z+3 := by
  rw [full_softRows_eq_point,hk]
  exact left_soft_card d hO hBO hcut z hz hz1

/-- Right rank prototype instantiated in the actual full crossing graph. -/
theorem full_right_rank_soft_card {cut : Nat} (d : RightGeometry B O cut)
    (rs : Fin P → Point) (k : Fin P) (hk : rs k = rightPoint d)
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((CompleteProbeFreezing.softRows d.ys (frameParameter B) rs false z k).card:ℝ) ≤ 12*(B:ℝ)*z+3 := by
  rw [full_softRows_eq_point,hk]
  exact right_soft_card d hO hBO hcut z hz hz1

theorem full_placed_left_rank_soft_card {cut : Nat} (d : LeftGeometry B O cut)
    (M : Nat) (base prototypes : Finset Point) (rs : Fin P → Point) (k : Fin P)
    (hf : ∀ i, frame (frameParameter B i) ∈ base) (hy : ∀ j, original (d.ys j) ∈ base)
    (hp0 : leftPoint d ∈ prototypes) (hproto : ∀ q ∈ prototypes, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius base prototypes) (leftPoint d) (rs k))
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((CompleteProbeFreezing.softRows d.ys (frameParameter B) rs false z k).card:ℝ) ≤ 12*(B:ℝ)*z+3 := by
  rw [full_softRows_eq_point]
  exact placed_left_soft_card d M base prototypes (rs k) hf hy hp0 hproto hp hO hBO hcut z hz hz1

theorem full_placed_right_rank_soft_card {cut : Nat} (d : RightGeometry B O cut)
    (M : Nat) (base prototypes : Finset Point) (rs : Fin P → Point) (k : Fin P)
    (hf : ∀ i, frame (frameParameter B i) ∈ base) (hy : ∀ j, original (d.ys j) ∈ base)
    (hp0 : rightPoint d ∈ prototypes) (hproto : ∀ q ∈ prototypes, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius base prototypes) (rightPoint d) (rs k))
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((CompleteProbeFreezing.softRows d.ys (frameParameter B) rs false z k).card:ℝ) ≤ 12*(B:ℝ)*z+3 := by
  rw [full_softRows_eq_point]
  exact placed_right_soft_card d M base prototypes (rs k) hf hy hp0 hproto hp hO hBO hcut z hz hz1

/-- A program point is an actual common-radius placed ordinary/left-rank/
right-rank copy. This contains coordinate and index data, never a field,
soft-row, optimality, or freezing conclusion. -/
inductive ProgramWitness (ys : Fin O → ℚ) (M : Nat) (base prototypes : Finset Point) (p : Point) : Prop
  | ordinary {r : Nat} (d : OrdinaryResponse.Geometry B O r)
      (hys : d.ys = ys) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
      (hside : (r:ℝ)/O≤1/514 ∨ 1-1/514≤(r:ℝ)/O)
      (hmem : ordinary d.a d.mu ∈ prototypes)
      (hplaced : Placed M (constructionRadius base prototypes) (ordinary d.a d.mu) p) :
      ProgramWitness ys M base prototypes p
  | leftRank {cut : Nat} (d : LeftGeometry B O cut) (hys : d.ys = ys) (hcut : cut≤O)
      (hmem : leftPoint d ∈ prototypes)
      (hplaced : Placed M (constructionRadius base prototypes) (leftPoint d) p) :
      ProgramWitness ys M base prototypes p
  | rightRank {cut : Nat} (d : RightGeometry B O cut) (hys : d.ys = ys) (hcut : cut≤O)
      (hmem : rightPoint d ∈ prototypes)
      (hplaced : Placed M (constructionRadius base prototypes) (rightPoint d) p) :
      ProgramWitness ys M base prototypes p

theorem witnessed_valid (ys : Fin O → ℚ) (M : Nat) (base prototypes : Finset Point) (p : Point)
    (hw : ProgramWitness (B:=B) ys M base prototypes p) : (ConvexSeparation.Vertex.program p).valid := by
  cases hw with
  | ordinary _ _ _ _ _ _ hplaced => exact (Exists.choose_spec hplaced).2
  | leftRank _ _ _ _ hplaced => exact (Exists.choose_spec hplaced).2
  | rightRank _ _ _ _ hplaced => exact (Exists.choose_spec hplaced).2

theorem witnessed_soft_card (ys : Fin O → ℚ) (M : Nat) (base prototypes : Finset Point)
    (rs : Fin P → Point) (k : Fin P) (hw : ProgramWitness (B:=B) ys M base prototypes (rs k))
    (hf : ∀ i, frame (frameParameter B i) ∈ base) (hy : ∀ j, original (ys j) ∈ base)
    (hproto : ∀ q ∈ prototypes, phi q < 0 ∧ |q.2| < 2)
    (hO : 1000≤O) (hBO : O≤B) (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((CompleteProbeFreezing.softRows ys (frameParameter B) rs false z k).card:ℝ) ≤ 12*(B:ℝ)*z+3 := by
  cases hw with
  | ordinary d hys hr hW hside hmem hplaced =>
    have hyd : ∀ j, original (d.ys j) ∈ base := by simpa only [hys] using hy
    have hh := full_placed_ordinary_soft_card d M base prototypes rs k hf hyd hmem hproto hplaced
      hO hBO hr hW hside z hz hz1
    simpa only [hys] using hh
  | leftRank d hys hcut hmem hplaced =>
    have hyd : ∀ j, original (d.ys j) ∈ base := by simpa only [hys] using hy
    have hh := full_placed_left_rank_soft_card d M base prototypes rs k hf hyd hmem hproto hplaced
      hO hBO hcut z hz hz1
    simpa only [hys] using hh
  | rightRank d hys hcut hmem hplaced =>
    have hyd : ∀ j, original (d.ys j) ∈ base := by simpa only [hys] using hy
    have hh := full_placed_right_rank_soft_card d M base prototypes rs k hf hyd hmem hproto hplaced
      hO hBO hcut z hz hz1
    simpa only [hys] using hh

/-- All auxiliary fans freeze in the actual complete drawing from their
ordinary/rank coordinate witnesses. The soft-count interface is discharged. -/
theorem complete_freezing_from_program_geometry
    (ys : Fin O → ℚ) (M : Nat) (base prototypes : Finset Point) (rs : Fin P → Point)
    (hw : ∀ k, ProgramWitness (B:=B) ys M base prototypes (rs k))
    (hf : ∀ i, frame (frameParameter B i) ∈ base) (hy : ∀ j, original (ys j) ∈ base)
    (hproto : ∀ q ∈ prototypes, phi q < 0 ∧ |q.2| < 2)
    (hO : 1000≤O) (hBO : O≤B) (hys : StrictMono ys) (hybox : ∀ j, |ys j| ≤ 1)
    (a : ℝ) (ha : (P:ℝ)/O + GridCounts.rho B O ≤ a) (hsmall : a ≤ 1/(2:ℝ)^4096)
    (hz1 : 104*a+outsideBudget O B P ≤ 1/100)
    (χ : Edge O B P → Bool)
    (hmin : ∀ ζ, CompleteGridEnergy.energy ys (frameParameter B) rs χ ≤ CompleteGridEnergy.energy ys (frameParameter B) rs ζ) :
    ∃ b : Bool, ∃ ψ : Edge O B P → Bool,
      (∀ t : Fin B × Fin P, ψ (.inr (.inl t)) = frozenColor ys (frameParameter B) rs b (.inr (.inl t))) ∧
      (∀ e, (∀ t : Fin B × Fin P, e ≠ .inr (.inl t)) → ψ e = χ e) ∧
      (∀ x : Fin B × Fin O, ψ (.inl x) = χ (.inl x)) ∧
      0 ≤ CompleteGridEnergy.energy ys (frameParameter B) rs ψ-CompleteGridEnergy.energy ys (frameParameter B) rs χ ∧
      CompleteGridEnergy.energy ys (frameParameter B) rs ψ-CompleteGridEnergy.energy ys (frameParameter B) rs χ ≤
        2*(12*P/O)*(104*a+outsideBudget O B P+GridCounts.rho B O)*
          (104*a+outsideBudget O B P)*((B:ℝ)*O)^2 := by
  have hO0 : 0<O := by omega
  have hB0 : 0<B := by omega
  have ha0 : 0≤a := le_trans (add_nonneg (by positivity) (GridCounts.rho_nonneg B O)) ha
  have hz : 0≤104*a+outsideBudget O B P := add_nonneg (by positivity) outsideBudget_nonneg
  apply complete_probe_freezing_from_rows hO0 hB0 ys (frameParameter B) rs hys
    (frameParameter_antitone B) hybox (fun i => (frameParameter_unit B i).le)
    (fun k => witnessed_valid ys M base prototypes (rs k) (hw k)) a 12 ha hsmall (by norm_num) _ χ hmin
  intro k
  have hh := witnessed_soft_card ys M base prototypes rs k (hw k) hf hy hproto hO hBO
    (104*a+outsideBudget O B P) hz hz1
  linarith

end Q4.Candidate.CompleteFanFields

#print axioms Q4.Candidate.CompleteFanFields.full_field_eq_pointField
#print axioms Q4.Candidate.CompleteFanFields.full_ordinary_soft_card
#print axioms Q4.Candidate.CompleteFanFields.placed_ordinary_field
#print axioms Q4.Candidate.CompleteFanFields.full_placed_ordinary_soft_card
#print axioms Q4.Candidate.CompleteFanFields.full_left_rank_soft_card
#print axioms Q4.Candidate.CompleteFanFields.full_right_rank_soft_card
#print axioms Q4.Candidate.CompleteFanFields.full_placed_left_rank_soft_card
#print axioms Q4.Candidate.CompleteFanFields.full_placed_right_rank_soft_card
#print axioms Q4.Candidate.CompleteFanFields.witnessed_soft_card
#print axioms Q4.Candidate.CompleteFanFields.complete_freezing_from_program_geometry
