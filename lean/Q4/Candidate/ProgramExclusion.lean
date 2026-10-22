import Q4.Candidate.ProgramCatalog

/-! Exact zero cost, not merely zero signed field, for core chords excluded
by every program macro's actual geometric curvature margin. -/
namespace Q4.Candidate.ProgramExclusion
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.ProgramCount Q4.Candidate.ProgramCatalog
open Q4.Candidate.RankResponse Q4.Candidate.RankSoftRows
open Q4.Candidate.OrientationPreservation Q4.Candidate.UniformInsertion
open scoped BigOperators

/-- All four actual catalog branches are checked against the actual core
chord. This is the interface used for a dummy chord lying outside every
program parent block. -/
theorem all_no_cross {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcMem : original c∈p.base) (hbMem : original b∈p.base)
    (hother : ∀j, Nonincident g j c b) (l : Label d gaps) (k : Fin B) :
    ¬ProperCross (p.points l) (frame (frameParameter B k)) (original c) (original b) := by
  rcases l with ⟨j,i⟩|⟨j,i⟩|⟨j,a,i⟩|⟨j,a,i⟩
  · exact OrdinaryNonincident.placed_ordinary_nonincident_no_cross p.M p.base p.prototypes
      (g.ordinaryLeft j).2.a c b (g.ordinaryLeft j).2.mu (frameParameter B k) _
      (g.ordinaryLeft j).2.unit_a hc hb (frameParameter_unit B k).le (g.ordinaryLeft j).2.mu_pos
      (hother j).ordinary_left (p.frame_mem k) hcMem hbMem (p.prototype_mem (.inl ⟨j,i⟩))
      p.proto_below (p.placed (.inl ⟨j,i⟩))
  · exact OrdinaryNonincident.placed_ordinary_nonincident_no_cross p.M p.base p.prototypes
      (g.ordinaryRight j).2.a c b (g.ordinaryRight j).2.mu (frameParameter B k) _
      (g.ordinaryRight j).2.unit_a hc hb (frameParameter_unit B k).le (g.ordinaryRight j).2.mu_pos
      (hother j).ordinary_right (p.frame_mem k) hcMem hbMem (p.prototype_mem (.inr (.inl ⟨j,i⟩)))
      p.proto_below (p.placed (.inr (.inl ⟨j,i⟩)))
  · let r := (g.rankLeft j a).2
    exact RankNonincident.placed_leftRank_nonincident p.M p.base p.prototypes
      r.a r.b r.tau r.w r.mu r.ell c b (frameParameter B k) _
      r.ordered r.width r.mu_pos r.mu_small r.tau_pos r.tau_small r.box_a r.box_b r.gap_lo r.gap_hi
      hc hb (frameParameter_unit B k).le ((hother j).rank_left a) (p.frame_mem k) hcMem hbMem
      (p.prototype_mem (.inr (.inr (.inl ⟨j,a,i⟩)))) p.proto_below (p.placed (.inr (.inr (.inl ⟨j,a,i⟩))))
  · let r := (g.rankRight j a).2
    exact RankNonincident.placed_rightRank_nonincident p.M p.base p.prototypes
      r.a r.b r.tau r.w r.mu r.ell c b (frameParameter B k) _
      r.ordered r.width r.mu_pos r.mu_small r.tau_pos r.tau_small r.box_a r.box_b r.gap_lo r.gap_hi
      hc hb (frameParameter_unit B k).le ((hother j).rank_right a) (p.frame_mem k) hcMem hbMem
      (p.prototype_mem (.inr (.inr (.inr ⟨j,a,i⟩)))) p.proto_below (p.placed (.inr (.inr (.inr ⟨j,a,i⟩))))

/-- The total actual program cost on the excluded chord is identically zero
for both colors, so no extra unknown dummy baseline is introduced. -/
theorem cost_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcMem : original c∈p.base) (hbMem : original b∈p.base)
    (hother : ∀j, Nonincident g j c b) (color : Bool) :
    ProgramField.cost (B:=B) d g.ys p.points (original c) (original b) color=0 := by
  classical
  unfold ProgramField.cost RankResponse.coreCost
  simp only [all_no_cross d g p c b hc hb hcMem hbMem hother,ite_false,Finset.sum_const_zero]

/-- In particular every excluded chord has zero aggregate field. -/
theorem field_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcMem : original c∈p.base) (hbMem : original b∈p.base)
    (hother : ∀j, Nonincident g j c b) :
    ProgramField.field (B:=B) d g.ys p.points (original c) (original b)=0 := by
  rw [←ProgramField.cost_difference,cost_zero d g p c b hc hb hcMem hbMem hother,
    cost_zero d g p c b hc hb hcMem hbMem hother,sub_self]

end Q4.Candidate.ProgramExclusion
#print axioms Q4.Candidate.ProgramExclusion.all_no_cross
#print axioms Q4.Candidate.ProgramExclusion.cost_zero
#print axioms Q4.Candidate.ProgramExclusion.field_zero
