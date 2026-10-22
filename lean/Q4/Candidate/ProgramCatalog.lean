import Q4.Candidate.ProgramField
import Q4.Candidate.RankNonincident

/-! Coordinate data and actual placed points for the computed four-family
program catalog. No field or crossing table is stored in the data package. -/
namespace Q4.Candidate.ProgramCatalog
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.ProgramCount Q4.Candidate.ProgramField
open Q4.Candidate.RankResponse Q4.Candidate.RankSoftRows
open Q4.Candidate.OrientationPreservation Q4.Candidate.UniformInsertion
open scoped BigOperators

structure Geometries (S gaps B O : ℕ) where
  ys : Fin O → ℚ
  ordinaryLeft : Fin S → Σ cut, OrdinaryResponse.Geometry B O cut
  ordinaryRight : Fin S → Σ cut, OrdinaryResponse.Geometry B O cut
  rankLeft : Fin S → Fin gaps → Σ cut, LeftGeometry B O cut
  rankRight : Fin S → Fin gaps → Σ cut, RightGeometry B O cut
  ys_ol : ∀j, (ordinaryLeft j).2.ys=ys
  ys_or : ∀j, (ordinaryRight j).2.ys=ys
  ys_rl : ∀j g, (rankLeft j g).2.ys=ys
  ys_rr : ∀j g, (rankRight j g).2.ys=ys

noncomputable def Geometries.prototypes {S gaps B O : ℕ} (g : Geometries S gaps B O) :
    Prototypes S gaps where
  ordinaryLeft j := ConvexSeparation.ordinary (g.ordinaryLeft j).2.a (g.ordinaryLeft j).2.mu
  ordinaryRight j := ConvexSeparation.ordinary (g.ordinaryRight j).2.a (g.ordinaryRight j).2.mu
  rankLeft j h := leftPoint (g.rankLeft j h).2
  rankRight j h := rightPoint (g.rankRight j h).2

structure Placement {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O) where
  M : ℕ
  base : Finset Point
  prototypes : Finset Point
  points : Label d gaps → Point
  frame_mem : ∀k, frame (frameParameter B k)∈base
  original_mem : ∀j, original (g.ys j)∈base
  prototype_mem : ∀l, prototype d g.prototypes l∈prototypes
  proto_below : ∀q∈prototypes, phi q<0 ∧ |q.2|<2
  placed : ∀l, Placed M (constructionRadius base prototypes) (prototype d g.prototypes l) (points l)

/-- Genuine geometric exclusion of every row of a placed left-rank fan. -/
theorem left_nonincident_zero {N O cut : ℕ} (d : LeftGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀k, frame (frameParameter N k)∈B)
    (hr : leftPoint d∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (leftPoint d) p)
    (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcurve : 200*d.mu*(d.b-d.a)< |c-d.a| * |b-d.a|)
    (hcMem : original c∈B) (hbMem : original b∈B) :
    coreCoefficient (B:=N) d.ys p (original c) (original b)=0 := by
  classical
  unfold coreCoefficient
  apply Finset.sum_eq_zero
  intro k _
  have hn := RankNonincident.placed_leftRank_nonincident M B R
    d.a d.b d.tau d.w d.mu d.ell c b (frameParameter N k) p d.ordered d.width
    d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b d.gap_lo d.gap_hi
    hc hb (frameParameter_unit N k).le hcurve (hf k) hcMem hbMem hr hproto hp
  simp [hn]

theorem right_nonincident_zero {N O cut : ℕ} (d : RightGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀k, frame (frameParameter N k)∈B)
    (hr : rightPoint d∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (rightPoint d) p)
    (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcurve : 200*d.mu*(d.b-d.a)< |c-d.b| * |b-d.b|)
    (hcMem : original c∈B) (hbMem : original b∈B) :
    coreCoefficient (B:=N) d.ys p (original c) (original b)=0 := by
  classical
  unfold coreCoefficient
  apply Finset.sum_eq_zero
  intro k _
  have hn := RankNonincident.placed_rightRank_nonincident M B R
    d.a d.b d.tau d.w d.mu d.ell c b (frameParameter N k) p d.ordered d.width
    d.mu_pos d.mu_small d.tau_pos d.tau_small d.box_a d.box_b d.gap_lo d.gap_hi
    hc hb (frameParameter_unit N k).le hcurve (hf k) hcMem hbMem hr hproto hp
  simp [hn]

/-- The actual catalog objective partitions over macro labels, gap labels,
and copies. All four families remain explicitly present. -/
theorem field_eq_groups {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (x y : Point) :
    field (B:=B) d g.ys p.points x y=
      ∑ j : Fin S,
        ((∑ i : Fin (ordinaryLeft d j), coreCoefficient (B:=B) g.ys (p.points (.inl ⟨j,i⟩)) x y)+
        (∑ i : Fin (ordinaryRight d j), coreCoefficient (B:=B) g.ys (p.points (.inr (.inl ⟨j,i⟩))) x y)+
        (∑ h : Fin gaps, ∑ i : Fin (rankLeft d j h.val),
          coreCoefficient (B:=B) g.ys (p.points (.inr (.inr (.inl ⟨j,h,i⟩)))) x y)+
        (∑ h : Fin gaps, ∑ i : Fin (rankRight d j h.val),
          coreCoefficient (B:=B) g.ys (p.points (.inr (.inr (.inr ⟨j,h,i⟩)))) x y)) := by
  unfold field
  simp only [Label,Fintype.sum_sum_type,Fintype.sum_sigma,Finset.sum_add_distrib]
  ring

/-- A macro unrelated to the core edge contributes exactly zero, by its
ordinary and rank curvature margins on the actual endpoints. -/
theorem group_nonincident_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcMem : original c∈p.base) (hbMem : original b∈p.base)
    (hOL : 1200*(g.ordinaryLeft j).2.mu< |c-(g.ordinaryLeft j).2.a| * |b-(g.ordinaryLeft j).2.a|)
    (hOR : 1200*(g.ordinaryRight j).2.mu< |c-(g.ordinaryRight j).2.a| * |b-(g.ordinaryRight j).2.a|)
    (hRL : ∀h, 200*(g.rankLeft j h).2.mu*((g.rankLeft j h).2.b-(g.rankLeft j h).2.a)<
      |c-(g.rankLeft j h).2.a| * |b-(g.rankLeft j h).2.a|)
    (hRR : ∀h, 200*(g.rankRight j h).2.mu*((g.rankRight j h).2.b-(g.rankRight j h).2.a)<
      |c-(g.rankRight j h).2.b| * |b-(g.rankRight j h).2.b|) :
    ((∑ i : Fin (ordinaryLeft d j), coreCoefficient (B:=B) g.ys (p.points (.inl ⟨j,i⟩)) (original c) (original b))+
      (∑ i : Fin (ordinaryRight d j), coreCoefficient (B:=B) g.ys (p.points (.inr (.inl ⟨j,i⟩))) (original c) (original b))+
      (∑ h : Fin gaps, ∑ i : Fin (rankLeft d j h.val), coreCoefficient (B:=B) g.ys
        (p.points (.inr (.inr (.inl ⟨j,h,i⟩)))) (original c) (original b))+
      (∑ h : Fin gaps, ∑ i : Fin (rankRight d j h.val), coreCoefficient (B:=B) g.ys
        (p.points (.inr (.inr (.inr ⟨j,h,i⟩)))) (original c) (original b)))=0 := by
  have hL (i : Fin (ordinaryLeft d j)) : coreCoefficient (B:=B) g.ys
      (p.points (.inl ⟨j,i⟩)) (original c) (original b)=0 := by
    rw [←g.ys_ol j]
    exact PlacedOrdinaryField.placed_nonincident_coefficient_zero (g.ordinaryLeft j).2
      p.M p.base p.prototypes _ p.frame_mem (p.prototype_mem (.inl ⟨j,i⟩))
      p.proto_below (p.placed (.inl ⟨j,i⟩)) c b hc hb hOL hcMem hbMem
  have hR (i : Fin (ordinaryRight d j)) : coreCoefficient (B:=B) g.ys
      (p.points (.inr (.inl ⟨j,i⟩))) (original c) (original b)=0 := by
    rw [←g.ys_or j]
    exact PlacedOrdinaryField.placed_nonincident_coefficient_zero (g.ordinaryRight j).2
      p.M p.base p.prototypes _ p.frame_mem (p.prototype_mem (.inr (.inl ⟨j,i⟩)))
      p.proto_below (p.placed (.inr (.inl ⟨j,i⟩))) c b hc hb hOR hcMem hbMem
  have hRL' (h : Fin gaps) (i : Fin (rankLeft d j h.val)) : coreCoefficient (B:=B) g.ys
      (p.points (.inr (.inr (.inl ⟨j,h,i⟩)))) (original c) (original b)=0 := by
    rw [←g.ys_rl j h]
    exact left_nonincident_zero (g.rankLeft j h).2 p.M p.base p.prototypes _
      p.frame_mem (p.prototype_mem (.inr (.inr (.inl ⟨j,h,i⟩)))) p.proto_below
      (p.placed (.inr (.inr (.inl ⟨j,h,i⟩)))) c b hc hb (hRL h) hcMem hbMem
  have hRR' (h : Fin gaps) (i : Fin (rankRight d j h.val)) : coreCoefficient (B:=B) g.ys
      (p.points (.inr (.inr (.inr ⟨j,h,i⟩)))) (original c) (original b)=0 := by
    rw [←g.ys_rr j h]
    exact right_nonincident_zero (g.rankRight j h).2 p.M p.base p.prototypes _
      p.frame_mem (p.prototype_mem (.inr (.inr (.inr ⟨j,h,i⟩)))) p.proto_below
      (p.placed (.inr (.inr (.inr ⟨j,h,i⟩)))) c b hc hb (hRR h) hcMem hbMem
  simp only [hL,hR,hRL',hRR',Finset.sum_const_zero,add_zero]


noncomputable def groupField {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (x y : Point) : ℤ :=
    (∑ i : Fin (ordinaryLeft d j), coreCoefficient (B:=B) g.ys (p.points (.inl ⟨j,i⟩)) x y)+
    (∑ i : Fin (ordinaryRight d j), coreCoefficient (B:=B) g.ys (p.points (.inr (.inl ⟨j,i⟩))) x y)+
    (∑ h : Fin gaps, ∑ i : Fin (rankLeft d j h.val),
      coreCoefficient (B:=B) g.ys (p.points (.inr (.inr (.inl ⟨j,h,i⟩)))) x y)+
    (∑ h : Fin gaps, ∑ i : Fin (rankRight d j h.val),
      coreCoefficient (B:=B) g.ys (p.points (.inr (.inr (.inr ⟨j,h,i⟩)))) x y)

theorem field_eq_sum_groupField {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (x y : Point) :
    field (B:=B) d g.ys p.points x y=∑j, groupField d g p j x y := field_eq_groups d g p x y

theorem coefficient_reverse {B O : ℕ} (ys : Fin O → ℚ) (p x y : Point) :
    coreCoefficient (B:=B) ys p x y=coreCoefficient (B:=B) ys p y x := by
  classical
  unfold coreCoefficient
  simp only [RankGap.properCross_reverse_second]

/-- Compatibility with one actual selected core edge. The rank weights in
the integer recipe are explicitly the actual prototype response weights.
The remaining fields are coordinate equations and separation inequalities;
there is no assumed copy coefficient, total field, or residual estimate. -/
structure Selected {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (j : Fin S) (W : ℕ) (s t : Fin W) (c b : ℚ) : Prop where
  unit_c : |c|≤1
  unit_b : |b|≤1
  ordinary_left_clone : 3*((B:ℚ)+1)*|c-(g.ordinaryLeft j).2.a|≤(g.ordinaryLeft j).2.mu
  ordinary_left_sep : 5*(g.ordinaryLeft j).2.mu≤|b-(g.ordinaryLeft j).2.a|
  ordinary_right_clone : 3*((B:ℚ)+1)*|b-(g.ordinaryRight j).2.a|≤(g.ordinaryRight j).2.mu
  ordinary_right_sep : 5*(g.ordinaryRight j).2.mu≤|c-(g.ordinaryRight j).2.a|
  left_width : ∀h, (g.rankLeft j h).2.w=(W:ℚ)
  left_gap : ∀h, (g.rankLeft j h).2.ell=(h.val:ℚ)
  left_c : ∀h, c=RankGap.cloneAt (g.rankLeft j h).2.a (g.rankLeft j h).2.tau W s.val
  left_b : ∀h, b=RankGap.cloneAt (g.rankLeft j h).2.b (g.rankLeft j h).2.tau W t.val
  right_width : ∀h, (g.rankRight j h).2.w=(W:ℚ)
  right_gap : ∀h, (g.rankRight j h).2.ell=(h.val:ℚ)
  right_c : ∀h, c=RankGap.cloneAt (g.rankRight j h).2.a (g.rankRight j h).2.tau W s.val
  right_b : ∀h, b=RankGap.cloneAt (g.rankRight j h).2.b (g.rankRight j h).2.tau W t.val
  left_weight : ∀h, totalWeight (B:=B) (g.rankLeft j h).2.ys (leftPoint (g.rankLeft j h).2)=(d.leftWeight j h.val:ℤ)
  right_weight : ∀h, totalWeight (B:=B) (g.rankRight j h).2.ys (rightPoint (g.rankRight j h).2)= -(d.rightWeight j h.val:ℤ)

/-- Exact selected-macro field, summed over every actual placed copy. The
rank terms are the computed greedy prefix and negative suffix. -/
theorem selected_group_field {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (W : ℕ) (s t : Fin W) (c b : ℚ)
    (h : Selected d g j W s t c b) (hs : s.val≤gaps) (ht : t.val≤gaps)
    (hcMem : original c∈p.base) (hbMem : original b∈p.base) :
    groupField d g p j (original c) (original b)=
      (ordinaryLeft d j:ℤ)*OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2 c b+
      (ordinaryRight d j:ℤ)*OrdinaryCoreField.coreCoefficient (g.ordinaryRight j).2 b c+
      RankCorrection.cumulative (d.leftSlope j) (d.leftWeight j) s.val-
      RankCorrection.cumulative (d.rightSlope j) (d.rightWeight j) gaps+
      RankCorrection.cumulative (d.rightSlope j) (d.rightWeight j) t.val := by
  have hOL (i : Fin (ordinaryLeft d j)) : coreCoefficient (B:=B) g.ys
      (p.points (.inl ⟨j,i⟩)) (original c) (original b)=
      OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2 c b := by
    rw [←g.ys_ol j]
    exact PlacedOrdinaryField.placed_incident_coefficient (g.ordinaryLeft j).2 p.M p.base p.prototypes _
      p.frame_mem (by intro k; rw [g.ys_ol]; exact p.original_mem k)
      (p.prototype_mem (.inl ⟨j,i⟩)) p.proto_below (p.placed (.inl ⟨j,i⟩))
      c b h.unit_c h.unit_b h.ordinary_left_clone h.ordinary_left_sep hcMem hbMem
  have hOR (i : Fin (ordinaryRight d j)) : coreCoefficient (B:=B) g.ys
      (p.points (.inr (.inl ⟨j,i⟩))) (original c) (original b)=
      OrdinaryCoreField.coreCoefficient (g.ordinaryRight j).2 b c := by
    rw [coefficient_reverse,←g.ys_or j]
    exact PlacedOrdinaryField.placed_incident_coefficient (g.ordinaryRight j).2 p.M p.base p.prototypes _
      p.frame_mem (by intro k; rw [g.ys_or]; exact p.original_mem k)
      (p.prototype_mem (.inr (.inl ⟨j,i⟩))) p.proto_below (p.placed (.inr (.inl ⟨j,i⟩)))
      b c h.unit_b h.unit_c h.ordinary_right_clone h.ordinary_right_sep hbMem hcMem
  have hRL (a : Fin gaps) (i : Fin (rankLeft d j a.val)) : coreCoefficient (B:=B) g.ys
      (p.points (.inr (.inr (.inl ⟨j,a,i⟩)))) (original c) (original b)=
      (d.leftWeight j a.val:ℤ)*(if a.val<s.val then 1 else 0) := by
    rw [←g.ys_rl j a,h.left_c a,h.left_b a]
    rw [placed_left_selected_fixed_weight (g.rankLeft j a).2 W a.val (h.left_width a) (h.left_gap a) s t
      p.M p.base p.prototypes _ p.frame_mem
      (by intro k; rw [g.ys_rl]; exact p.original_mem k)
      (p.prototype_mem (.inr (.inr (.inl ⟨j,a,i⟩)))) p.proto_below (p.placed (.inr (.inr (.inl ⟨j,a,i⟩))))
      (h.left_c a ▸ hcMem) (h.left_b a ▸ hbMem),h.left_weight a]
  have hRR (a : Fin gaps) (i : Fin (rankRight d j a.val)) : coreCoefficient (B:=B) g.ys
      (p.points (.inr (.inr (.inr ⟨j,a,i⟩)))) (original c) (original b)=
      (-(d.rightWeight j a.val:ℤ))*(if t.val≤a.val then 1 else 0) := by
    rw [←g.ys_rr j a,h.right_c a,h.right_b a]
    rw [placed_right_selected_fixed_weight (g.rankRight j a).2 W a.val (h.right_width a) (h.right_gap a) s t
      p.M p.base p.prototypes _ p.frame_mem
      (by intro k; rw [g.ys_rr]; exact p.original_mem k)
      (p.prototype_mem (.inr (.inr (.inr ⟨j,a,i⟩)))) p.proto_below (p.placed (.inr (.inr (.inr ⟨j,a,i⟩))))
      (h.right_c a ▸ hcMem) (h.right_b a ▸ hbMem),h.right_weight a]
  unfold groupField
  simp only [hOL,hOR,hRL,hRR,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp_rw [←mul_assoc]
  rw [show rankLeft d j=(RankCorrection.multiplicity (d.leftSlope j) (d.leftWeight j)) from rfl,
    show rankRight d j=(RankCorrection.multiplicity (d.rightSlope j) (d.rightWeight j)) from rfl,
    rank_prefix _ _ _ _ hs,rank_suffix _ _ _ _ ht]
  ring


/-- Only coordinate curvature inequalities: an unrelated macro cannot
contribute to this actual core edge. -/
structure Nonincident {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (j : Fin S) (c b : ℚ) : Prop where
  ordinary_left : 1200*(g.ordinaryLeft j).2.mu< |c-(g.ordinaryLeft j).2.a| * |b-(g.ordinaryLeft j).2.a|
  ordinary_right : 1200*(g.ordinaryRight j).2.mu< |c-(g.ordinaryRight j).2.a| * |b-(g.ordinaryRight j).2.a|
  rank_left : ∀h, 200*(g.rankLeft j h).2.mu*((g.rankLeft j h).2.b-(g.rankLeft j h).2.a)<
    |c-(g.rankLeft j h).2.a| * |b-(g.rankLeft j h).2.a|
  rank_right : ∀h, 200*(g.rankRight j h).2.mu*((g.rankRight j h).2.b-(g.rankRight j h).2.a)<
    |c-(g.rankRight j h).2.b| * |b-(g.rankRight j h).2.b|

/-- Every placed program point is accounted for. Other macros vanish by
actual geometric exclusion, while the selected macro has the exact greedy
prefix/suffix formula. -/
theorem selected_field {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (W : ℕ) (s t : Fin W) (c b : ℚ)
    (h : Selected d g j W s t c b) (hs : s.val≤gaps) (ht : t.val≤gaps)
    (hcMem : original c∈p.base) (hbMem : original b∈p.base)
    (hother : ∀k, k≠j → Nonincident g k c b) :
    field (B:=B) d g.ys p.points (original c) (original b)=
      (ordinaryLeft d j:ℤ)*OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2 c b+
      (ordinaryRight d j:ℤ)*OrdinaryCoreField.coreCoefficient (g.ordinaryRight j).2 b c+
      RankCorrection.cumulative (d.leftSlope j) (d.leftWeight j) s.val-
      RankCorrection.cumulative (d.rightSlope j) (d.rightWeight j) gaps+
      RankCorrection.cumulative (d.rightSlope j) (d.rightWeight j) t.val := by
  rw [field_eq_sum_groupField,Finset.sum_eq_single j]
  · exact selected_group_field d g p j W s t c b h hs ht hcMem hbMem
  · intro k _ hkj
    exact group_nonincident_zero d g p k c b h.unit_c h.unit_b hcMem hbMem
      (hother k hkj).ordinary_left (hother k hkj).ordinary_right
      (hother k hkj).rank_left (hother k hkj).rank_right
  · simp

end Q4.Candidate.ProgramCatalog
#print axioms Q4.Candidate.ProgramCatalog.left_nonincident_zero
#print axioms Q4.Candidate.ProgramCatalog.right_nonincident_zero
#print axioms Q4.Candidate.ProgramCatalog.field_eq_groups
#print axioms Q4.Candidate.ProgramCatalog.group_nonincident_zero

#print axioms Q4.Candidate.ProgramCatalog.selected_group_field

#print axioms Q4.Candidate.ProgramCatalog.selected_field
