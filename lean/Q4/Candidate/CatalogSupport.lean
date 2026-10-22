import Q4.Candidate.ActualRecipe

/-! Actual catalog support on an original-original core edge. Only program
families at its parent blocks can contribute; the entire remaining rank
response is bounded by the actual computed copy counts. -/
namespace Q4.Candidate.CatalogSupport
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.ProgramCount Q4.Candidate.ProgramCatalog
open Q4.Candidate.RankResponse
open scoped BigOperators

noncomputable def ordinaryL {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) : ℤ :=
  ∑i : Fin (ordinaryLeft d j), coreCoefficient (B:=B) g.ys (p.points (.inl ⟨j,i⟩)) (original c) (original b)
noncomputable def ordinaryR {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) : ℤ :=
  ∑i : Fin (ordinaryRight d j), coreCoefficient (B:=B) g.ys (p.points (.inr (.inl ⟨j,i⟩))) (original c) (original b)
noncomputable def rankL {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) : ℤ :=
  ∑h : Fin gaps, ∑i : Fin (rankLeft d j h.val),
    coreCoefficient (B:=B) g.ys (p.points (.inr (.inr (.inl ⟨j,h,i⟩)))) (original c) (original b)
noncomputable def rankR {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) : ℤ :=
  ∑h : Fin gaps, ∑i : Fin (rankRight d j h.val),
    coreCoefficient (B:=B) g.ys (p.points (.inr (.inr (.inr ⟨j,h,i⟩)))) (original c) (original b)

theorem field_split {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (c b : ℚ) :
    ProgramField.field (B:=B) d g.ys p.points (original c) (original b)=
      (∑j,ordinaryL d g p j c b)+(∑j,ordinaryR d g p j c b)+
      (∑j,rankL d g p j c b)+(∑j,rankR d g p j c b) := by
  rw [ProgramCatalog.field_eq_groups]
  simp only [ordinaryL,ordinaryR,rankL,rankR,Finset.sum_add_distrib]

theorem ordinary_left_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hcurve : 1200*(g.ordinaryLeft j).2.mu< |c-(g.ordinaryLeft j).2.a| * |b-(g.ordinaryLeft j).2.a|) :
    ordinaryL d g p j c b=0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [←g.ys_ol j]
  exact PlacedOrdinaryField.placed_nonincident_coefficient_zero (g.ordinaryLeft j).2
    p.M p.base p.prototypes _ p.frame_mem (p.prototype_mem (.inl ⟨j,i⟩)) p.proto_below
    (p.placed (.inl ⟨j,i⟩)) c b hc hb hcurve hcM hbM

theorem ordinary_right_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hcurve : 1200*(g.ordinaryRight j).2.mu< |c-(g.ordinaryRight j).2.a| * |b-(g.ordinaryRight j).2.a|) :
    ordinaryR d g p j c b=0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [←g.ys_or j]
  exact PlacedOrdinaryField.placed_nonincident_coefficient_zero (g.ordinaryRight j).2
    p.M p.base p.prototypes _ p.frame_mem (p.prototype_mem (.inr (.inl ⟨j,i⟩))) p.proto_below
    (p.placed (.inr (.inl ⟨j,i⟩))) c b hc hb hcurve hcM hbM

theorem rank_left_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hcurve : ∀h, 200*(g.rankLeft j h).2.mu*((g.rankLeft j h).2.b-(g.rankLeft j h).2.a)<
      |c-(g.rankLeft j h).2.a| * |b-(g.rankLeft j h).2.a|) :
    rankL d g p j c b=0 := by
  apply Finset.sum_eq_zero
  intro h _
  apply Finset.sum_eq_zero
  intro i _
  rw [←g.ys_rl j h]
  exact left_nonincident_zero (g.rankLeft j h).2 p.M p.base p.prototypes _
    p.frame_mem (p.prototype_mem (.inr (.inr (.inl ⟨j,h,i⟩)))) p.proto_below
    (p.placed (.inr (.inr (.inl ⟨j,h,i⟩)))) c b hc hb (hcurve h) hcM hbM

theorem rank_right_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hcurve : ∀h, 200*(g.rankRight j h).2.mu*((g.rankRight j h).2.b-(g.rankRight j h).2.a)<
      |c-(g.rankRight j h).2.b| * |b-(g.rankRight j h).2.b|) :
    rankR d g p j c b=0 := by
  apply Finset.sum_eq_zero
  intro h _
  apply Finset.sum_eq_zero
  intro i _
  rw [←g.ys_rr j h]
  exact right_nonincident_zero (g.rankRight j h).2 p.M p.base p.prototypes _
    p.frame_mem (p.prototype_mem (.inr (.inr (.inr ⟨j,h,i⟩)))) p.proto_below
    (p.placed (.inr (.inr (.inr ⟨j,h,i⟩)))) c b hc hb (hcurve h) hcM hbM

/-- Every row and copy is charged exactly once; no gap-independent +W loss. -/
theorem rank_left_bound {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) :
    |rankL d g p j c b|≤(B:ℤ)*RankCorrection.copyCount (d.leftSlope j) (d.leftWeight j) gaps := by
  unfold rankL
  calc
    _ ≤ ∑h : Fin gaps, |∑i : Fin (rankLeft d j h.val),
        coreCoefficient (B:=B) g.ys (p.points (.inr (.inr (.inl ⟨j,h,i⟩)))) (original c) (original b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑h : Fin gaps, ∑i : Fin (rankLeft d j h.val), (B:ℤ) := by
      apply Finset.sum_le_sum
      intro h _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact PlacedOrdinaryField.point_coefficient_bound g.ys _ _ _
    _ = _ := by
      rw [copyCount_eq_sum]
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_sum,rankLeft,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      change (Fintype.card (Fin (rankLeft d j h.val)):ℤ)*B= _
      rw [Fintype.card_fin]
      exact mul_comm _ _

theorem rank_right_bound {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) :
    |rankR d g p j c b|≤(B:ℤ)*RankCorrection.copyCount (d.rightSlope j) (d.rightWeight j) gaps := by
  unfold rankR
  calc
    _ ≤ ∑h : Fin gaps, |∑i : Fin (rankRight d j h.val),
        coreCoefficient (B:=B) g.ys (p.points (.inr (.inr (.inr ⟨j,h,i⟩)))) (original c) (original b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑h : Fin gaps, ∑i : Fin (rankRight d j h.val), (B:ℤ) := by
      apply Finset.sum_le_sum
      intro h _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact PlacedOrdinaryField.point_coefficient_bound g.ys _ _ _
    _ = _ := by
      rw [copyCount_eq_sum]
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_sum,rankRight,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      change (Fintype.card (Fin (rankRight d j h.val)):ℤ)*B= _
      rw [Fintype.card_fin]
      exact mul_comm _ _

/-- A cross-block edge only needs the left-rank family of its early parent
and right-rank family of its late parent. Their actual combined field has
the manuscript's 8OW+8B adversarial budget. -/
theorem cross_rank_budget {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j k : Fin S) (c b : ℚ) (W : ℕ) (hB : 0<B) (hg : gaps≤W)
    (hsL : d.leftSlope j≤O) (hsR : d.rightSlope k≤O)
    (hwL : ∀i<gaps, 0<d.leftWeight j i ∧ d.leftWeight j i≤B ∧ B≤4*d.leftWeight j i)
    (hwR : ∀i<gaps, 0<d.rightWeight k i ∧ d.rightWeight k i≤B ∧ B≤4*d.rightWeight k i) :
    |rankL d g p j c b+rankR d g p k c b|<8*(O:ℤ)*W+8*B := by
  have hL := rank_left_bound d g p j c b
  have hR := rank_right_bound d g p k c b
  have hC := PaletteBounds.rank_copy_budget (d.leftSlope j) (d.rightSlope k) B gaps O W
    (d.leftWeight j) (d.rightWeight k) hB hsL hsR hg hwL hwR
  have hCi : (B:ℤ)*(RankCorrection.copyCount (d.leftSlope j) (d.leftWeight j) gaps+
      RankCorrection.copyCount (d.rightSlope k) (d.rightWeight k) gaps)<8*(O:ℤ)*W+8*B := by exact_mod_cast hC
  have hsum := abs_add_le (rankL d g p j c b) (rankR d g p k c b)
  nlinarith


structure CrossSupport {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (j k : Fin S) (c b : ℚ) : Prop where
  unit_c : |c|≤1
  unit_b : |b|≤1
  left_clone : 3*((B:ℚ)+1)*|c-(g.ordinaryLeft j).2.a|≤(g.ordinaryLeft j).2.mu
  left_sep : 5*(g.ordinaryLeft j).2.mu≤|b-(g.ordinaryLeft j).2.a|
  right_clone : 3*((B:ℚ)+1)*|b-(g.ordinaryRight k).2.a|≤(g.ordinaryRight k).2.mu
  right_sep : 5*(g.ordinaryRight k).2.mu≤|c-(g.ordinaryRight k).2.a|
  other_ordinary_left : ∀l, l≠j → 1200*(g.ordinaryLeft l).2.mu<
    |c-(g.ordinaryLeft l).2.a| * |b-(g.ordinaryLeft l).2.a|
  other_ordinary_right : ∀l, l≠k → 1200*(g.ordinaryRight l).2.mu<
    |c-(g.ordinaryRight l).2.a| * |b-(g.ordinaryRight l).2.a|
  other_rank_left : ∀l, l≠j → ∀h, 200*(g.rankLeft l h).2.mu*((g.rankLeft l h).2.b-(g.rankLeft l h).2.a)<
    |c-(g.rankLeft l h).2.a| * |b-(g.rankLeft l h).2.a|
  other_rank_right : ∀l, l≠k → ∀h, 200*(g.rankRight l h).2.mu*((g.rankRight l h).2.b-(g.rankRight l h).2.a)<
    |c-(g.rankRight l h).2.b| * |b-(g.rankRight l h).2.b|

theorem ordinary_left_incident {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hclone : 3*((B:ℚ)+1)*|c-(g.ordinaryLeft j).2.a|≤(g.ordinaryLeft j).2.mu)
    (hsep : 5*(g.ordinaryLeft j).2.mu≤|b-(g.ordinaryLeft j).2.a|) :
    ordinaryL d g p j c b=(ordinaryLeft d j:ℤ)*OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2 c b := by
  have he (i : Fin (ordinaryLeft d j)) : coreCoefficient (B:=B) g.ys
      (p.points (.inl ⟨j,i⟩)) (original c) (original b)=
      OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2 c b := by
    rw [←g.ys_ol j]
    exact PlacedOrdinaryField.placed_incident_coefficient (g.ordinaryLeft j).2 p.M p.base p.prototypes _
      p.frame_mem (by intro y; rw [g.ys_ol]; exact p.original_mem y)
      (p.prototype_mem (.inl ⟨j,i⟩)) p.proto_below (p.placed (.inl ⟨j,i⟩)) c b hc hb hclone hsep hcM hbM
  simp only [ordinaryL,he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem ordinary_right_incident {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hclone : 3*((B:ℚ)+1)*|b-(g.ordinaryRight j).2.a|≤(g.ordinaryRight j).2.mu)
    (hsep : 5*(g.ordinaryRight j).2.mu≤|c-(g.ordinaryRight j).2.a|) :
    ordinaryR d g p j c b=(ordinaryRight d j:ℤ)*OrdinaryCoreField.coreCoefficient (g.ordinaryRight j).2 b c := by
  have he (i : Fin (ordinaryRight d j)) : coreCoefficient (B:=B) g.ys
      (p.points (.inr (.inl ⟨j,i⟩))) (original c) (original b)=
      OrdinaryCoreField.coreCoefficient (g.ordinaryRight j).2 b c := by
    rw [coefficient_reverse,←g.ys_or j]
    exact PlacedOrdinaryField.placed_incident_coefficient (g.ordinaryRight j).2 p.M p.base p.prototypes _
      p.frame_mem (by intro y; rw [g.ys_or]; exact p.original_mem y)
      (p.prototype_mem (.inr (.inl ⟨j,i⟩))) p.proto_below (p.placed (.inr (.inl ⟨j,i⟩))) b c hb hc hclone hsep hbM hcM
  simp only [ordinaryR,he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Exact complete catalog field of an early-j/late-k chord, for every
placement and every canonical response in the remaining two rank families. -/
theorem cross_field {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (j k : Fin S) (c b : ℚ) (h : CrossSupport g j k c b)
    (hcM : original c∈p.base) (hbM : original b∈p.base) :
    ProgramField.field (B:=B) d g.ys p.points (original c) (original b)=
      (ordinaryLeft d j:ℤ)*OrdinaryCoreField.coreCoefficient (g.ordinaryLeft j).2 c b+
      (ordinaryRight d k:ℤ)*OrdinaryCoreField.coreCoefficient (g.ordinaryRight k).2 b c+
      rankL d g p j c b+rankR d g p k c b := by
  have hOL : (∑l,ordinaryL d g p l c b)=ordinaryL d g p j c b := by
    apply Finset.sum_eq_single j
    · intro l _ hlj
      exact ordinary_left_zero d g p l c b h.unit_c h.unit_b hcM hbM (h.other_ordinary_left l hlj)
    · simp
  have hOR : (∑l,ordinaryR d g p l c b)=ordinaryR d g p k c b := by
    apply Finset.sum_eq_single k
    · intro l _ hlk
      exact ordinary_right_zero d g p l c b h.unit_c h.unit_b hcM hbM (h.other_ordinary_right l hlk)
    · simp
  have hRL : (∑l,rankL d g p l c b)=rankL d g p j c b := by
    apply Finset.sum_eq_single j
    · intro l _ hlj
      exact rank_left_zero d g p l c b h.unit_c h.unit_b hcM hbM (h.other_rank_left l hlj)
    · simp
  have hRR : (∑l,rankR d g p l c b)=rankR d g p k c b := by
    apply Finset.sum_eq_single k
    · intro l _ hlk
      exact rank_right_zero d g p l c b h.unit_c h.unit_b hcM hbM (h.other_rank_right l hlk)
    · simp
  rw [field_split,hOL,hOR,hRL,hRR,
    ordinary_left_incident d g p j c b h.unit_c h.unit_b hcM hbM h.left_clone h.left_sep,
    ordinary_right_incident d g p k c b h.unit_c h.unit_b hcM hbM h.right_clone h.right_sep]

end Q4.Candidate.CatalogSupport
#print axioms Q4.Candidate.CatalogSupport.ordinary_left_zero
#print axioms Q4.Candidate.CatalogSupport.rank_left_zero
#print axioms Q4.Candidate.CatalogSupport.rank_left_bound
#print axioms Q4.Candidate.CatalogSupport.rank_right_bound
#print axioms Q4.Candidate.CatalogSupport.cross_rank_budget

#print axioms Q4.Candidate.CatalogSupport.ordinary_left_incident
#print axioms Q4.Candidate.CatalogSupport.ordinary_right_incident
#print axioms Q4.Candidate.CatalogSupport.cross_field
