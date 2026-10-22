import Q4.Candidate.CatalogDominance

/-! Actual same-side and dummy-incident program support. The support set
contains one or two genuine parent macro labels, with both endpoint orders
handled explicitly by the incident geometry. -/
namespace Q4.Candidate.SideCatalog
open Q4.Candidate.ConvexSeparation Q4.Candidate.ProgramCount
open Q4.Candidate.ProgramCatalog Q4.Candidate.CatalogSupport
open scoped BigOperators

noncomputable def ordinaryGeo {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (late : Bool) (j : Fin S) : Σcut, OrdinaryResponse.Geometry B O cut :=
  if late then g.ordinaryRight j else g.ordinaryLeft j

def ordinaryCount {S : ℕ} (d : Recipe S) (late : Bool) (j : Fin S) : ℕ :=
  if late then ordinaryRight d j else ordinaryLeft d j
noncomputable def ordinaryField {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (j : Fin S) (c b : ℚ) : ℤ :=
  if late then ordinaryR d g p j c b else ordinaryL d g p j c b
noncomputable def rankField {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (j : Fin S) (c b : ℚ) : ℤ :=
  if late then rankR d g p j c b else rankL d g p j c b

def sign (late : Bool) : ℤ := if late then -1 else 1

def Incident {B O : ℕ} (a : Σcut, OrdinaryResponse.Geometry B O cut) (c b : ℚ) : Prop :=
  (3*((B:ℚ)+1)*|c-a.2.a|≤a.2.mu ∧ 5*a.2.mu≤|b-a.2.a|) ∨
  (3*((B:ℚ)+1)*|b-a.2.a|≤a.2.mu ∧ 5*a.2.mu≤|c-a.2.a|)

def ordinaryMargin {S gaps B O : ℕ} (g : Geometries S gaps B O) (late : Bool) (j : Fin S)
    (c b : ℚ) : Prop :=
  1200*(ordinaryGeo g late j).2.mu< |c-(ordinaryGeo g late j).2.a| * |b-(ordinaryGeo g late j).2.a|
def rankMargin {S gaps B O : ℕ} (g : Geometries S gaps B O) (late : Bool) (j : Fin S)
    (c b : ℚ) : Prop :=
  if late then ∀h, 200*(g.rankRight j h).2.mu*((g.rankRight j h).2.b-(g.rankRight j h).2.a)<
    |c-(g.rankRight j h).2.b| * |b-(g.rankRight j h).2.b|
  else ∀h, 200*(g.rankLeft j h).2.mu*((g.rankLeft j h).2.b-(g.rankLeft j h).2.a)<
    |c-(g.rankLeft j h).2.a| * |b-(g.rankLeft j h).2.a|

structure Support {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (late : Bool) (parents : Finset (Fin S)) (c b : ℚ) : Prop where
  unit_c : |c|≤1
  unit_b : |b|≤1
  incident : ∀j∈parents, Incident (ordinaryGeo g late j) c b
  ordinary_outside : ∀j, j∉parents → ordinaryMargin g late j c b
  rank_outside : ∀j, j∉parents → rankMargin g late j c b
  opposite_ordinary : ∀j, ordinaryMargin g (!late) j c b
  opposite_rank : ∀j, rankMargin g (!late) j c b

theorem ordinary_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base) (hcurve : ordinaryMargin g late j c b) :
    ordinaryField d g p late j c b=0 := by
  cases late
  · exact ordinary_left_zero d g p j c b hc hb hcM hbM hcurve
  · exact ordinary_right_zero d g p j c b hc hb hcM hbM hcurve

theorem rank_zero {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base) (hcurve : rankMargin g late j c b) :
    rankField d g p late j c b=0 := by
  cases late
  · exact rank_left_zero d g p j c b hc hb hcM hbM hcurve
  · exact rank_right_zero d g p j c b hc hb hcM hbM hcurve

theorem ordinary_symm {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (j : Fin S) (c b : ℚ) :
    ordinaryField d g p late j c b=ordinaryField d g p late j b c := by
  cases late <;> unfold ordinaryField <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · unfold ordinaryL
    apply Finset.sum_congr rfl
    intro i _
    exact coefficient_reverse _ _ _ _
  · unfold ordinaryR
    apply Finset.sum_congr rfl
    intro i _
    exact coefficient_reverse _ _ _ _

theorem ordinary_incident {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base) (hi : Incident (ordinaryGeo g late j) c b) :
    ordinaryField d g p late j c b=(ordinaryCount d late j:ℤ)*
      OrdinaryCoreField.coreCoefficient (ordinaryGeo g late j).2 c b := by
  cases late
  · rcases hi with ⟨hclone,hsep⟩|⟨hclone,hsep⟩
    · exact ordinary_left_incident d g p j c b hc hb hcM hbM hclone hsep
    · rw [ordinary_symm]
      change ordinaryL d g p j b c=_
      rw [ordinary_left_incident d g p j b c hb hc hbM hcM hclone hsep,
        OrdinaryCoreField.coefficient_symm _ b c]
      rfl
  · rcases hi with ⟨hclone,hsep⟩|⟨hclone,hsep⟩
    · rw [ordinary_symm]
      exact ordinary_right_incident d g p j b c hb hc hbM hcM hclone hsep
    · change ordinaryR d g p j c b=_
      rw [ordinary_right_incident d g p j c b hc hb hcM hbM hclone hsep,
        OrdinaryCoreField.coefficient_symm _ b c]
      rfl

/-- The full catalog reduces to the actual one/two same-side parent sums.
All opposite-side and unrelated macros were excluded geometrically. -/
theorem field_support {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (parents : Finset (Fin S)) (c b : ℚ)
    (h : Support g late parents c b) (hcM : original c∈p.base) (hbM : original b∈p.base) :
    ProgramField.field (B:=B) d g.ys p.points (original c) (original b)=
      (∑j∈parents,ordinaryField d g p late j c b)+(∑j∈parents,rankField d g p late j c b) := by
  have hO : (∑j,ordinaryField d g p (!late) j c b)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact ordinary_zero d g p (!late) j c b h.unit_c h.unit_b hcM hbM (h.opposite_ordinary j)
  have hR : (∑j,rankField d g p (!late) j c b)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact rank_zero d g p (!late) j c b h.unit_c h.unit_b hcM hbM (h.opposite_rank j)
  have hOS : (∑j,ordinaryField d g p late j c b)=∑j∈parents,ordinaryField d g p late j c b := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact ordinary_zero d g p late j c b h.unit_c h.unit_b hcM hbM (h.ordinary_outside j hj)
  have hRS : (∑j,rankField d g p late j c b)=∑j∈parents,rankField d g p late j c b := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact rank_zero d g p late j c b h.unit_c h.unit_b hcM hbM (h.rank_outside j hj)
  rw [field_split]
  cases late <;> simp only [Bool.not_false,Bool.not_true,ordinaryField,rankField,
    Bool.false_eq_true,ite_false,ite_true] at hO hR hOS hRS ⊢ <;>
    rw [hO,hR] <;> simp only [zero_add,add_zero] <;> rw [hOS,hRS]

end Q4.Candidate.SideCatalog
#print axioms Q4.Candidate.SideCatalog.ordinary_incident
#print axioms Q4.Candidate.SideCatalog.field_support
