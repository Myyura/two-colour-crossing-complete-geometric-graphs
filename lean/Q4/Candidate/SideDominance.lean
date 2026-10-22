import Q4.Candidate.SideCatalog

/-! Actual same-side and dummy-incident domination. The bounded support is
geometric; every retained ordinary and rank term is its real frozen fan sum. -/
namespace Q4.Candidate.SideDominance
open Q4.Candidate.ConvexSeparation Q4.Candidate.ProgramCount
open Q4.Candidate.ProgramCatalog Q4.Candidate.CatalogSupport
open Q4.Candidate.ActualRecipe Q4.Candidate.SideCatalog
open scoped BigOperators

structure Regime {S gaps B O : ℕ} (g : Geometries S gaps B O) (late : Bool) (j : Fin S) : Prop where
  cut : (ordinaryGeo g late j).1≤O
  parent : ((ordinaryGeo g late j).2.parent.card:ℝ)/O≤1/514
  side : if late then 1-1/514≤((ordinaryGeo g late j).1:ℝ)/O
    else ((ordinaryGeo g late j).1:ℝ)/O≤1/514

def slope {S : ℕ} (d : Recipe S) (late : Bool) (j : Fin S) : ℕ :=
  if late then d.rightSlope j else d.leftSlope j
def weight {S : ℕ} (d : Recipe S) (late : Bool) (j : Fin S) : ℕ→ℕ :=
  if late then d.rightWeight j else d.leftWeight j

/-- Both endpoint orders and both sides use the actual two half-frame bounds. -/
theorem incident_weight {S gaps B O : ℕ} (g : Geometries S gaps B O)
    (late : Bool) (j : Fin S) (hO : 1000≤O) (hBO : O≤B) (h8 : 8∣B)
    (hr : Regime g late j) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hi : Incident (ordinaryGeo g late j) c b) :
    (B:ℚ)/4≤(sign late:ℚ)*(OrdinaryCoreField.coreCoefficient (ordinaryGeo g late j).2 c b:ℚ) := by
  have hearly (a : Σr, OrdinaryResponse.Geometry B O r) (hcut : a.1≤O)
      (hp : (a.2.parent.card:ℝ)/O≤1/514) (hs : (a.1:ℝ)/O≤1/514)
      (ha : Incident a c b) : (B:ℝ)/4≤(OrdinaryCoreField.coreCoefficient a.2 c b:ℝ) := by
    rcases ha with ⟨hclone,hsep⟩|⟨hclone,hsep⟩
    · exact (OrdinaryCoreField.early_incident_coefficient a.2 hO hBO hcut h8 hp hs c b hc hb hclone hsep).1
    · rw [OrdinaryCoreField.coefficient_symm]
      exact (OrdinaryCoreField.early_incident_coefficient a.2 hO hBO hcut h8 hp hs b c hb hc hclone hsep).1
  have hlate (a : Σr, OrdinaryResponse.Geometry B O r) (hcut : a.1≤O)
      (hp : (a.2.parent.card:ℝ)/O≤1/514) (hs : 1-1/514≤(a.1:ℝ)/O)
      (ha : Incident a c b) : (OrdinaryCoreField.coreCoefficient a.2 c b:ℝ)≤ -(B:ℝ)/4 := by
    rcases ha with ⟨hclone,hsep⟩|⟨hclone,hsep⟩
    · exact (OrdinaryCoreField.late_incident_coefficient a.2 hO hBO hcut h8 hp hs c b hc hb hclone hsep).2
    · rw [OrdinaryCoreField.coefficient_symm]
      exact (OrdinaryCoreField.late_incident_coefficient a.2 hO hBO hcut h8 hp hs b c hb hc hclone hsep).2
  cases late
  · have hh := hearly _ hr.cut hr.parent hr.side hi
    simp only [sign,Bool.false_eq_true,ite_false,Int.cast_one,one_mul]
    have hhR : (B:ℝ)≤4*(OrdinaryCoreField.coreCoefficient (ordinaryGeo g false j).2 c b:ℝ) := by linarith
    have hhQ : (B:ℚ)≤4*(OrdinaryCoreField.coreCoefficient (ordinaryGeo g false j).2 c b:ℚ) := by exact_mod_cast hhR
    linarith
  · have hh := hlate _ hr.cut hr.parent hr.side hi
    have hhq : (OrdinaryCoreField.coreCoefficient (ordinaryGeo g true j).2 c b:ℚ)≤ -(B:ℚ)/4 := by exact_mod_cast hh
    simp only [sign,ite_true,Int.cast_neg,Int.cast_one,neg_one_mul]
    linarith

/-- The actual greedy copies of one arbitrary rank family cost at most 4OW+4B. -/
theorem rank_family_bound {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (j : Fin S) (c b : ℚ) (W : ℕ)
    (hB : 0<B) (hg : gaps≤W) (hs : slope d late j≤O)
    (hw : ∀i<gaps, 0<weight d late j i ∧ weight d late j i≤B ∧ B≤4*weight d late j i) :
    |rankField d g p late j c b|≤4*(O:ℤ)*W+4*B := by
  have hgC := (RankCorrection.greedy_correction (slope d late j) B gaps (weight d late j) hB hw).2
  have hmul := Nat.mul_le_mul hs hg
  have hgC' : B*RankCorrection.copyCount (slope d late j) (weight d late j) gaps≤4*O*W+4*B := by nlinarith
  have hgCi : (B:ℤ)*RankCorrection.copyCount (slope d late j) (weight d late j) gaps≤4*(O:ℤ)*W+4*B := by exact_mod_cast hgC'
  cases late
  · exact (rank_left_bound d g p j c b).trans hgCi
  · exact (rank_right_bound d g p j c b).trans hgCi

/-- One or two parents pay the whole actual rank field; no prescribed rank
response is used for these nonselected chords. -/
theorem rank_support_bound {S gaps B O : ℕ} (d : Recipe S) (g : Geometries S gaps B O)
    (p : Placement d g) (late : Bool) (parents : Finset (Fin S)) (hc : parents.card≤2)
    (c b : ℚ) (W : ℕ) (hB : 0<B) (hg : gaps≤W)
    (hs : ∀j∈parents,slope d late j≤O)
    (hw : ∀j∈parents,∀i<gaps, 0<weight d late j i ∧ weight d late j i≤B ∧ B≤4*weight d late j i) :
    |∑j∈parents,rankField d g p late j c b|≤8*(O:ℤ)*W+8*B := by
  have hh := Finset.abs_sum_le_sum_abs (fun j => rankField d g p late j c b) parents
  have hsum : (∑j∈parents, |rankField d g p late j c b|)≤
      (parents.card:ℤ)*(4*(O:ℤ)*W+4*B) := by
    calc
      _ ≤ ∑_j∈parents,(4*(O:ℤ)*W+4*B) := Finset.sum_le_sum (fun j hj =>
        rank_family_bound d g p late j c b W hB hg (hs j hj) (hw j hj))
      _ = _ := by simp
  have hcard : (parents.card:ℤ)≤2 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right hcard (show (0:ℤ)≤4*(O:ℤ)*W+4*B by positivity)
  nlinarith

/-- The other half of a genuine ordinary fan also contributes at least A/8,
although its weight need not equal the reference half used by the recipe. -/
theorem ordinary_lower {S W D B : ℕ} (A T : ℤ) (hS : 0<S) (hW : 0<W)
    (pi : Equiv.Perm (Fin S)) (g : Geometries S (W-1) B (S*W+D+S*W))
    (hy : StrictMono g.ys) (hD : 2*S*W<D) (p : Placement (recipe A T hW pi g) g)
    (late : Bool) (j : Fin S) (c b : ℚ) (hc : |c|≤1) (hb : |b|≤1)
    (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hi : Incident (ordinaryGeo g late j) c b) (hr : Regime g late j)
    (hO : 1000≤S*W+D+S*W) (hBO : S*W+D+S*W≤B) (h8 : 8∣B)
    (hBsmall : B≤(S*W+D+S*W)^2) (hA : 8*((S*W+D+S*W:ℕ):ℤ)^2≤A) (hT : 0≤T)
    (hwR : ∀i<W-1,0<rankRightWeight g j i ∧ rankRightWeight g j i≤B)
    (hu : 0<(if late then ordinaryRightWeight hW pi g j else ordinaryLeftWeight hW pi g j))
    (huB : (if late then ordinaryRightWeight hW pi g j else ordinaryLeftWeight hW pi g j)≤B) :
    (A:ℚ)/8≤(sign late:ℚ)*(ordinaryField (recipe A T hW pi g) g p late j c b:ℚ) := by
  have hB : 0<B := by omega
  have hh := incident_weight g late j hO hBO h8 hr c b hc hb hi
  have hoff := CatalogDominance.offset_bound A T hS hW pi g hy hD j hB hBsmall hwR
  have hAq : 8*(((S*W+D+S*W:ℕ):ℚ)^2)≤(A:ℚ) := by exact_mod_cast hA
  have hTq : (0:ℚ)≤T := by exact_mod_cast hT
  have htargets := PaletteBounds.targets_positive A ((j:ℚ)*T)
    ((recipe A T hW pi g).offset j) ((S*W+D+S*W:ℕ):ℚ) (by exact_mod_cast (show 0<S*W+D+S*W by omega)) hAq (by positivity) hoff
  have hA0 : (0:ℚ)≤A := by nlinarith [sq_nonneg (((S*W+D+S*W:ℕ):ℚ))]
  have htR : (A:ℚ)/2≤(A:ℚ)+(j:ℚ)*T := by nlinarith [mul_nonneg (show (0:ℚ)≤j by positivity) hTq]
  rw [ordinary_incident _ g p late j c b hc hb hcM hbM hi]
  push_cast
  let other : ℚ := (sign late:ℚ)*(OrdinaryCoreField.coreCoefficient (ordinaryGeo g late j).2 c b:ℚ)
  have rearrange : (sign late:ℚ)*((ordinaryCount (recipe A T hW pi g) late j:ℚ)*
      OrdinaryCoreField.coreCoefficient (ordinaryGeo g late j).2 c b)=
      (ordinaryCount (recipe A T hW pi g) late j:ℚ)*other := by dsimp [other]; ring
  rw [rearrange]
  cases late <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hu huB
  · exact PaletteBounds.rounded_other_half _ _ other A B (by exact_mod_cast hB) hA0 htargets.2.2
      (by change (0:ℚ)<(ordinaryLeftWeight hW pi g j:ℚ); exact_mod_cast hu) (by change (ordinaryLeftWeight hW pi g j:ℚ)≤B; exact_mod_cast huB) hh
  · exact PaletteBounds.rounded_other_half _ _ other A B (by exact_mod_cast hB) hA0 htR
      (by change (0:ℚ)<(ordinaryRightWeight hW pi g j:ℚ); exact_mod_cast hu) (by change (ordinaryRightWeight hW pi g j:ℚ)≤B; exact_mod_cast huB) hh

/-- Every actual same-side or side-dummy field has its prescribed sign and
strictly dominates the entire core-neighbor budget. -/
theorem dominance {S W D B : ℕ} (A T : ℤ) (hS : 0<S) (hW : 0<W)
    (pi : Equiv.Perm (Fin S)) (g : Geometries S (W-1) B (S*W+D+S*W))
    (hy : StrictMono g.ys) (hD : 2*S*W<D) (p : Placement (recipe A T hW pi g) g)
    (late : Bool) (parents : Finset (Fin S)) (hne : parents.Nonempty) (hcard : parents.card≤2)
    (c b : ℚ) (h : Support g late parents c b) (hcM : original c∈p.base) (hbM : original b∈p.base)
    (hreg : ∀j∈parents,Regime g late j)
    (hO : 1000≤S*W+D+S*W) (hBO : S*W+D+S*W≤B) (h8 : 8∣B)
    (hscale : 514*W≤S*W+D+S*W) (hBscale : 1024*B≤(S*W+D+S*W)^2)
    (hA : 8*((S*W+D+S*W:ℕ):ℤ)^2≤A) (hT : 0≤T)
    (hwL : ∀j∈parents,∀i<W-1,0<rankLeftWeight g j i ∧ rankLeftWeight g j i≤B ∧ B≤4*rankLeftWeight g j i)
    (hwR : ∀j∈parents,∀i<W-1,0<rankRightWeight g j i ∧ rankRightWeight g j i≤B ∧ B≤4*rankRightWeight g j i)
    (hu : ∀j∈parents,0<(if late then ordinaryRightWeight hW pi g j else ordinaryLeftWeight hW pi g j))
    (huB : ∀j∈parents,(if late then ordinaryRightWeight hW pi g j else ordinaryLeftWeight hW pi g j)≤B) :
    (((S*W+D+S*W:ℕ):ℚ)^2)/2 < (sign late:ℚ)*
      (ProgramField.field (B:=B) (recipe A T hW pi g) g.ys p.points (original c) (original b):ℚ) := by
  let d := recipe A T hW pi g
  have hB : 0<B := by omega
  have hlo (j : Fin S) (hj : j∈parents) := ordinary_lower A T hS hW pi g hy hD p late j c b h.unit_c h.unit_b
    hcM hbM (h.incident j hj) (hreg j hj) hO hBO h8 (by omega) hA hT
    (fun i hi => ⟨(hwR j hj i hi).1,(hwR j hj i hi).2.1⟩) (hu j hj) (huB j hj)
  have hA0 : (0:ℚ)≤A := by exact_mod_cast (show (0:ℤ)≤A by nlinarith [sq_nonneg (((S*W+D+S*W:ℕ):ℤ))])
  obtain ⟨j,hj⟩ := hne
  have hsingle := Finset.single_le_sum (s:=parents)
    (f:=fun k => (sign late:ℚ)*(ordinaryField d g p late k c b:ℚ))
    (fun k hk => le_trans (by positivity : (0:ℚ)≤(A:ℚ)/8) (hlo k hk)) hj
  have hordinary : (A:ℚ)/8≤(sign late:ℚ)*(∑k∈parents,ordinaryField d g p late k c b:ℤ) := by
    push_cast
    rw [Finset.mul_sum]
    exact (hlo j hj).trans hsingle
  have hsl (j : Fin S) (hj : j∈parents) : slope d late j≤S*W+D+S*W := by
    have hp := palette_affine hS hW pi g.ys hy hD j
    cases late
    · exact hp.1
    · exact hp.2.1
  have hw (j : Fin S) (hj : j∈parents) : ∀i<W-1,0<weight d late j i ∧ weight d late j i≤B ∧ B≤4*weight d late j i := by
    cases late
    · exact hwL j hj
    · exact hwR j hj
  have hr := rank_support_bound d g p late parents hcard c b W hB (Nat.sub_le W 1) hsl hw
  have hrq : |((∑k∈parents,rankField d g p late k c b:ℤ):ℚ)|≤8*((S*W+D+S*W:ℕ):ℚ)*W+8*B := by exact_mod_cast hr
  have hrs : -(8*((S*W+D+S*W:ℕ):ℚ)*W+8*B)≤
      (sign late:ℚ)*((∑k∈parents,rankField d g p late k c b:ℤ):ℚ) := by
    have ha := abs_le.mp hrq
    cases late <;> simp only [sign,Bool.false_eq_true,ite_false,ite_true,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul] <;> linarith
  have hbudget := PaletteBounds.side_adverse_budget ((S*W+D+S*W:ℕ):ℚ) W B
    (by exact_mod_cast (show 0<S*W+D+S*W by omega)) (by positivity) (by exact_mod_cast hscale) (by positivity) (by exact_mod_cast hBscale)
  have hAq : 8*(((S*W+D+S*W:ℕ):ℚ)^2)≤(A:ℚ) := by exact_mod_cast hA
  rw [field_support d g p late parents c b h hcM hbM]
  push_cast
  push_cast at hordinary hrs hAq hbudget
  nlinarith only [hAq,hbudget,hordinary,hrs]

end Q4.Candidate.SideDominance
#print axioms Q4.Candidate.SideDominance.incident_weight
#print axioms Q4.Candidate.SideDominance.rank_support_bound
#print axioms Q4.Candidate.SideDominance.ordinary_lower
#print axioms Q4.Candidate.SideDominance.dominance
