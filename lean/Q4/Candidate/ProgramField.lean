import Q4.Candidate.ProgramCount
import Q4.Candidate.PlacedOrdinaryField

/-! Actual canonical frozen-fan fields over the computed program-copy labels.
The finite summation identities retain every individual placed point. -/
namespace Q4.Candidate.ProgramField
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.ProgramCount Q4.Candidate.RankResponse
open Q4.Candidate.RankSoftRows Q4.Candidate.VirtualColumnField
open Q4.Candidate.OrientationPreservation Q4.Candidate.UniformInsertion
open scoped BigOperators

structure Prototypes (S gaps : ℕ) where
  ordinaryLeft : Fin S → Point
  ordinaryRight : Fin S → Point
  rankLeft : Fin S → Fin gaps → Point
  rankRight : Fin S → Fin gaps → Point

abbrev prototype {S gaps : ℕ} (d : Recipe S) (p : Prototypes S gaps) : Label d gaps → Point
  | .inl ⟨j,_⟩ => p.ordinaryLeft j
  | .inr (.inl ⟨j,_⟩) => p.ordinaryRight j
  | .inr (.inr (.inl ⟨j,g,_⟩)) => p.rankLeft j g
  | .inr (.inr (.inr ⟨j,g,_⟩)) => p.rankRight j g

noncomputable def field {S gaps B O : ℕ} (d : Recipe S) (ys : Fin O → ℚ)
    (points : Label d gaps → Point) (x y : Point) : ℤ :=
  ∑ l : Label d gaps, coreCoefficient (B:=B) ys (points l) x y

noncomputable def cost {S gaps B O : ℕ} (d : Recipe S) (ys : Fin O → ℚ)
    (points : Label d gaps → Point) (x y : Point) (b : Bool) : ℤ :=
  ∑ l : Label d gaps, coreCost (B:=B) ys (points l) x y b

theorem cost_difference {S gaps B O : ℕ} (d : Recipe S) (ys : Fin O → ℚ)
    (points : Label d gaps → Point) (x y : Point) :
    cost (B:=B) d ys points x y true-cost (B:=B) d ys points x y false=field (B:=B) d ys points x y := by
  unfold cost field
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  exact (coreCoefficient_cost_difference ys (points l) x y).symm

/-- Summation over the actual finite copy labels, with counts defined by
rational ceilings and the explicit integer greedy program. -/
theorem sum_prototype {S gaps : ℕ} (d : Recipe S) (p : Prototypes S gaps) (f : Point → ℤ) :
    (∑ l : Label d gaps, f (prototype d p l))=
      ∑ j : Fin S, ((ordinaryLeft d j:ℤ)*f (p.ordinaryLeft j)+
        (ordinaryRight d j:ℤ)*f (p.ordinaryRight j)+
        (∑ g : Fin gaps, (rankLeft d j g.val:ℤ)*f (p.rankLeft j g))+
        (∑ g : Fin gaps, (rankRight d j g.val:ℤ)*f (p.rankRight j g))) := by
  simp only [Label,Fintype.sum_sum_type,Fintype.sum_sigma,prototype,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_add_distrib]
  ring

/-- The preserved single-copy coefficients yield the full actual program
field by finite summation. The geometric preservation lemmas supply hcopy. -/
theorem field_from_copies {S gaps B O : ℕ} (d : Recipe S) (ys : Fin O → ℚ)
    (p : Prototypes S gaps) (points : Label d gaps → Point) (x y : Point)
    (hcopy : ∀l, coreCoefficient (B:=B) ys (points l) x y=
      coreCoefficient (B:=B) ys (prototype d p l) x y) :
    field (B:=B) d ys points x y=
      ∑ j : Fin S, ((ordinaryLeft d j:ℤ)*coreCoefficient (B:=B) ys (p.ordinaryLeft j) x y+
        (ordinaryRight d j:ℤ)*coreCoefficient (B:=B) ys (p.ordinaryRight j) x y+
        (∑ g : Fin gaps, (rankLeft d j g.val:ℤ)*coreCoefficient (B:=B) ys (p.rankLeft j g) x y)+
        (∑ g : Fin gaps, (rankRight d j g.val:ℤ)*coreCoefficient (B:=B) ys (p.rankRight j g) x y)) := by
  unfold field
  simp_rw [hcopy]
  exact sum_prototype d p (fun z => coreCoefficient (B:=B) ys z x y)

theorem response_eq_of_field {B O : ℕ} (ys : Fin O → ℚ) (p q : Point)
    (heq : ∀k : Fin B, pointField spin ys p k=pointField spin ys q k) :
    (∀k : Fin B, response ys p k=response ys q k) ∧
      totalWeight (B:=B) ys p=totalWeight (B:=B) ys q := by
  have hr (k : Fin B) : response ys p k=response ys q k := by
    unfold response
    rw [heq k]
  refine ⟨hr,?_⟩
  unfold totalWeight responseSpin
  simp_rw [hr]

/-- Each actual placed left-rank copy has exactly the same integer response
weight as its prototype, including the zero-field tie convention. -/
theorem placed_left_weight_eq {N O cut : ℕ} (d : LeftGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i)∈B) (hy : ∀j, original (d.ys j)∈B)
    (hr : leftPoint d∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (leftPoint d) p) :
    totalWeight (B:=N) d.ys p=totalWeight (B:=N) d.ys (leftPoint d) := by
  apply (response_eq_of_field d.ys p (leftPoint d) ?_).2
  intro k
  rw [placed_left_field_eq_virtual d M B R p hf hy hr hproto hp,
    left_field_eq_virtual]

theorem placed_right_weight_eq {N O cut : ℕ} (d : RightGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i)∈B) (hy : ∀j, original (d.ys j)∈B)
    (hr : rightPoint d∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (rightPoint d) p) :
    totalWeight (B:=N) d.ys p=totalWeight (B:=N) d.ys (rightPoint d) := by
  apply (response_eq_of_field d.ys p (rightPoint d) ?_).2
  intro k
  rw [placed_right_field_eq_virtual d M B R p hf hy hr hproto hp,
    right_field_eq_virtual]


/-- The selected-edge coefficient of a final left copy uses the fixed actual
prototype response weight, so the greedy count need not depend on placement. -/
theorem placed_left_selected_fixed_weight {N O cut : ℕ} (d : LeftGeometry N O cut)
    (W ell : ℕ) (hw : d.w=(W:ℚ)) (he : d.ell=(ell:ℚ)) (s t : Fin W)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i)∈B) (hy : ∀j, original (d.ys j)∈B)
    (hr : leftPoint d∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (leftPoint d) p)
    (hleft : original (RankGap.cloneAt d.a d.tau W s.val)∈B)
    (hright : original (RankGap.cloneAt d.b d.tau W t.val)∈B) :
    coreCoefficient (B:=N) d.ys p (original (RankGap.cloneAt d.a d.tau W s.val))
      (original (RankGap.cloneAt d.b d.tau W t.val))=
      totalWeight (B:=N) d.ys (leftPoint d)*(if ell<s.val then 1 else 0) := by
  have hW : 2≤W := by exact_mod_cast (hw ▸ d.width)
  have hell : ell+1<W := by
    have h := d.gap_hi
    rw [hw,he] at h
    have h' : (ell:ℚ)+2≤W := by linarith
    have : ell+2≤W := by exact_mod_cast h'
    omega
  have hpoint : leftPoint d=RankGap.leftRank d.a d.b d.tau W d.mu ell := by
    simp only [leftPoint,hw,he]
  rw [RankResponse.placed_left_selected_coefficient d.ys M B R d.a d.b d.tau d.mu W ell s t p
    d.ordered hW d.mu_pos (hw ▸ d.mu_small) d.tau_pos d.tau_small d.box_a d.box_b hell
    hf hleft hright (hpoint ▸ hr) hproto (hpoint ▸ hp),
    placed_left_weight_eq d M B R p hf hy hr hproto hp]

theorem placed_right_selected_fixed_weight {N O cut : ℕ} (d : RightGeometry N O cut)
    (W ell : ℕ) (hw : d.w=(W:ℚ)) (he : d.ell=(ell:ℚ)) (s t : Fin W)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i)∈B) (hy : ∀j, original (d.ys j)∈B)
    (hr : rightPoint d∈R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (rightPoint d) p)
    (hleft : original (RankGap.cloneAt d.a d.tau W s.val)∈B)
    (hright : original (RankGap.cloneAt d.b d.tau W t.val)∈B) :
    coreCoefficient (B:=N) d.ys p (original (RankGap.cloneAt d.a d.tau W s.val))
      (original (RankGap.cloneAt d.b d.tau W t.val))=
      totalWeight (B:=N) d.ys (rightPoint d)*(if t.val≤ell then 1 else 0) := by
  have hW : 2≤W := by exact_mod_cast (hw ▸ d.width)
  have hell : ell+1<W := by
    have h := d.gap_hi
    rw [hw,he] at h
    have h' : (ell:ℚ)+2≤W := by linarith
    have : ell+2≤W := by exact_mod_cast h'
    omega
  have hpoint : rightPoint d=RankGap.rightRank d.a d.b d.tau W d.mu ell := by
    simp only [rightPoint,hw,he]
  rw [RankResponse.placed_right_selected_coefficient d.ys M B R d.a d.b d.tau d.mu W ell s t p
    d.ordered hW d.mu_pos (hw ▸ d.mu_small) d.tau_pos d.tau_small d.box_a d.box_b hell
    hf hleft hright (hpoint ▸ hr) hproto (hpoint ▸ hp),
    placed_right_weight_eq d M B R p hf hy hr hproto hp]

/-- A strict rank prefix in the actual finite gap index equals the exact
integer greedy cumulative weight. -/
theorem rank_prefix (slope gaps r : ℕ) (weight : ℕ → ℕ) (hr : r≤gaps) :
    (∑ g : Fin gaps, (RankCorrection.multiplicity slope weight g.val:ℤ)*
      (weight g.val:ℤ)*(if g.val<r then 1 else 0))=
      (RankCorrection.cumulative slope weight r:ℤ) := by
  rw [RankCorrection.cumulative_eq_sum]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun g => (RankCorrection.multiplicity slope weight g:ℤ)*
    (weight g:ℤ)*(if g<r then 1 else 0))]
  calc
    (∑ g∈Finset.range gaps, (RankCorrection.multiplicity slope weight g:ℤ)*
      (weight g:ℤ)*(if g<r then 1 else 0))=
        ∑ g∈Finset.range r, (RankCorrection.multiplicity slope weight g:ℤ)*
          (weight g:ℤ)*(if g<r then 1 else 0) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hr)
      intro g hg hgr
      simp only [Finset.mem_range] at hgr
      simp [hgr]
    _ = ∑ g∈Finset.range r, (weight g:ℤ)*RankCorrection.multiplicity slope weight g := by
      apply Finset.sum_congr rfl
      intro g hg
      simp [Finset.mem_range.mp hg,mul_comm]

/-- Right-rank fans have negative response and cross at ranks t≤g. Thus their
actual suffix is minus the total greedy prefix plus the prefix at t. -/
theorem rank_suffix (slope gaps t : ℕ) (weight : ℕ → ℕ) (ht : t≤gaps) :
    (∑ g : Fin gaps, (RankCorrection.multiplicity slope weight g.val:ℤ)*
      (-(weight g.val:ℤ))*(if t≤g.val then 1 else 0))=
      -(RankCorrection.cumulative slope weight gaps:ℤ)+
        (RankCorrection.cumulative slope weight t:ℤ) := by
  have htotal := rank_prefix slope gaps gaps weight (le_refl gaps)
  have hpre := rank_prefix slope gaps t weight ht
  rw [←htotal,←hpre,←Finset.sum_neg_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  by_cases htg : t≤g.val
  · simp [htg,not_lt.mpr htg,g.isLt]
  · have hgt : g.val<t := by omega
    simp [htg,hgt,g.isLt]

end Q4.Candidate.ProgramField
#print axioms Q4.Candidate.ProgramField.cost_difference
#print axioms Q4.Candidate.ProgramField.sum_prototype
#print axioms Q4.Candidate.ProgramField.field_from_copies
#print axioms Q4.Candidate.ProgramField.placed_left_weight_eq
#print axioms Q4.Candidate.ProgramField.placed_right_weight_eq

#print axioms Q4.Candidate.ProgramField.placed_left_selected_fixed_weight
#print axioms Q4.Candidate.ProgramField.placed_right_selected_fixed_weight
#print axioms Q4.Candidate.ProgramField.rank_prefix
#print axioms Q4.Candidate.ProgramField.rank_suffix
