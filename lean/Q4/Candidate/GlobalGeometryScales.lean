import Q4.Candidate.ParentBlockExclusion

/-! Explicit common positive rational scales for every macro in a finite set.
These formulas replace successive qualitative choices by one uniform choice;
bit-complexity and the final full family assembly remain separate. -/
namespace Q4.Candidate.GlobalGeometryScales
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.RankGap Q4.Candidate.RankNonselected
open Q4.Candidate.OrdinaryNonincident Q4.Candidate.RankNonincident

noncomputable def programScale (A : Finset ℚ) (W : ℕ) : ℚ :=
  (macroSpacing A)^2/(10000*((W:ℚ)+1))
noncomputable def cloneScale (A : Finset ℚ) (W B : ℕ) : ℚ :=
  programScale A W*(macroSpacing A)^2/(1000*((B:ℚ)+1))

theorem common_scale_bounds (A : Finset ℚ) (W B : ℕ) :
    0 < programScale A W ∧ programScale A W ≤ 1/10000 ∧
    100*(W:ℚ)*programScale A W ≤ 1 ∧
    0 < cloneScale A W B ∧ cloneScale A W B ≤ macroSpacing A/1000 ∧
    10000*programScale A W ≤ (macroSpacing A)^2 ∧
    1000*cloneScale A W B ≤ programScale A W*(macroSpacing A)^2 ∧
    3*((B:ℚ)+1)*(cloneScale A W B/2) ≤ programScale A W := by
  let eta := macroSpacing A
  let mu := programScale A W
  let tau := cloneScale A W B
  have he0 : 0 < eta := macroSpacing_positive A
  have he1 : eta ≤ 1 := macroSpacing_le_one A
  have he2 : eta^2 ≤ eta := by nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1)]
  have he21 : eta^2 ≤ 1 := he2.trans he1
  have hm0 : 0 < mu := by dsimp [mu,programScale]; positivity
  have ht0 : 0 < tau := by dsimp [tau,cloneScale]; exact div_pos (mul_pos hm0 (sq_pos_of_pos he0)) (by positivity)
  have hmEq : 10000*((W:ℚ)+1)*mu=eta^2 := by
    dsimp [mu,programScale,eta]
    field_simp
  have htEq : 1000*((B:ℚ)+1)*tau=mu*eta^2 := by
    dsimp [tau,cloneScale,mu,eta]
    field_simp
  have hW0 : (0:ℚ) ≤ W := Nat.cast_nonneg _
  have hB0 : (0:ℚ) ≤ B := Nat.cast_nonneg _
  have hmSmall : 10000*mu ≤ eta^2 := by nlinarith [mul_nonneg hW0 hm0.le]
  have hm1 : mu ≤ 1 := by nlinarith
  have htSmall : 1000*tau ≤ mu*eta^2 := by nlinarith [mul_nonneg hB0 ht0.le]
  have hmult : mu*eta^2 ≤ eta := by nlinarith [mul_le_mul_of_nonneg_right hm1 (sq_nonneg eta)]
  change 0<mu ∧ mu≤1/10000 ∧ 100*(W:ℚ)*mu≤1 ∧ 0<tau ∧ tau≤eta/1000 ∧
    10000*mu≤eta^2 ∧ 1000*tau≤mu*eta^2 ∧ 3*((B:ℚ)+1)*(tau/2)≤mu
  refine ⟨hm0,by nlinarith,by nlinarith,ht0,by nlinarith,hmSmall,htSmall,?_⟩
  nlinarith [mul_le_mul_of_nonneg_left he21 hm0.le]

/-- For every ordered pair of distinct macros, the common scales meet the
selected-rank inequalities and the ordinary parent-clone width inequality. -/
theorem pair_scale_conditions (A : Finset ℚ) (W B : ℕ) (a b : ℚ)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
    100*cloneScale A W B ≤ programScale A W*(b-a) ∧
    4800*programScale A W < (macroSpacing A)^2 := by
  have hh := common_scale_bounds A W B
  have he0 := macroSpacing_positive A
  have he1 := macroSpacing_le_one A
  have he2 : (macroSpacing A)^2 ≤ macroSpacing A := by
    nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1)]
  have hgap := macroSpacing_le A a b ha hb (ne_of_gt hab)
  rw [abs_of_pos (sub_pos.mpr hab)] at hgap
  have hp := mul_le_mul_of_nonneg_left (he2.trans hgap) hh.1.le
  exact ⟨by nlinarith [hh.2.2.2.2.2.2.1],by nlinarith [hh.2.2.2.2.2.1]⟩

/-- The manuscript's macro box [-3/4,3/4] leaves a uniform strict outer cap
margin for every actual clone under the chosen width. -/
theorem global_clone_box (A : Finset ℚ) (W B : ℕ) (a : ℚ)
    (ha : |a| ≤ 3/4) :
    -1 < a-cloneScale A W B/2 ∧ a+cloneScale A W B/2 < 1 := by
  have hh := common_scale_bounds A W B
  have ht := hh.2.2.2.2.1
  have he1 := macroSpacing_le_one A
  constructor <;> linarith [(abs_le.mp ha).1,(abs_le.mp ha).2]

/-- Every actual nonparent original (cloned or un-cloned) retains at least
half its macro spacing and its exact side of the parent macro. -/
theorem nonparent_distance_order (A : Finset ℚ) (W B : ℕ) (a c z : ℚ)
    (ha : a ∈ A) (hc : c ∈ A) (hne : c ≠ a)
    (hz : |z-c| ≤ cloneScale A W B/2) :
    macroSpacing A/2 ≤ |z-a| ∧ (z<a ↔ c<a) ∧ (a<z ↔ a<c) := by
  have hh := common_scale_bounds A W B
  have he0 := macroSpacing_positive A
  have hgap := macroSpacing_le A a c ha hc hne
  have hz' : |z-c| ≤ macroSpacing A/2 := by linarith [hh.2.2.2.2.1]
  have hdist := clone_macro_distance a z c (macroSpacing A) hgap hz'
  refine ⟨hdist,?_⟩
  rcases lt_or_gt_of_ne hne with hca|hac
  · rw [abs_of_neg (sub_neg.mpr hca)] at hgap
    have hza : z<a := by linarith [(abs_le.mp hz').2]
    exact ⟨by constructor <;> intro _ <;> assumption,by constructor <;> intro h <;> linarith⟩
  · rw [abs_of_pos (sub_pos.mpr hac)] at hgap
    have haz : a<z := by linarith [(abs_le.mp hz').1]
    exact ⟨by constructor <;> intro h <;> linarith,by constructor <;> intro _ <;> assumption⟩

/-- The same displacement works for all ordinary and rank nonparent rays. -/
theorem nonparent_ray_margins (A : Finset ℚ) (W B : ℕ) (a b c z : ℚ)
    (ha : a ∈ A) (hc : c ∈ A) (hne : c ≠ a)
    (haUnit : |a| ≤ 1) (hbUnit : |b| ≤ 1)
    (hz : |z-c| ≤ cloneScale A W B/2) :
    5*programScale A W ≤ |z-a| ∧ 2*programScale A W*(b-a) ≤ |z-a| := by
  have hh := common_scale_bounds A W B
  have he0 := macroSpacing_positive A
  have he1 := macroSpacing_le_one A
  have he2 : (macroSpacing A)^2 ≤ macroSpacing A := by
    nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1)]
  have hmu := hh.2.2.2.2.2.1
  have hdist := (nonparent_distance_order A W B a c z ha hc hne hz).1
  have hd : b-a ≤ 2 := by linarith [(abs_le.mp haUnit).1,(abs_le.mp hbUnit).2]
  have hp := mul_le_mul_of_nonneg_left hd hh.1.le
  constructor <;> nlinarith

/-- The same clone diameter pays for every nonselected partner's actual gap,
without assuming its determinant sign or its crossing status. -/
theorem nonselected_partner_gap (A : Finset ℚ) (W B : ℕ) (a b partner c z : ℚ)
    (ha : a ∈ A) (hb : b ∈ A) (hpMem : partner ∈ A) (hc : c ∈ A) (hab : a < b) (hne : c ≠ partner)
    (hz : |z-c| ≤ cloneScale A W B/2) :
    20*cloneScale A W B ≤ programScale A W*(b-a)*|partner-z| := by
  have hh := common_scale_bounds A W B
  have he0 := macroSpacing_positive A
  have hd := macroSpacing_le A a b ha hb (ne_of_gt hab)
  rw [abs_of_pos (sub_pos.mpr hab)] at hd
  have hdist := (nonparent_distance_order A W B partner c z hpMem hc hne hz).1
  rw [abs_sub_comm z partner] at hdist
  have hp := mul_le_mul hd hdist (by linarith : (0:ℚ) ≤ macroSpacing A/2) (by linarith : 0 ≤ b-a)
  have hp' := mul_le_mul_of_nonneg_left hp hh.1.le
  nlinarith [hh.2.2.2.2.2.2.1]

/-- Actual quadratic curvature margins hold simultaneously for every pair of
nonparent endpoints, with no separation required between those two endpoints. -/
theorem nonincident_margins (A : Finset ℚ) (W B : ℕ) (parent c d z v span : ℚ)
    (ha : parent ∈ A) (hc : c ∈ A) (hd : d ∈ A) (hcne : c ≠ parent) (hdne : d ≠ parent)
    (hz : |z-c| ≤ cloneScale A W B/2) (hv : |v-d| ≤ cloneScale A W B/2)
    (hspan : span ≤ 2) :
    1200*programScale A W < |z-parent| * |v-parent| ∧
    200*programScale A W*span < |z-parent| * |v-parent| := by
  have hh := common_scale_bounds A W B
  have he0 := macroSpacing_positive A
  have hm := hh.2.2.2.2.2.1
  have ht := hh.2.2.2.2.1
  have hz' : |z-c| ≤ macroSpacing A/2 := by linarith
  have hv' : |v-d| ≤ macroSpacing A/2 := by linarith
  have hC := macroSpacing_le A parent c ha hc hcne
  have hD := macroSpacing_le A parent d ha hd hdne
  constructor
  · exact curvature_from_macro_boxes parent z v c d (macroSpacing A) (programScale A W)
      he0 (by nlinarith [hh.1]) hC hD hz' hv'
  · have he := rank_curvature_from_macro_boxes parent z v c d (macroSpacing A) (programScale A W*span)
      he0 (by nlinarith [mul_le_mul_of_nonneg_left hspan hh.1.le,hh.1]) hC hD hz' hv'
    nlinarith

/-- Every actual parent clone meets the ordinary ray margin in every row,
and every clone fits the common half-width used in all macro estimates. -/
theorem actual_clone_conditions (A : Finset ℚ) (W B : ℕ) (a s : ℚ)
    (hW : 2 ≤ W) (hs : 0 ≤ s) (hs1 : s ≤ (W:ℚ)-1) :
    |cloneAt a (cloneScale A W B) W s-a| ≤ cloneScale A W B/2 ∧
    3*((B:ℚ)+1)*|cloneAt a (cloneScale A W B) W s-a| ≤ programScale A W := by
  have hh := common_scale_bounds A W B
  have hnear := clone_macro_near a (cloneScale A W B) W s hh.2.2.2.1.le
    (by exact_mod_cast hW) hs hs1
  refine ⟨hnear,?_⟩
  have hp := mul_le_mul_of_nonneg_left hnear (by positivity : (0:ℚ) ≤ 3*((B:ℚ)+1))
  exact hp.trans hh.2.2.2.2.2.2.2

/-- The actual ordinary prototype satisfies the strict cap and height
hypotheses required by the common general-position construction. -/
theorem ordinary_strict_valid (A : Finset ℚ) (W B : ℕ) (a : ℚ) (ha : |a| ≤ 3/4) :
    phi (ordinary a (programScale A W)) < 0 ∧ |(ordinary a (programScale A W)).2| < 2 := by
  have hh := common_scale_bounds A W B
  have hv := ordinary_valid a (programScale A W) (by linarith [(abs_le.mp ha).1])
    (by linarith [(abs_le.mp ha).2]) hh.1 (by linarith [hh.2.1])
  refine ⟨hv.1,?_⟩
  have he : (ordinary a (programScale A W)).2 = a*(1+programScale A W) := by
    unfold ordinary mix original frame
    ring
  rw [he,abs_mul,abs_of_pos (by linarith [hh.1] : 0<1+programScale A W)]
  have hp := mul_le_mul_of_nonneg_right ha (by linarith [hh.1] : 0≤1+programScale A W)
  nlinarith [hh.2.1]

/-- Both actual rank prototypes have strict cap and strict height margins
under the same scales, ready for the common batch insertion hypothesis. -/
theorem rank_strict_valid (A : Finset ℚ) (W B : ℕ) (a b ell : ℚ)
    (hW : 2 ≤ W) (ha : a ∈ A) (hb : b ∈ A) (hab : a < b)
    (haBox : |a| ≤ 3/4) (hbBox : |b| ≤ 3/4)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ (W:ℚ)-1) :
    (phi (leftRank a b (cloneScale A W B) W (programScale A W) ell) < 0 ∧
      |(leftRank a b (cloneScale A W B) W (programScale A W) ell).2| < 2) ∧
    (phi (rightRank a b (cloneScale A W B) W (programScale A W) ell) < 0 ∧
      |(rightRank a b (cloneScale A W B) W (programScale A W) ell).2| < 2) := by
  have hh := common_scale_bounds A W B
  have hpair := pair_scale_conditions A W B a b ha hb hab
  have hboxA := (global_clone_box A W B a haBox).1.le
  have hboxB := (global_clone_box A W B b hbBox).2.le
  have hl := leftRank_valid a b (cloneScale A W B) W (programScale A W) ell hab
    (by exact_mod_cast hW) hh.1 hh.2.2.1 hh.2.2.2.1 hpair.1 hboxA hboxB hell hell1
  have hr := rightRank_valid a b (cloneScale A W B) W (programScale A W) ell hab
    (by exact_mod_cast hW) hh.1 hh.2.2.1 hh.2.2.2.1 hpair.1 hboxA hboxB hell hell1
  have hd0 := mul_pos hh.1 (sub_pos.mpr hab)
  have hd1 : programScale A W*(b-a) ≤ b-a :=
    by nlinarith [mul_le_mul_of_nonneg_right (show programScale A W ≤ 1 by linarith [hh.2.1]) (sub_pos.mpr hab).le]
  refine ⟨⟨hl.1,?_⟩,⟨hr.1,?_⟩⟩
  · change |a+programScale A W*(b-a)| < 2
    apply abs_lt.mpr
    constructor <;> linarith [(abs_le.mp haBox).1,(abs_le.mp hbBox).2]
  · change |b-programScale A W*(b-a)| < 2
    apply abs_lt.mpr
    constructor <;> linarith [(abs_le.mp haBox).1,(abs_le.mp hbBox).2]

end Q4.Candidate.GlobalGeometryScales

#print axioms Q4.Candidate.GlobalGeometryScales.common_scale_bounds
#print axioms Q4.Candidate.GlobalGeometryScales.pair_scale_conditions
#print axioms Q4.Candidate.GlobalGeometryScales.nonparent_distance_order
#print axioms Q4.Candidate.GlobalGeometryScales.nonparent_ray_margins
#print axioms Q4.Candidate.GlobalGeometryScales.nonselected_partner_gap
#print axioms Q4.Candidate.GlobalGeometryScales.nonincident_margins
#print axioms Q4.Candidate.GlobalGeometryScales.actual_clone_conditions
#print axioms Q4.Candidate.GlobalGeometryScales.ordinary_strict_valid
#print axioms Q4.Candidate.GlobalGeometryScales.rank_strict_valid
