import Q4.Candidate.RankSoftRows
import Q4.Candidate.OrdinaryResponse

/-! Actual canonical rank responses and selected-core coefficients. Only the
pure finite middle-row counting lemma is shared with ordinary responses. -/
open scoped BigOperators
namespace Q4.Candidate.RankResponse
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.RankGap Q4.Candidate.RankGapPreservation
open Q4.Candidate.RankSoftRows Q4.Candidate.VirtualColumnField
open Q4.Candidate.VirtualColumnShape Q4.Candidate.VirtualColumnSoftRows
open Q4.Candidate.GridCounts Q4.Candidate.OrientationPreservation Q4.Candidate.UniformInsertion

noncomputable def response {B O : ℕ} (ys : Fin O → ℚ) (p : Point) (k : Fin B) : Bool :=
  decide (pointField (spin : Fin B × Fin O → ℤ) ys p k<0)
noncomputable def responseSpin {B O : ℕ} (ys : Fin O → ℚ) (p : Point) (k : Fin B) : ℤ :=
  if response ys p k then 1 else -1
noncomputable def totalWeight {B O : ℕ} (ys : Fin O → ℚ) (p : Point) : ℤ :=
  ∑ k : Fin B, responseSpin ys p k

theorem responseSpin_bounds {B O : ℕ} (ys : Fin O → ℚ) (p : Point) (k : Fin B) :
    -1≤(responseSpin ys p k:ℝ) ∧ (responseSpin ys p k:ℝ)≤1 := by
  unfold responseSpin
  split <;> norm_num

theorem response_minimizes {B O : ℕ} (ys : Fin O → ℚ) (p : Point) (k : Fin B) (c : Bool) :
    pointCost Q4.Candidate.CanonicalField.canonical ys p k (response ys p k) ≤
      pointCost Q4.Candidate.CanonicalField.canonical ys p k c := by
  have hh := pointField_cost_difference Q4.Candidate.CanonicalField.canonical ys p k
  rw [←canonical_spin_eq] at hh
  by_cases hneg : pointField (spin : Fin B × Fin O → ℤ) ys p k<0
  · have hc : response ys p k=true := by simp [response,hneg]
    rw [hc]
    cases c
    · omega
    · rfl
  · have hc : response ys p k=false := by simp [response,hneg]
    rw [hc]
    cases c
    · rfl
    · omega

/-- The actual middle-row response follows from exact virtual-field equality.
The final rank theorems instantiate that equality using actual crossing tables. -/
theorem early_middle_of_virtual {B O cut : ℕ} (ys : Fin O → ℚ) (p : Point)
    (heq : ∀k, pointField (spin : Fin B × Fin O → ℤ) ys p k=virtualField (spin : Fin B × Fin O → ℤ) cut k.val)
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (hearly : (cut:ℝ)/O≤1/514)
    (k : Fin B) (hk : 1/8≤u B k ∧ u B k≤7/8) : responseSpin ys p k=1 := by
  have hv0 : 0≤(cut:ℝ)/O := by positivity
  have hslo : 1/9≤coord B O cut k := by unfold coord; linarith [hk.2]
  have hshi : coord B O cut k≤8/9 := by unfold coord; linarith [hk.1]
  have hshape := Q4.Candidate.OrdinaryResponse.positive_shape _ hslo hshi
  have herr := (abs_le.mp (virtualField_shape_estimate B O cut (by omega) hcut k)).2
  change (virtualField (spin : Fin B × Fin O → ℤ) cut k.val:ℝ)/((B:ℝ)*O)+shape (coord B O cut k)≤6*rho B O at herr
  have hnorm : (virtualField (spin : Fin B × Fin O → ℤ) cut k.val:ℝ)/((B:ℝ)*O)<0 := by
    linarith [rho_small B O hO hBO]
  have hbp : 0<B := by omega
  have hop : 0<O := by omega
  have hneg : (pointField (spin : Fin B × Fin O → ℤ) ys p k:ℝ)<0 := by
    rw [heq k]
    have hh := (div_lt_iff₀ (by positivity : (0:ℝ)<(B:ℝ)*O)).mp hnorm
    simpa only [zero_mul] using hh
  have hn : pointField (spin : Fin B × Fin O → ℤ) ys p k<0 := by exact_mod_cast hneg
  simp [responseSpin,response,hn]

theorem late_middle_of_virtual {B O cut : ℕ} (ys : Fin O → ℚ) (p : Point)
    (heq : ∀k, pointField (spin : Fin B × Fin O → ℤ) ys p k=virtualField (spin : Fin B × Fin O → ℤ) cut k.val)
    (hO : 1000≤O) (hBO : O≤B) (hcut : cut≤O) (hlate : 1-1/514≤(cut:ℝ)/O)
    (k : Fin B) (hk : 1/8≤u B k ∧ u B k≤7/8) : responseSpin ys p k= -1 := by
  have ho : (0:ℝ)<O := by exact_mod_cast (show 0<O by omega)
  have hv1 : (cut:ℝ)/O≤1 := by rw [div_le_one ho]; exact_mod_cast hcut
  have hslo : -8/9≤coord B O cut k := by unfold coord; linarith [hk.2]
  have hshi : coord B O cut k≤ -1/9 := by unfold coord; linarith [hk.1]
  have hshape := Q4.Candidate.OrdinaryResponse.negative_shape _ hslo hshi
  have herr := (abs_le.mp (virtualField_shape_estimate B O cut (by omega) hcut k)).1
  change -(6*rho B O)≤(virtualField (spin : Fin B × Fin O → ℤ) cut k.val:ℝ)/((B:ℝ)*O)+shape (coord B O cut k) at herr
  have hnorm : 0<(virtualField (spin : Fin B × Fin O → ℤ) cut k.val:ℝ)/((B:ℝ)*O) := by
    linarith [rho_small B O hO hBO]
  have hbp : 0<B := by omega
  have hpos : 0<(pointField (spin : Fin B × Fin O → ℤ) ys p k:ℝ) := by
    rw [heq k]
    have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<(B:ℝ)*O)).mp hnorm
    simpa only [zero_mul] using hh
  have hn : ¬pointField (spin : Fin B × Fin O → ℤ) ys p k<0 := by
    have hh : 0<pointField (spin : Fin B × Fin O → ℤ) ys p k := by exact_mod_cast hpos
    omega
  simp [responseSpin,response,hn]

theorem weight_bounds_of_middle {B O : ℕ} (ys : Fin O → ℚ) (p : Point) (h8 : 8∣B)
    (hmid : ∀k : Fin B, 1/8≤u B k ∧ u B k≤7/8 → responseSpin ys p k=1) :
    (B:ℝ)/2≤(totalWeight (B:=B) ys p:ℝ) ∧ (totalWeight (B:=B) ys p:ℝ)≤B := by
  obtain ⟨n,hn⟩ := h8
  have hh := Q4.Candidate.OrdinaryResponse.half_weights_of_middle B n hn
    (fun k => (responseSpin ys p k:ℝ)) (responseSpin_bounds ys p) (by
      intro k hk1 hk2
      rw [hmid k (Q4.Candidate.OrdinaryResponse.middle_index_coordinates B n hn k ⟨hk1,hk2⟩)]
      norm_num)
  have hup := Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin B))) => (responseSpin_bounds ys p k).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hup
  simpa only [totalWeight,Int.cast_sum] using And.intro hh.2.2 hup

theorem negative_weight_bounds_of_middle {B O : ℕ} (ys : Fin O → ℚ) (p : Point) (h8 : 8∣B)
    (hmid : ∀k : Fin B, 1/8≤u B k ∧ u B k≤7/8 → responseSpin ys p k= -1) :
    -(B:ℝ)≤(totalWeight (B:=B) ys p:ℝ) ∧ (totalWeight (B:=B) ys p:ℝ)≤ -(B:ℝ)/2 := by
  obtain ⟨n,hn⟩ := h8
  have hh := Q4.Candidate.OrdinaryResponse.half_weights_of_middle B n hn
    (fun k => -(responseSpin ys p k:ℝ)) (by
      intro k
      have h := responseSpin_bounds ys p k
      constructor <;> linarith) (by
      intro k hk1 hk2
      rw [hmid k (Q4.Candidate.OrdinaryResponse.middle_index_coordinates B n hn k ⟨hk1,hk2⟩)]
      norm_num)
  have hlo := Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin B))) => (responseSpin_bounds ys p k).1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hlo
  rw [Finset.sum_neg_distrib] at hh
  have hs : (totalWeight (B:=B) ys p:ℝ)=∑k : Fin B, (responseSpin ys p k:ℝ) := by simp [totalWeight]
  rw [hs]
  constructor <;> linarith [hh.2.2]

theorem left_weight_bounds {N O cut : ℕ} (d : LeftGeometry N O cut)
    (hO : 1000≤O) (hBO : O≤N) (hcut : cut≤O) (h8 : 8∣N) (hearly : (cut:ℝ)/O≤1/514) :
    0 < totalWeight (B:=N) d.ys (leftPoint d) ∧
      (N:ℝ)/2≤(totalWeight (B:=N) d.ys (leftPoint d):ℝ) ∧
      (totalWeight (B:=N) d.ys (leftPoint d):ℝ)≤N := by
  have heq := left_field_eq_virtual d spin
  have hw := weight_bounds_of_middle d.ys (leftPoint d) h8
    (early_middle_of_virtual d.ys (leftPoint d) heq hO hBO hcut hearly)
  have hN : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpos : (0:ℝ)<(totalWeight (B:=N) d.ys (leftPoint d):ℝ) := by linarith [hw.1,hw.2]
  refine ⟨?_,by linarith [hw.1,hw.2],by linarith [hw.1,hw.2]⟩
  exact_mod_cast hpos

theorem placed_left_weight_bounds {N O cut : ℕ} (d : LeftGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i) ∈ B) (hy : ∀j, original (d.ys j) ∈ B)
    (hr : leftPoint d ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (leftPoint d) p)
    (hO : 1000≤O) (hBO : O≤N) (hcut : cut≤O) (h8 : 8∣N) (hearly : (cut:ℝ)/O≤1/514) :
    0 < totalWeight (B:=N) d.ys p ∧
      (N:ℝ)/2≤(totalWeight (B:=N) d.ys p:ℝ) ∧
      (totalWeight (B:=N) d.ys p:ℝ)≤N := by
  have heq := placed_left_field_eq_virtual d M B R p hf hy hr hproto hp spin
  have hw := weight_bounds_of_middle d.ys p h8
    (early_middle_of_virtual d.ys p heq hO hBO hcut hearly)
  have hN : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpos : (0:ℝ)<(totalWeight (B:=N) d.ys p:ℝ) := by linarith [hw.1,hw.2]
  refine ⟨?_,by linarith [hw.1,hw.2],by linarith [hw.1,hw.2]⟩
  exact_mod_cast hpos

theorem right_weight_bounds {N O cut : ℕ} (d : RightGeometry N O cut)
    (hO : 1000≤O) (hBO : O≤N) (hcut : cut≤O) (h8 : 8∣N) (hlate : 1-1/514≤(cut:ℝ)/O) :
    0 < -totalWeight (B:=N) d.ys (rightPoint d) ∧
      (N:ℝ)/2≤-(totalWeight (B:=N) d.ys (rightPoint d):ℝ) ∧
      -(totalWeight (B:=N) d.ys (rightPoint d):ℝ)≤N := by
  have heq := right_field_eq_virtual d spin
  have hw := negative_weight_bounds_of_middle d.ys (rightPoint d) h8
    (late_middle_of_virtual d.ys (rightPoint d) heq hO hBO hcut hlate)
  have hN : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpos : (0:ℝ)< -(totalWeight (B:=N) d.ys (rightPoint d):ℝ) := by linarith [hw.1,hw.2]
  refine ⟨?_,by linarith [hw.1,hw.2],by linarith [hw.1,hw.2]⟩
  exact_mod_cast hpos

theorem placed_right_weight_bounds {N O cut : ℕ} (d : RightGeometry N O cut)
    (M : ℕ) (B R : Finset Point) (p : Point)
    (hf : ∀i, frame (frameParameter N i) ∈ B) (hy : ∀j, original (d.ys j) ∈ B)
    (hr : rightPoint d ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (rightPoint d) p)
    (hO : 1000≤O) (hBO : O≤N) (hcut : cut≤O) (h8 : 8∣N) (hlate : 1-1/514≤(cut:ℝ)/O) :
    0 < -totalWeight (B:=N) d.ys p ∧
      (N:ℝ)/2≤-(totalWeight (B:=N) d.ys p:ℝ) ∧
      -(totalWeight (B:=N) d.ys p:ℝ)≤N := by
  have heq := placed_right_field_eq_virtual d M B R p hf hy hr hproto hp spin
  have hw := negative_weight_bounds_of_middle d.ys p h8
    (late_middle_of_virtual d.ys p heq hO hBO hcut hlate)
  have hN : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpos : (0:ℝ)< -(totalWeight (B:=N) d.ys p:ℝ) := by linarith [hw.1,hw.2]
  refine ⟨?_,by linarith [hw.1,hw.2],by linarith [hw.1,hw.2]⟩
  exact_mod_cast hpos

/-- Signed cost coefficient contributed by the actual canonically responding
rank fans to an actual core edge. -/
noncomputable def coreCoefficient {B O : ℕ} (ys : Fin O → ℚ) (p x y : Point) : ℤ := by
  classical
  exact ∑k : Fin B, if ProperCross p (frame (frameParameter B k)) x y
    then responseSpin ys p k else 0

noncomputable def coreCost {B O : ℕ} (ys : Fin O → ℚ) (p x y : Point) (color : Bool) : ℤ := by
  classical
  exact ∑k : Fin B, if ProperCross p (frame (frameParameter B k)) x y
    then (if color=response ys p k then 1 else 0) else 0

theorem coreCoefficient_cost_difference {B O : ℕ} (ys : Fin O → ℚ) (p x y : Point) :
    coreCoefficient (B:=B) ys p x y=coreCost (B:=B) ys p x y true-coreCost (B:=B) ys p x y false := by
  classical
  unfold coreCoefficient coreCost
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : ProperCross p (frame (frameParameter B k)) x y <;>
    cases hr : response ys p k <;> simp [hc,responseSpin,hr]

/-- Summing the actual selected-bundle crossing table gives precisely a
whole-column response weight times the selected rank indicator. -/
theorem placed_left_selected_coefficient {N O : ℕ} (ys : Fin O → ℚ)
    (M : ℕ) (B R : Finset Point) (a b tau mu : ℚ) (W ell : ℕ) (s t : Fin W) (p : Point)
    (hab : a<b) (hW : 2≤W) (hmu : 0<mu) (hmuW : 100*(W:ℚ)*mu≤1)
    (htau : 0<tau) (htauMu : 100*tau≤mu*(b-a))
    (hboxA : -1≤a-tau/2) (hboxB : b+tau/2≤1) (hell : ell+1<W)
    (hf : ∀k, frame (frameParameter N k) ∈ B)
    (hleft : original (cloneAt a tau W s.val) ∈ B) (hright : original (cloneAt b tau W t.val) ∈ B)
    (hr : leftRank a b tau W mu ell ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (leftRank a b tau W mu ell) p) :
    coreCoefficient (B:=N) ys p (original (cloneAt a tau W s.val)) (original (cloneAt b tau W t.val))=
      totalWeight (B:=N) ys p*(if ell<s.val then 1 else 0) := by
  have hc (k : Fin N) := placed_leftRank_crossing_table M B R a b tau mu (frameParameter N k) W ell s t p
    hab hW hmu hmuW htau htauMu hboxA hboxB (frameParameter_unit N k).le hell
    (hf k) hleft hright hr hproto hp
  unfold coreCoefficient
  simp_rw [hc]
  by_cases he : ell<s.val <;> simp [he,totalWeight]

/-- Summing the actual selected-bundle crossing table gives precisely a
whole-column response weight times the selected rank indicator. -/
theorem placed_right_selected_coefficient {N O : ℕ} (ys : Fin O → ℚ)
    (M : ℕ) (B R : Finset Point) (a b tau mu : ℚ) (W ell : ℕ) (s t : Fin W) (p : Point)
    (hab : a<b) (hW : 2≤W) (hmu : 0<mu) (hmuW : 100*(W:ℚ)*mu≤1)
    (htau : 0<tau) (htauMu : 100*tau≤mu*(b-a))
    (hboxA : -1≤a-tau/2) (hboxB : b+tau/2≤1) (hell : ell+1<W)
    (hf : ∀k, frame (frameParameter N k) ∈ B)
    (hleft : original (cloneAt a tau W s.val) ∈ B) (hright : original (cloneAt b tau W t.val) ∈ B)
    (hr : rightRank a b tau W mu ell ∈ R) (hproto : ∀q∈R, phi q<0 ∧ |q.2|<2)
    (hp : Placed M (constructionRadius B R) (rightRank a b tau W mu ell) p) :
    coreCoefficient (B:=N) ys p (original (cloneAt a tau W s.val)) (original (cloneAt b tau W t.val))=
      totalWeight (B:=N) ys p*(if t.val≤ell then 1 else 0) := by
  have hc (k : Fin N) := placed_rightRank_crossing_table M B R a b tau mu (frameParameter N k) W ell s t p
    hab hW hmu hmuW htau htauMu hboxA hboxB (frameParameter_unit N k).le hell
    (hf k) hleft hright hr hproto hp
  unfold coreCoefficient
  simp_rw [hc]
  by_cases he : t.val≤ell <;> simp [he,totalWeight]

end Q4.Candidate.RankResponse

#print axioms Q4.Candidate.RankResponse.response_minimizes
#print axioms Q4.Candidate.RankResponse.early_middle_of_virtual
#print axioms Q4.Candidate.RankResponse.late_middle_of_virtual
#print axioms Q4.Candidate.RankResponse.left_weight_bounds
#print axioms Q4.Candidate.RankResponse.right_weight_bounds
#print axioms Q4.Candidate.RankResponse.placed_left_weight_bounds
#print axioms Q4.Candidate.RankResponse.placed_right_weight_bounds
#print axioms Q4.Candidate.RankResponse.coreCoefficient_cost_difference
#print axioms Q4.Candidate.RankResponse.placed_left_selected_coefficient
#print axioms Q4.Candidate.RankResponse.placed_right_selected_coefficient
