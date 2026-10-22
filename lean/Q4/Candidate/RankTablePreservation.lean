import Q4.Candidate.RankNonincident

/-! The actual nonselected-core and complete virtual-column rank tables survive
the same single general-position placement radius as the selected rank table. -/
namespace Q4.Candidate.RankTablePreservation
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.RankGap Q4.Candidate.RankGapPreservation
open Q4.Candidate.RankNonselected Q4.Candidate.RankNonincident
open Q4.Candidate.OrdinaryFan Q4.Candidate.OrientationPreservation
open Q4.Candidate.UniformInsertion

/-- Geometric frame-side separation supplies the third fan determinant.
Only the two ray determinants remain to be instantiated by actual formulas. -/
theorem fan_preserved_of_rays (M : ℕ) (B R : Finset Point) (r p : Point) (z ti tk : ℚ)
    (hrvalid : (Vertex.program r).valid) (hi : |ti| ≤ 1) (hk : |tk| ≤ 1)
    (hri : orient r (original z) (frame ti) ≠ 0)
    (hrk : orient r (original z) (frame tk) ≠ 0)
    (hfi : frame ti ∈ B) (hfk : frame tk ∈ B) (hz : original z ∈ B) (hr : r ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) r p) :
    ProperCross p (frame tk) (original z) (frame ti) ↔
      ProperCross r (frame tk) (original z) (frame ti) := by
  have hdelta := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hdelta _ p hp
  have hfirst : orient (frame tk) (original z) r ≠ 0 := by
    rw [orient_cycle,orient_cycle,orient_reverse_last]
    exact neg_ne_zero.mpr hrk
  have hsecond : orient (frame tk) (frame ti) r ≠ 0 ∨ frame tk=frame ti := by
    by_cases he : tk=ti
    · exact Or.inr (congrArg frame he)
    · left
      rw [frame_side_orientation]
      exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm he))
        (ne_of_gt (frameSide_positive tk ti r hk hi hrvalid))
  have hthird : orient (original z) (frame ti) r ≠ 0 := by
    rw [orient_cycle,orient_cycle]
    exact hri
  exact one_program_crossing_preserved B R _ _ _ _ p hfk hz hfi hr
    (Or.inl hfirst) hsecond (Or.inl hthird) _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])

theorem nonparent_ray_nonzero (r : Point) (a z t delta : ℚ)
    (hd : 0 < delta) (hsep : 2*delta ≤ |z-a|)
    (hsign : (0 < orient r (original z) (frame t) ↔ z<a) ∧
      (orient r (original z) (frame t) < 0 ↔ a<z)) :
    orient r (original z) (frame t) ≠ 0 := by
  have hne : z ≠ a := by intro he; rw [he,sub_self,abs_zero] at hsep; linarith
  rcases lt_or_gt_of_ne hne with h|h
  · exact ne_of_gt (hsign.1.mpr h)
  · exact ne_of_lt (hsign.2.mpr h)

/-- Actual strict certificates for both entries of the all/zero table. -/
theorem leftRank_nonselected_determinants (a b tau w mu ell s z t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (hz : |z| ≤ 1) (ht : |t| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-a|) (hgap : 20*tau ≤ mu*(b-a)*|b-z|) :
    orient (frame t) (original (cloneAt a tau w s)) (leftRank a b tau w mu ell) ≠ 0 ∧
    orient (frame t) (original z) (leftRank a b tau w mu ell) ≠ 0 ∧
    orient (original (cloneAt a tau w s)) (original z) (leftRank a b tau w mu ell) ≠ 0 := by
  have hunit := clones_in_unit a b tau w s hab.le htau.le hw hboxA hboxB hs hs1
  have hnear := clone_macro_near a tau w s htau.le hw hs hs1
  have hparent := (leftRank_endpoint_sides a b tau w mu ell s 0 t hab hw hmu hmuW
    htau htauMu hboxA hboxB ht hell hell1 hs hs1 (by rfl) (by linarith)).1
  have hotherSign := leftRank_nonparent_ray_sign a b tau w mu ell z t hab hw hmu hmuW
    htau htauMu hboxA hboxB hell hell1 hz ht hsep
  have hnz := nonparent_ray_nonzero _ a z t (mu*(b-a)) (mul_pos hmu (sub_pos.mpr hab))
    (by nlinarith) hotherSign
  have hheight := height_between_all_clones a b tau w mu s 0 hab hw hmu hmuW htau htauMu
    hs hs1 (by rfl) (by linarith)
  have hrightUnit := (clones_in_unit a b tau w 0 hab.le htau.le hw hboxA hboxB (by rfl) (by linarith)).2
  have hy : |(leftRank a b tau w mu ell).2| ≤ 1 := by
    change |leftHeight a b mu| ≤ 1
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hunit.1).1],by linarith [(abs_le.mp hrightUnit).2]⟩
  have hsteer := leftRank_steering_bound a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hsupport := support_signs_of_steering (leftRank a b tau w mu ell) a b (cloneAt a tau w s) z mu tau
    hz hy htau rfl hsteer hnear hgap
  have hne : cloneAt a tau w s ≠ z := by
    intro he
    rw [he] at hnear
    nlinarith
  have hzb : z ≠ b := by intro he; rw [he,sub_self,abs_zero,mul_zero] at hgap; linarith
  refine ⟨?_,?_,?_⟩
  · rw [orient_cycle,orient_cycle]
    exact ne_of_lt hparent
  · rw [orient_cycle,orient_cycle,orient_reverse_last]
    exact neg_ne_zero.mpr hnz
  · rw [original_chord_orientation]
    apply mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne)))
    rcases lt_or_gt_of_ne hzb with h|h
    · exact ne_of_lt (hsupport.1.mpr h)
    · exact ne_of_gt (hsupport.2.mpr h)

theorem rightRank_nonselected_determinants (a b tau w mu ell s z t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (hz : |z| ≤ 1) (ht : |t| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-b|) (hgap : 20*tau ≤ mu*(b-a)*|a-z|) :
    orient (frame t) (original (cloneAt b tau w s)) (rightRank a b tau w mu ell) ≠ 0 ∧
    orient (frame t) (original z) (rightRank a b tau w mu ell) ≠ 0 ∧
    orient (original (cloneAt b tau w s)) (original z) (rightRank a b tau w mu ell) ≠ 0 := by
  have hspan : -a-(-b) = b-a := by ring
  have hh := leftRank_nonselected_determinants (-b) (-a) tau w mu (w-2-ell) (w-1-s) (-z) (-t)
    (by linarith) hw hmu hmuW htau (by simpa only [hspan] using htauMu)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by simpa using hz) (by simpa using ht)
    (by simpa only [hspan,neg_sub_neg,abs_sub_comm b z] using hsep)
    (by simpa only [hspan,neg_sub_neg,abs_sub_comm z a] using hgap)
  rw [clone_reverse b tau w s hw,←rightRank_reflection a b tau w mu ell hw,
    ←reflect_frame,←reflect_original,←reflect_original] at hh
  simpa only [orient_reflect,neg_ne_zero] using hh

theorem placed_leftRank_nonselected_core (M : ℕ) (B R : Finset Point)
    (a b tau w mu ell s z t : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (hz : |z| ≤ 1) (ht : |t| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-a|) (hgap : 20*tau ≤ mu*(b-a)*|b-z|)
    (hframe : frame t ∈ B) (hparent : original (cloneAt a tau w s) ∈ B)
    (hother : original z ∈ B) (hr : leftRank a b tau w mu ell ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (leftRank a b tau w mu ell) p) :
    ProperCross p (frame t) (original (cloneAt a tau w s)) (original z) ↔ a < z ∧ z < b := by
  have hdelta := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hdelta _ p hp
  have hnz := leftRank_nonselected_determinants a b tau w mu ell s z t
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hs hs1 hz ht hsep hgap
  have he := one_program_crossing_preserved B R _ _ _ _ p hframe hparent hother hr
    (Or.inl hnz.1) (Or.inl hnz.2.1) (Or.inl hnz.2.2) _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  exact he.trans (leftRank_nonselected_core a b tau w mu ell s z t
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hs hs1 hz ht hsep hgap)

theorem placed_leftRank_parent_fan (M N : ℕ) (B R : Finset Point)
    (i k : Fin N) (a b tau w mu ell s : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1)
    (hfi : frame (frameParameter N i) ∈ B) (hfk : frame (frameParameter N k) ∈ B)
    (hzmem : original (cloneAt a tau w s) ∈ B) (hr : leftRank a b tau w mu ell ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (leftRank a b tau w mu ell) p) :
    ProperCross p (frame (frameParameter N k)) (original (cloneAt a tau w s)) (frame (frameParameter N i)) ↔
      i < k := by
  have hvalid := leftRank_valid a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hne (j : Fin N) : orient (leftRank a b tau w mu ell) (original (cloneAt a tau w s)) (frame (frameParameter N j)) ≠ 0 := by
    have hh := (leftRank_endpoint_sides a b tau w mu ell s 0 (frameParameter N j)
      hab hw hmu hmuW htau htauMu hboxA hboxB (frameParameter_unit N j).le hell hell1
      hs hs1 (by rfl) (by linarith)).1
    rw [orient_reverse_last] at hh
    exact ne_of_gt (by linarith)
  have he := fan_preserved_of_rays M B R (leftRank a b tau w mu ell) p (cloneAt a tau w s)
    (frameParameter N i) (frameParameter N k) hvalid
    (frameParameter_unit N i).le (frameParameter_unit N k).le (hne i) (hne k)
    hfi hfk hzmem hr hproto hp
  exact he.trans (leftRank_parent_fan_indexed N i k a b tau w mu ell s
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hs hs1)

theorem placed_leftRank_nonparent_fan (M N : ℕ) (B R : Finset Point)
    (i k : Fin N) (a b tau w mu ell z : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hz : |z| ≤ 1) (hsep : 2*mu*(b-a) ≤ |z-a|)
    (hfi : frame (frameParameter N i) ∈ B) (hfk : frame (frameParameter N k) ∈ B)
    (hzmem : original (z) ∈ B) (hr : leftRank a b tau w mu ell ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (leftRank a b tau w mu ell) p) :
    ProperCross p (frame (frameParameter N k)) (original (z)) (frame (frameParameter N i)) ↔
      (i < k ∧ z < a) ∨ (k < i ∧ a < z) := by
  have hvalid := leftRank_valid a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hne (j : Fin N) : orient (leftRank a b tau w mu ell) (original (z)) (frame (frameParameter N j)) ≠ 0 := by
    exact nonparent_ray_nonzero _ a z _ (mu*(b-a)) (mul_pos hmu (sub_pos.mpr hab))
      (by nlinarith) (leftRank_nonparent_ray_sign a b tau w mu ell z (frameParameter N j)
        hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hz (frameParameter_unit N j).le hsep)
  have he := fan_preserved_of_rays M B R (leftRank a b tau w mu ell) p (z)
    (frameParameter N i) (frameParameter N k) hvalid
    (frameParameter_unit N i).le (frameParameter_unit N k).le (hne i) (hne k)
    hfi hfk hzmem hr hproto hp
  exact he.trans (leftRank_nonparent_fan_indexed N i k a b tau w mu ell z
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hz hsep)

theorem placed_rightRank_nonselected_core (M : ℕ) (B R : Finset Point)
    (a b tau w mu ell s z t : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (hz : |z| ≤ 1) (ht : |t| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-b|) (hgap : 20*tau ≤ mu*(b-a)*|a-z|)
    (hframe : frame t ∈ B) (hparent : original (cloneAt b tau w s) ∈ B)
    (hother : original z ∈ B) (hr : rightRank a b tau w mu ell ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (rightRank a b tau w mu ell) p) :
    ProperCross p (frame t) (original (cloneAt b tau w s)) (original z) ↔ a < z ∧ z < b := by
  have hdelta := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hdelta _ p hp
  have hnz := rightRank_nonselected_determinants a b tau w mu ell s z t
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hs hs1 hz ht hsep hgap
  have he := one_program_crossing_preserved B R _ _ _ _ p hframe hparent hother hr
    (Or.inl hnz.1) (Or.inl hnz.2.1) (Or.inl hnz.2.2) _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  exact he.trans (rightRank_nonselected_core a b tau w mu ell s z t
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hs hs1 hz ht hsep hgap)

theorem placed_rightRank_parent_fan (M N : ℕ) (B R : Finset Point)
    (i k : Fin N) (a b tau w mu ell s : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1)
    (hfi : frame (frameParameter N i) ∈ B) (hfk : frame (frameParameter N k) ∈ B)
    (hzmem : original (cloneAt b tau w s) ∈ B) (hr : rightRank a b tau w mu ell ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (rightRank a b tau w mu ell) p) :
    ProperCross p (frame (frameParameter N k)) (original (cloneAt b tau w s)) (frame (frameParameter N i)) ↔
      k < i := by
  have hvalid := rightRank_valid a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hne (j : Fin N) : orient (rightRank a b tau w mu ell) (original (cloneAt b tau w s)) (frame (frameParameter N j)) ≠ 0 := by
    exact ne_of_lt (rightRank_parent_ray_negative a b tau w mu ell s (frameParameter N j)
      hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hs hs1 (frameParameter_unit N j).le)
  have he := fan_preserved_of_rays M B R (rightRank a b tau w mu ell) p (cloneAt b tau w s)
    (frameParameter N i) (frameParameter N k) hvalid
    (frameParameter_unit N i).le (frameParameter_unit N k).le (hne i) (hne k)
    hfi hfk hzmem hr hproto hp
  exact he.trans (rightRank_parent_fan_indexed N i k a b tau w mu ell s
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hs hs1)

theorem placed_rightRank_nonparent_fan (M N : ℕ) (B R : Finset Point)
    (i k : Fin N) (a b tau w mu ell z : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hz : |z| ≤ 1) (hsep : 2*mu*(b-a) ≤ |z-b|)
    (hfi : frame (frameParameter N i) ∈ B) (hfk : frame (frameParameter N k) ∈ B)
    (hzmem : original (z) ∈ B) (hr : rightRank a b tau w mu ell ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (rightRank a b tau w mu ell) p) :
    ProperCross p (frame (frameParameter N k)) (original (z)) (frame (frameParameter N i)) ↔
      (i < k ∧ z < b) ∨ (k < i ∧ b < z) := by
  have hvalid := rightRank_valid a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hne (j : Fin N) : orient (rightRank a b tau w mu ell) (original (z)) (frame (frameParameter N j)) ≠ 0 := by
    exact nonparent_ray_nonzero _ b z _ (mu*(b-a)) (mul_pos hmu (sub_pos.mpr hab))
      (by nlinarith) (rightRank_nonparent_ray_sign a b tau w mu ell z (frameParameter N j)
        hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hz (frameParameter_unit N j).le hsep)
  have he := fan_preserved_of_rays M B R (rightRank a b tau w mu ell) p (z)
    (frameParameter N i) (frameParameter N k) hvalid
    (frameParameter_unit N i).le (frameParameter_unit N k).le (hne i) (hne k)
    hfi hfk hzmem hr hproto hp
  exact he.trans (rightRank_nonparent_fan_indexed N i k a b tau w mu ell z
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hz hsep)

end Q4.Candidate.RankTablePreservation

#print axioms Q4.Candidate.RankTablePreservation.fan_preserved_of_rays
#print axioms Q4.Candidate.RankTablePreservation.leftRank_nonselected_determinants
#print axioms Q4.Candidate.RankTablePreservation.rightRank_nonselected_determinants
#print axioms Q4.Candidate.RankTablePreservation.placed_leftRank_nonselected_core
#print axioms Q4.Candidate.RankTablePreservation.placed_rightRank_nonselected_core
#print axioms Q4.Candidate.RankTablePreservation.placed_leftRank_parent_fan
#print axioms Q4.Candidate.RankTablePreservation.placed_rightRank_parent_fan
#print axioms Q4.Candidate.RankTablePreservation.placed_leftRank_nonparent_fan
#print axioms Q4.Candidate.RankTablePreservation.placed_rightRank_nonparent_fan
