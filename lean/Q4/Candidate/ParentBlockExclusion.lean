import Q4.Candidate.OrdinaryTablePreservation

/-! Short core edges inside the parent's own clone block require only the two
same-side fan rays. Their supporting-line determinant need not be nonzero. -/
namespace Q4.Candidate.ParentBlockExclusion
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.RankGap Q4.Candidate.RankGapPreservation
open Q4.Candidate.RankNonselected Q4.Candidate.OrdinaryFan
open Q4.Candidate.OrdinaryTablePreservation Q4.Candidate.OrientationPreservation
open Q4.Candidate.UniformInsertion

/-- Preserve a no-crossing certificate using only the two strict same-side
rays. No assertion is made about the unused core supporting-line determinant. -/
theorem placed_no_cross_of_same_rays (M : ℕ) (B R : Finset Point) (r p f c d : Point)
    (hprod : 0 < orient r f c * orient r f d)
    (hf : f ∈ B) (hc : c ∈ B) (hd : d ∈ B) (hr : r ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) r p) : ¬ProperCross p f c d := by
  have hdelta := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hdelta _ p hp
  have hn1 : orient f c r ≠ 0 := by
    rw [orient_cycle,orient_cycle]
    intro he
    rw [he,zero_mul] at hprod
    exact (lt_irrefl 0 hprod)
  have hn2 : orient f d r ≠ 0 := by
    rw [orient_cycle,orient_cycle]
    intro he
    rw [he,mul_zero] at hprod
    exact (lt_irrefl 0 hprod)
  have hs1 := fixed_base_orientation_preserved B R f c r p hf hc hr hn1 _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  have hs2 := fixed_base_orientation_preserved B R f d r p hf hd hr hn2 _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  have hs := sameSigns_mul_neg _ _ _ _ hs1 hs2
  rw [orient_cycle f c p,orient_cycle c p f,orient_cycle f d p,orient_cycle d p f,
    orient_cycle f c r,orient_cycle c r f,orient_cycle f d r,orient_cycle d r f] at hs
  exact fun hcross => (not_lt_of_ge hprod.le) (hs.mp hcross.1)

theorem ordinary_parent_block_rays (N : ℕ) (hN : Even N) (k : Fin N)
    (a c d mu : ℚ) (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1)
    (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hcloneC : 3*((N:ℚ)+1)*|c-a| ≤ mu) (hcloneD : 3*((N:ℚ)+1)*|d-a| ≤ mu) :
    0 < orient (ordinary a mu) (frame (frameParameter N k)) (original c) *
      orient (ordinary a mu) (frame (frameParameter N k)) (original d) := by
  have ht : frameParameter N k ≠ 0 := by
    intro he
    have hh := frameParameter_gap N hN k
    rw [he,abs_zero,mul_zero] at hh
    norm_num at hh
  have hsc := ordinary_clone_sign a c mu (frameParameter N k) ha hc hm hm1
    (frameParameter_unit N k).le ht (indexed_clone_margin N hN k a c mu hcloneC)
  have hsd := ordinary_clone_sign a d mu (frameParameter N k) ha hd hm hm1
    (frameParameter_unit N k).le ht (indexed_clone_margin N hN k a d mu hcloneD)
  rw [orient_reverse_last (ordinary a mu) (frame (frameParameter N k)) (original c),
    orient_reverse_last (ordinary a mu) (frame (frameParameter N k)) (original d),neg_mul_neg]
  rcases lt_or_gt_of_ne ht with h|h
  · exact mul_pos_of_neg_of_neg (hsc.2.mpr h) (hsd.2.mpr h)
  · exact mul_pos (hsc.1.mpr h) (hsd.1.mpr h)

theorem placed_ordinary_parent_block (M N : ℕ) (B R : Finset Point) (hN : Even N)
    (k : Fin N) (a c d mu : ℚ) (p : Point)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hcloneC : 3*((N:ℚ)+1)*|c-a| ≤ mu) (hcloneD : 3*((N:ℚ)+1)*|d-a| ≤ mu)
    (hframe : frame (frameParameter N k) ∈ B) (hcMem : original c ∈ B)
    (hdMem : original d ∈ B) (hr : ordinary a mu ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (ordinary a mu) p) :
    ¬ProperCross p (frame (frameParameter N k)) (original c) (original d) := by
  exact placed_no_cross_of_same_rays M B R _ p _ _ _
    (ordinary_parent_block_rays N hN k a c d mu ha hc hd hm hm1 hcloneC hcloneD)
    hframe hcMem hdMem hr hproto hp

theorem placed_leftRank_parent_block (M : ℕ) (B R : Finset Point)
    (a b tau w mu ell s v t : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (hv : 0 ≤ v) (hv1 : v ≤ w-1) (ht : |t| ≤ 1)
    (hframe : frame t ∈ B) (hsMem : original (cloneAt a tau w s) ∈ B)
    (hvMem : original (cloneAt a tau w v) ∈ B) (hr : leftRank a b tau w mu ell ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (leftRank a b tau w mu ell) p) :
    ¬ProperCross p (frame t) (original (cloneAt a tau w s)) (original (cloneAt a tau w v)) := by
  have hprod : 0 < orient (leftRank a b tau w mu ell) (frame t) (original (cloneAt a tau w s)) *
      orient (leftRank a b tau w mu ell) (frame t) (original (cloneAt a tau w v)) := by
    have hfirst := (leftRank_endpoint_sides a b tau w mu ell s 0 t hab hw hmu hmuW
      htau htauMu hboxA hboxB ht hell hell1 hs hs1 (by rfl) (by linarith)).1
    have hsecond := (leftRank_endpoint_sides a b tau w mu ell v 0 t hab hw hmu hmuW
      htau htauMu hboxA hboxB ht hell hell1 hv hv1 (by rfl) (by linarith)).1
    exact mul_pos_of_neg_of_neg hfirst hsecond
  exact placed_no_cross_of_same_rays M B R _ p _ _ _ hprod hframe hsMem hvMem hr hproto hp

theorem placed_rightRank_parent_block (M : ℕ) (B R : Finset Point)
    (a b tau w mu ell s v t : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (hv : 0 ≤ v) (hv1 : v ≤ w-1) (ht : |t| ≤ 1)
    (hframe : frame t ∈ B) (hsMem : original (cloneAt b tau w s) ∈ B)
    (hvMem : original (cloneAt b tau w v) ∈ B) (hr : rightRank a b tau w mu ell ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (rightRank a b tau w mu ell) p) :
    ¬ProperCross p (frame t) (original (cloneAt b tau w s)) (original (cloneAt b tau w v)) := by
  have hprod : 0 < orient (rightRank a b tau w mu ell) (frame t) (original (cloneAt b tau w s)) *
      orient (rightRank a b tau w mu ell) (frame t) (original (cloneAt b tau w v)) := by
    have hfirst := rightRank_parent_ray_negative a b tau w mu ell s t hab hw hmu hmuW
      htau htauMu hboxA hboxB hell hell1 hs hs1 ht
    have hsecond := rightRank_parent_ray_negative a b tau w mu ell v t hab hw hmu hmuW
      htau htauMu hboxA hboxB hell hell1 hv hv1 ht
    rw [orient_reverse_last (rightRank a b tau w mu ell) (frame t) (original (cloneAt b tau w s)),
      orient_reverse_last (rightRank a b tau w mu ell) (frame t) (original (cloneAt b tau w v)),neg_mul_neg]
    exact mul_pos_of_neg_of_neg hfirst hsecond
  exact placed_no_cross_of_same_rays M B R _ p _ _ _ hprod hframe hsMem hvMem hr hproto hp

end Q4.Candidate.ParentBlockExclusion

#print axioms Q4.Candidate.ParentBlockExclusion.placed_no_cross_of_same_rays
#print axioms Q4.Candidate.ParentBlockExclusion.ordinary_parent_block_rays
#print axioms Q4.Candidate.ParentBlockExclusion.placed_ordinary_parent_block
#print axioms Q4.Candidate.ParentBlockExclusion.placed_leftRank_parent_block
#print axioms Q4.Candidate.ParentBlockExclusion.placed_rightRank_parent_block
