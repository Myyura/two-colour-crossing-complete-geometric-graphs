import Q4.Candidate.RankGap
import Q4.Candidate.OrientationPreservation

/-!
The selected-bundle rank tables survive the common general-position insertion.
All three moving determinants are proved nonzero from the actual clone/rank
coordinates. In particular, noncrossing entries are protected too: absence of
a crossing alone would not have supplied the necessary strict margin.
-/

namespace Q4.Candidate.RankGapPreservation

open Q4.Candidate.ConvexSeparation Q4.Candidate.UniformInsertion
open Q4.Candidate.OrientationPreservation Q4.Candidate.RankGap

theorem leftRank_endpoint_sides (a b tau w mu ell s t z : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1) (hz : |z| ≤ 1)
    (hell : 0 ≤ ell) (hell' : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs' : s ≤ w-1) (ht : 0 ≤ t) (ht' : t ≤ w-1) :
    orient (leftRank a b tau w mu ell) (frame z) (original (cloneAt a tau w s)) < 0 ∧
    0 < orient (leftRank a b tau w mu ell) (frame z) (original (cloneAt b tau w t)) := by
  have hell0 : ell ≤ w-1 := by linarith
  have hell1 : 0 ≤ ell+1 := by linarith
  have hw0 : 0 ≤ w-1 := by linarith
  have huu := clones_in_unit a b tau w s (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB hs hs'
  have hvv := clones_in_unit a b tau w t (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB ht ht'
  have he0 := clones_in_unit a b tau w ell (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB hell hell0
  have he1 := clones_in_unit a b tau w (ell+1) (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB hell1 hell'
  have hb0 := clones_in_unit a b tau w 0 (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB (by rfl) hw0
  have hb1 := clones_in_unit a b tau w (w-1) (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB hw0 (by rfl)
  have hbetween := height_between_all_clones a b tau w mu s t hab hw hmu hmuW htau htauMu hs hs' ht ht'
  have hbetween0 := height_between_all_clones a b tau w mu ell 0 hab hw hmu hmuW htau htauMu hell hell0 (by rfl) hw0
  have hbetween1 := height_between_all_clones a b tau w mu (ell+1) (w-1) hab hw hmu hmuW htau htauMu hell1 hell' hw0 (by rfl)
  have hphi : phi (leftRank a b tau w mu ell) ≤ 0 := by
    exact le_of_lt (rank_midpoint_inside _ _ _ _ _ hbetween0.1 hbetween0.2 hbetween1.1 hbetween1.2)
  have hry : |(leftRank a b tau w mu ell).2| ≤ 1 := by
    apply abs_le.mpr
    dsimp [leftRank]
    constructor
    · linarith [(abs_le.mp huu.1).1,hbetween.1]
    · linarith [(abs_le.mp hvv.2).2,hbetween.2]
  have hgap := height_gaps_pay_width a b tau w mu s t hab hw hmu hmuW htau htauMu hs hs' ht ht'
  have hgapA : tau ≤ |leftHeight a b mu-cloneAt a tau w s| := by
    rw [abs_of_pos (sub_pos.mpr hbetween.1)]; exact hgap.1
  have hgapB : tau ≤ |leftHeight a b mu-cloneAt b tau w t| := by
    rw [abs_of_neg (sub_neg.mpr hbetween.2)]; linarith [hgap.2]
  have hslopeA : |(leftRank a b tau w mu ell).1-(original (cloneAt a tau w s)).1| ≤
      |(leftRank a b tau w mu ell).2-cloneAt a tau w s|/10 := by
    exact midpoint_endpoint_slope _ _ _ _ _ _ tau he0.1 hb0.2 he1.1 hb1.2 huu.1
      (Or.inl (clone_near_same_block a tau w s ell (le_of_lt htau) hw hs hs' hell hell0))
      (Or.inl (clone_near_same_block a tau w s (ell+1) (le_of_lt htau) hw hs hs' hell1 hell')) hgapA
  have hslopeB : |(leftRank a b tau w mu ell).1-(original (cloneAt b tau w t)).1| ≤
      |(leftRank a b tau w mu ell).2-cloneAt b tau w t|/10 := by
    exact midpoint_endpoint_slope _ _ _ _ _ _ tau he0.1 hb0.2 he1.1 hb1.2 hvv.2
      (Or.inr (clone_near_same_block b tau w t 0 (le_of_lt htau) hw ht ht' (by rfl) hw0))
      (Or.inr (clone_near_same_block b tau w t (w-1) (le_of_lt htau) hw ht ht' hw0 (by rfl))) hgapB
  exact ⟨(frame_endpoint_signs _ _ _ hphi hry hz hslopeA).1 hbetween.1,
    (frame_endpoint_signs _ _ _ hphi hry hz hslopeB).2 hbetween.2⟩

/-- Even entries on the noncrossing side have strict determinant certificates. -/
theorem leftRank_determinants_nonzero (a b tau mu z : ℚ) (W ell : ℕ) (s t : Fin W)
    (hab : a < b) (hW : 2 ≤ W) (hmu : 0 < mu) (hmuW : 100*(W : ℚ)*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1) (hz : |z| ≤ 1)
    (hell : ell+1 < W) :
    orient (frame z) (original (cloneAt a tau W s.val)) (leftRank a b tau W mu ell) ≠ 0 ∧
    orient (frame z) (original (cloneAt b tau W t.val)) (leftRank a b tau W mu ell) ≠ 0 ∧
    orient (original (cloneAt a tau W s.val)) (original (cloneAt b tau W t.val))
      (leftRank a b tau W mu ell) ≠ 0 := by
  have hw : (2:ℚ) ≤ W := by exact_mod_cast hW
  have he0 : (0:ℚ) ≤ ell := by positivity
  have he1 : (ell:ℚ)+1 ≤ (W:ℚ)-1 := by
    have hh : (ell:ℚ)+2 ≤ W := by exact_mod_cast (by omega : ell+2 ≤ W)
    linarith
  have hs : (0:ℚ) ≤ s.val := by positivity
  have hs' : (s.val:ℚ) ≤ (W:ℚ)-1 := by
    have hh : (s.val:ℚ)+1 ≤ W := by exact_mod_cast (by omega : s.val+1 ≤ W)
    linarith
  have ht : (0:ℚ) ≤ t.val := by positivity
  have ht' : (t.val:ℚ) ≤ (W:ℚ)-1 := by
    have hh : (t.val:ℚ)+1 ≤ W := by exact_mod_cast (by omega : t.val+1 ≤ W)
    linarith
  have hside := leftRank_endpoint_sides a b tau W mu ell s.val t.val z hab hw hmu hmuW
    htau htauMu hboxA hboxB hz he0 he1 hs hs' ht ht'
  rw [orient_cycle _ (frame z),orient_cycle _ (frame z)] at hside
  refine ⟨ne_of_lt hside.1,ne_of_gt hside.2,?_⟩
  have hbetween := height_between_all_clones a b tau W mu s.val t.val hab hw hmu hmuW htau htauMu hs hs' ht ht'
  have hdiff : cloneAt b tau W t.val-cloneAt a tau W s.val ≠ 0 := by linarith [hbetween.1,hbetween.2]
  rw [source_orientation]
  apply mul_ne_zero hdiff
  by_cases hlow : s.val ≤ ell
  · have hh := lower_ranks_below_midpoint a b tau W mu ell s.val t.val hab hw hmu hmuW
      htau htauMu he0 he1 hs (by exact_mod_cast hlow) ht ht'
    exact ne_of_lt (sub_neg.mpr hh)
  · have hhigh : ell+1 ≤ s.val := by omega
    have hh := upper_ranks_above_midpoint a b tau W mu ell s.val t.val hab hw hmu hmuW
      htau htauMu he0 he1 (by exact_mod_cast hhigh) hs' ht ht'
    exact ne_of_gt (sub_pos.mpr hh)

/-- Actual final left-rank copies retain the full selected-bundle table. The
radius and determinant margin are computed from B,R; no crossing is assumed. -/
theorem placed_leftRank_crossing_table (M : ℕ) (B R : Finset Point)
    (a b tau mu z : ℚ) (W ell : ℕ) (s t : Fin W) (p : Point)
    (hab : a < b) (hW : 2 ≤ W) (hmu : 0 < mu) (hmuW : 100*(W : ℚ)*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1) (hz : |z| ≤ 1) (hell : ell+1 < W)
    (hframe : frame z ∈ B) (hleft : original (cloneAt a tau W s.val) ∈ B)
    (hright : original (cloneAt b tau W t.val) ∈ B)
    (hr : leftRank a b tau W mu ell ∈ R)
    (hproto : ∀ r ∈ R, phi r < 0 ∧ |r.2| < 2)
    (hp : Placed M (constructionRadius B R) (leftRank a b tau W mu ell) p) :
    ProperCross p (frame z) (original (cloneAt a tau W s.val))
      (original (cloneAt b tau W t.val)) ↔ ell < s.val := by
  have hd := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hd _ p hp
  have hnz := leftRank_determinants_nonzero a b tau mu z W ell s t hab hW hmu hmuW
    htau htauMu hboxA hboxB hz hell
  have he := one_program_crossing_preserved B R _ _ _ _ p hframe hleft hright hr
    (Or.inl hnz.1) (Or.inl hnz.2.1) (Or.inl hnz.2.2) _ hd
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  exact he.trans (leftRank_crossing_table a b tau mu z W ell s t hab hW hmu hmuW
    htau htauMu hboxA hboxB hz hell)

theorem orient_reflect (a b c : Point) :
    orient (reflect a) (reflect b) (reflect c) = -orient a b c := by
  unfold orient reflect
  ring

/-- The reflected right construction supplies the same strict certificates. -/
theorem rightRank_determinants_nonzero (a b tau mu z : ℚ) (W ell : ℕ) (s t : Fin W)
    (hab : a < b) (hW : 2 ≤ W) (hmu : 0 < mu) (hmuW : 100*(W : ℚ)*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1) (hz : |z| ≤ 1)
    (hell : ell+1 < W) :
    orient (frame z) (original (cloneAt a tau W s.val)) (rightRank a b tau W mu ell) ≠ 0 ∧
    orient (frame z) (original (cloneAt b tau W t.val)) (rightRank a b tau W mu ell) ≠ 0 ∧
    orient (original (cloneAt a tau W s.val)) (original (cloneAt b tau W t.val))
      (rightRank a b tau W mu ell) ≠ 0 := by
  let L : ℕ := W-2-ell
  have hLsum : L+ell+2 = W := by dsimp [L]; omega
  have hLsumR : (L:ℚ)+ell+2 = W := by exact_mod_cast hLsum
  have hL : (L:ℚ) = (W:ℚ)-2-ell := by linarith
  have hLbound : L+1 < W := by omega
  have hw : (2:ℚ) ≤ W := by exact_mod_cast hW
  have hnz := leftRank_determinants_nonzero (-b) (-a) tau mu (-z) W L t.rev s.rev
    (by linarith) hW hmu hmuW htau (by linarith) (by linarith) (by linarith)
    (by simpa using hz) hLbound
  rw [clone_rev_fin b tau W t hW,clone_rev_fin a tau W s hW] at hnz
  rw [hL, ← rightRank_reflection a b tau W mu ell hw,
    ← reflect_frame, ← reflect_original, ← reflect_original] at hnz
  simp only [orient_reflect,neg_ne_zero] at hnz
  have hswap : orient (original (cloneAt b tau W t.val)) (original (cloneAt a tau W s.val))
      (rightRank a b tau W mu ell) =
    -orient (original (cloneAt a tau W s.val)) (original (cloneAt b tau W t.val))
      (rightRank a b tau W mu ell) := by unfold orient; ring
  rw [hswap,neg_ne_zero] at hnz
  exact ⟨hnz.2.1,hnz.1,hnz.2.2⟩

/-- Every final right-rank copy retains the complete opposite-rank table. -/
theorem placed_rightRank_crossing_table (M : ℕ) (B R : Finset Point)
    (a b tau mu z : ℚ) (W ell : ℕ) (s t : Fin W) (p : Point)
    (hab : a < b) (hW : 2 ≤ W) (hmu : 0 < mu) (hmuW : 100*(W : ℚ)*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1) (hz : |z| ≤ 1) (hell : ell+1 < W)
    (hframe : frame z ∈ B) (hleft : original (cloneAt a tau W s.val) ∈ B)
    (hright : original (cloneAt b tau W t.val) ∈ B)
    (hr : rightRank a b tau W mu ell ∈ R)
    (hproto : ∀ r ∈ R, phi r < 0 ∧ |r.2| < 2)
    (hp : Placed M (constructionRadius B R) (rightRank a b tau W mu ell) p) :
    ProperCross p (frame z) (original (cloneAt a tau W s.val))
      (original (cloneAt b tau W t.val)) ↔ t.val ≤ ell := by
  have hd := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hd _ p hp
  have hnz := rightRank_determinants_nonzero a b tau mu z W ell s t hab hW hmu hmuW
    htau htauMu hboxA hboxB hz hell
  have he := one_program_crossing_preserved B R _ _ _ _ p hframe hleft hright hr
    (Or.inl hnz.1) (Or.inl hnz.2.1) (Or.inl hnz.2.2) _ hd
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  exact he.trans (rightRank_crossing_table a b tau mu z W ell s t hab hW hmu hmuW
    htau htauMu hboxA hboxB hz hell)

end Q4.Candidate.RankGapPreservation

#print axioms Q4.Candidate.RankGapPreservation.leftRank_endpoint_sides
#print axioms Q4.Candidate.RankGapPreservation.leftRank_determinants_nonzero
#print axioms Q4.Candidate.RankGapPreservation.placed_leftRank_crossing_table
#print axioms Q4.Candidate.RankGapPreservation.rightRank_determinants_nonzero
#print axioms Q4.Candidate.RankGapPreservation.placed_rightRank_crossing_table
