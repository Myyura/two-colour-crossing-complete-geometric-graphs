import Q4.Candidate.RankNonselected

/-! Rank fans cannot meet a core edge with neither endpoint in their parent
macro block. A quadratic curvature margin controls the actual two endpoints,
including short edges in a single other block. -/
namespace Q4.Candidate.RankNonincident
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.RankGap Q4.Candidate.RankGapPreservation
open Q4.Candidate.RankNonselected Q4.Candidate.OrdinaryFan
open Q4.Candidate.OrdinaryNonincident Q4.Candidate.OrientationPreservation
open Q4.Candidate.UniformInsertion

/-- A uniform coordinate perturbation changes a cap-chord offset by less than
2 delta, without dividing by the distance between the chord endpoints. -/
theorem chord_offset_change (r : Point) (a c d delta : ℚ)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1)
    (hx : |r.1-(original a).1| ≤ delta) (hy : |r.2-(original a).2| ≤ delta) :
    |r.1-chordX c d r.2+(a-c)*(a-d)/100| ≤ 2*delta := by
  have hdelta : 0 ≤ delta := (abs_nonneg _).trans hx
  have hcd : |c+d| ≤ 2 := (abs_add_le c d).trans (by linarith)
  have hprod : |(c+d)*(r.2-(original a).2)/100| ≤ delta/50 := by
    rw [abs_div,abs_mul]
    norm_num
    nlinarith [mul_le_mul hcd hy (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 2)]
  have he : r.1-chordX c d r.2+(a-c)*(a-d)/100 =
      (r.1-(original a).1)+(c+d)*(r.2-(original a).2)/100 := by
    unfold chordX original
    ring
  rw [he]
  have hh := abs_add_le (r.1-(original a).1) ((c+d)*(r.2-(original a).2)/100)
  linarith

theorem curvature_ray_separation (a c d delta : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hdelta : 0 < delta)
    (hcurve : 200*delta < |c-a| * |d-a|) :
    2*delta ≤ |c-a| ∧ 2*delta ≤ |d-a| := by
  have hc2 : |c-a| ≤ 2 := (abs_sub c a).trans (by linarith)
  have hd2 : |d-a| ≤ 2 := (abs_sub d a).trans (by linarith)
  have hp0 := mul_le_mul_of_nonneg_left hd2 (abs_nonneg (c-a))
  have hp1 := mul_le_mul_of_nonneg_right hc2 (abs_nonneg (d-a))
  constructor <;> nlinarith

/-- Actual supporting-line signs survive a quadratic margin. -/
theorem chord_offset_signs (r : Point) (a c d delta : ℚ)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1)
    (hx : |r.1-(original a).1| ≤ delta) (hy : |r.2-(original a).2| ≤ delta)
    (hcurve : 200*delta < |c-a| * |d-a|) :
    ((c < a ∧ a < d) ∨ (d < a ∧ a < c) → 0 < r.1-chordX c d r.2) ∧
    ((c < a ∧ d < a) ∨ (a < c ∧ a < d) → r.1-chordX c d r.2 < 0) := by
  have herr := chord_offset_change r a c d delta hc hd hx hy
  constructor
  · rintro (⟨hca,had⟩|⟨hda,hac⟩)
    · rw [abs_of_neg (sub_neg.mpr hca),abs_of_pos (sub_pos.mpr had)] at hcurve
      nlinarith [(abs_le.mp herr).1]
    · rw [abs_of_pos (sub_pos.mpr hac),abs_of_neg (sub_neg.mpr hda)] at hcurve
      nlinarith [(abs_le.mp herr).1]
  · rintro (⟨hca,hda⟩|⟨hac,had⟩)
    · rw [abs_of_neg (sub_neg.mpr hca),abs_of_neg (sub_neg.mpr hda)] at hcurve
      nlinarith [(abs_le.mp herr).2]
    · rw [abs_of_pos (sub_pos.mpr hac),abs_of_pos (sub_pos.mpr had)] at hcurve
      nlinarith [(abs_le.mp herr).2]

/-- Both strict segment tests are checked. The endpoint gap is a product of
actual distances to the parent, so no separation between c and d is needed. -/
theorem nonincident_of_close (r : Point) (a c d t delta : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (ht : |t| ≤ 1)
    (hdelta : 0 < delta)
    (hx : |r.1-(original a).1| ≤ delta) (hy : |r.2-(original a).2| ≤ delta)
    (hcurve : 200*delta < |c-a| * |d-a|) :
    ¬ProperCross r (frame t) (original c) (original d) ∧
    orient (frame t) (original c) r ≠ 0 ∧
    orient (frame t) (original d) r ≠ 0 ∧
    (orient (original c) (original d) r ≠ 0 ∨ original c=original d) := by
  have hs := curvature_ray_separation a c d delta ha hc hd hdelta hcurve
  have hsc := ray_sign_of_close r a c t delta ha hc ht hdelta hx hy hs.1
  have hsd := ray_sign_of_close r a d t delta ha hd ht hdelta hx hy hs.2
  have hca : c ≠ a := by intro he; simp only [he,sub_self,abs_zero] at hs; linarith [hs.1]
  have hda : d ≠ a := by intro he; simp only [he,sub_self,abs_zero] at hs; linarith [hs.2]
  have hm := chord_offset_signs r a c d delta hc hd hx hy hcurve
  have hfan (e : ℚ) (he : e ≠ a)
      (hsgn : (0 < orient r (original e) (frame t) ↔ e < a) ∧
        (orient r (original e) (frame t) < 0 ↔ a < e)) :
      orient (frame t) (original e) r ≠ 0 := by
    rw [orient_cycle,orient_cycle,orient_reverse_last]
    apply neg_ne_zero.mpr
    rcases lt_or_gt_of_ne he with h|h
    · exact ne_of_gt (hsgn.1.mpr h)
    · exact ne_of_lt (hsgn.2.mpr h)
  have hmne : r.1-chordX c d r.2 ≠ 0 := by
    rcases lt_or_gt_of_ne hca with h|h <;> rcases lt_or_gt_of_ne hda with g|g
    · exact ne_of_lt (hm.2 (Or.inl ⟨h,g⟩))
    · exact ne_of_gt (hm.1 (Or.inl ⟨h,g⟩))
    · exact ne_of_gt (hm.1 (Or.inr ⟨g,h⟩))
    · exact ne_of_lt (hm.2 (Or.inr ⟨h,g⟩))
  refine ⟨?_,hfan c hca hsc,hfan d hda hsd,?_⟩
  · have hsame (hside : (c < a ∧ d < a) ∨ (a < c ∧ a < d)) :
        ¬ProperCross r (frame t) (original c) (original d) := by
      intro hh
      have hn := hh.1
      rw [orient_reverse_last r (frame t) (original c),
        orient_reverse_last r (frame t) (original d),neg_mul_neg] at hn
      rcases hside with h|h
      · linarith [mul_pos (hsc.1.mpr h.1) (hsd.1.mpr h.2)]
      · linarith [mul_pos_of_neg_of_neg (hsc.2.mpr h.1) (hsd.2.mpr h.2)]
    have hbetween (hside : (c < a ∧ a < d) ∨ (d < a ∧ a < c)) :
        ¬ProperCross r (frame t) (original c) (original d) := by
      intro hh
      have hn := hh.2
      rw [original_chord_orientation,original_pair_frame] at hn
      have hp := mul_nonneg (mul_nonneg (sq_nonneg (d-c)) (hm.1 hside).le)
        (bridge_positive c d t hc hd).le
      nlinarith
    rcases lt_or_gt_of_ne hca with h|h <;> rcases lt_or_gt_of_ne hda with g|g
    · exact hsame (Or.inl ⟨h,g⟩)
    · exact hbetween (Or.inl ⟨h,g⟩)
    · exact hbetween (Or.inr ⟨g,h⟩)
    · exact hsame (Or.inr ⟨h,g⟩)
  · by_cases he : c=d
    · exact Or.inr (congrArg original he)
    · left
      rw [original_chord_orientation]
      exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm he))) hmne

/-- Actual right-rank coordinates satisfy the same displacement estimate by
reflection of the proved actual left-rank construction. -/
theorem rightRank_displacement (a b tau w mu ell : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) :
    |(rightRank a b tau w mu ell).1-(original b).1| ≤ mu*(b-a) ∧
    |(rightRank a b tau w mu ell).2-(original b).2| ≤ mu*(b-a) := by
  have hspan : -a-(-b)=b-a := by ring
  have hh := leftRank_displacement (-b) (-a) tau w mu (w-2-ell) (by linarith) hw hmu hmuW htau
    (by simpa only [hspan] using htauMu) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [←rightRank_reflection a b tau w mu ell hw,←reflect_original,hspan] at hh
  simpa only [reflect,neg_sub_neg,abs_sub_comm] using hh

/-- Actual left-rank certificate for every nonparent core edge. -/
theorem leftRank_nonincident (a b tau w mu ell c d t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (ht : |t| ≤ 1)
    (hcurve : 200*mu*(b-a) < |c-a| * |d-a|) :
    ¬ProperCross (leftRank a b tau w mu ell) (frame t) (original c) (original d) ∧
    orient (frame t) (original c) (leftRank a b tau w mu ell) ≠ 0 ∧
    orient (frame t) (original d) (leftRank a b tau w mu ell) ≠ 0 ∧
    (orient (original c) (original d) (leftRank a b tau w mu ell) ≠ 0 ∨ original c=original d) := by
  have hh := leftRank_displacement a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  exact nonincident_of_close _ a c d t (mu*(b-a))
    (abs_le.mpr ⟨by linarith,by linarith⟩) hc hd ht (mul_pos hmu (sub_pos.mpr hab))
    hh.1 hh.2 (by nlinarith)

/-- The common placement radius preserves the actual left-rank exclusion. -/
theorem placed_leftRank_nonincident (M : ℕ) (B R : Finset Point)
    (a b tau w mu ell c d t : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (ht : |t| ≤ 1)
    (hcurve : 200*mu*(b-a) < |c-a| * |d-a|)
    (hframe : frame t ∈ B) (hcoreC : original c ∈ B) (hcoreD : original d ∈ B)
    (hr : leftRank a b tau w mu ell ∈ R) (hproto : ∀ r ∈ R, phi r < 0 ∧ |r.2| < 2)
    (hp : Placed M (constructionRadius B R) (leftRank a b tau w mu ell) p) :
    ¬ProperCross p (frame t) (original c) (original d) := by
  have hdelta := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hdelta _ p hp
  have hnz := leftRank_nonincident a b tau w mu ell c d t hab hw hmu hmuW htau htauMu
    hboxA hboxB hell hell1 hc hd ht hcurve
  have he := one_program_crossing_preserved B R _ _ _ _ p hframe hcoreC hcoreD hr
    (Or.inl hnz.2.1) (Or.inl hnz.2.2.1) hnz.2.2.2 _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  exact fun hx => hnz.1 (he.mp hx)

/-- Actual right-rank certificate for every nonparent core edge. -/
theorem rightRank_nonincident (a b tau w mu ell c d t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (ht : |t| ≤ 1)
    (hcurve : 200*mu*(b-a) < |c-b| * |d-b|) :
    ¬ProperCross (rightRank a b tau w mu ell) (frame t) (original c) (original d) ∧
    orient (frame t) (original c) (rightRank a b tau w mu ell) ≠ 0 ∧
    orient (frame t) (original d) (rightRank a b tau w mu ell) ≠ 0 ∧
    (orient (original c) (original d) (rightRank a b tau w mu ell) ≠ 0 ∨ original c=original d) := by
  have hh := rightRank_displacement a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  exact nonincident_of_close _ b c d t (mu*(b-a))
    (abs_le.mpr ⟨by linarith,by linarith⟩) hc hd ht (mul_pos hmu (sub_pos.mpr hab))
    hh.1 hh.2 (by nlinarith)

/-- The common placement radius preserves the actual right-rank exclusion. -/
theorem placed_rightRank_nonincident (M : ℕ) (B R : Finset Point)
    (a b tau w mu ell c d t : ℚ) (p : Point)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (ht : |t| ≤ 1)
    (hcurve : 200*mu*(b-a) < |c-b| * |d-b|)
    (hframe : frame t ∈ B) (hcoreC : original c ∈ B) (hcoreD : original d ∈ B)
    (hr : rightRank a b tau w mu ell ∈ R) (hproto : ∀ r ∈ R, phi r < 0 ∧ |r.2| < 2)
    (hp : Placed M (constructionRadius B R) (rightRank a b tau w mu ell) p) :
    ¬ProperCross p (frame t) (original c) (original d) := by
  have hdelta := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hdelta _ p hp
  have hnz := rightRank_nonincident a b tau w mu ell c d t hab hw hmu hmuW htau htauMu
    hboxA hboxB hell hell1 hc hd ht hcurve
  have he := one_program_crossing_preserved B R _ _ _ _ p hframe hcoreC hcoreD hr
    (Or.inl hnz.2.1) (Or.inl hnz.2.2.1) hnz.2.2.2 _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  exact fun hx => hnz.1 (he.mp hx)

/-- One macro product bound implies every actual rank curvature bound,
including same-other-block core endpoints. -/
theorem rank_curvature_from_macro_boxes (a c d macroC macroD eta delta : ℚ)
    (heta : 0 < eta) (hm : 800*delta < eta^2)
    (hC : eta ≤ |macroC-a|) (hD : eta ≤ |macroD-a|)
    (hc : |c-macroC| ≤ eta/2) (hd : |d-macroD| ≤ eta/2) :
    200*delta < |c-a| * |d-a| := by
  have hca := clone_macro_distance a c macroC eta hC hc
  have hda := clone_macro_distance a d macroD eta hD hd
  have hp := mul_le_mul hca hda (by linarith : (0:ℚ) ≤ eta/2) (abs_nonneg _)
  nlinarith

end Q4.Candidate.RankNonincident

#print axioms Q4.Candidate.RankNonincident.chord_offset_change
#print axioms Q4.Candidate.RankNonincident.nonincident_of_close
#print axioms Q4.Candidate.RankNonincident.rightRank_displacement
#print axioms Q4.Candidate.RankNonincident.leftRank_nonincident
#print axioms Q4.Candidate.RankNonincident.rightRank_nonincident
#print axioms Q4.Candidate.RankNonincident.placed_leftRank_nonincident
#print axioms Q4.Candidate.RankNonincident.placed_rightRank_nonincident
#print axioms Q4.Candidate.RankNonincident.rank_curvature_from_macro_boxes
