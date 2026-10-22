import Q4.Candidate.OrdinaryFan
import Q4.Candidate.OrientationPreservation

/-! Actual ordinary fan versus every nonparent core edge. The displacement
is controlled by the quadratic curvature margin between the parent and both
actual endpoints, including short edges within one nonparent clone block. -/
namespace Q4.Candidate.OrdinaryNonincident
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.OrdinaryFan Q4.Candidate.OrientationPreservation
open Q4.Candidate.UniformInsertion

def displacementCoefficient (a c d : ℚ) : ℚ := 11+(a^2-a*c-a*d)/100

theorem displacementCoefficient_bounds (a c d : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) :
    10 ≤ displacementCoefficient a c d ∧ displacementCoefficient a c d ≤ 12 := by
  have ha2 := unit_square_bound a (abs_le.mp ha).1 (abs_le.mp ha).2
  have hac : |a*c| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul ha hc (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 1)
  have had : |a*d| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul ha hd (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 1)
  unfold displacementCoefficient
  constructor <;> nlinarith [(abs_le.mp hac).1,(abs_le.mp hac).2,
    (abs_le.mp had).1,(abs_le.mp had).2,sq_nonneg a]

theorem ordinary_chord_difference (a c d mu : ℚ) :
    (ordinary a mu).1-chordX c d (ordinary a mu).2 =
      -(a-c)*(a-d)/100-mu*displacementCoefficient a c d := by
  unfold ordinary mix original frame chordX displacementCoefficient
  ring

theorem chordX_comm (c d y : ℚ) : chordX c d y = chordX d c y := by
  unfold chordX
  ring

/-- The curvature bound automatically pays for both linear ray-separation bounds. -/
theorem curvature_implies_separation (a c d mu : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hm : 0 < mu)
    (hcurve : 1200*mu < |c-a| * |d-a|) :
    5*mu ≤ |c-a| ∧ 5*mu ≤ |d-a| := by
  have hc2 : |c-a| ≤ 2 := (abs_sub c a).trans (by linarith)
  have hd2 : |d-a| ≤ 2 := (abs_sub d a).trans (by linarith)
  have hp0 := mul_le_mul_of_nonneg_left hd2 (abs_nonneg (c-a))
  have hp1 := mul_le_mul_of_nonneg_right hc2 (abs_nonneg (d-a))
  constructor <;> nlinarith

/-- For a parent between the actual core endpoints, the ordinary point remains
strictly on the frame side of their chord; the quadratic gap is not discarded. -/
theorem chord_margin_between (a c d mu : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hm : 0 < mu)
    (hcurve : 1200*mu < |c-a| * |d-a|) (hca : c < a) (had : a < d) :
    0 < (ordinary a mu).1-chordX c d (ordinary a mu).2 := by
  have hcoef := (displacementCoefficient_bounds a c d ha hc hd).2
  have hmul := mul_le_mul_of_nonneg_left hcoef hm.le
  rw [abs_of_neg (sub_neg.mpr hca),abs_of_pos (sub_pos.mpr had)] at hcurve
  rw [ordinary_chord_difference]
  nlinarith

/-- For a parent outside the core parameter interval, its ordinary point is
strictly on the opposite side of the chord's supporting line from the frame. -/
theorem chord_margin_outside (a c d mu : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hm : 0 < mu)
    (hside : (c < a ∧ d < a) ∨ (a < c ∧ a < d)) :
    (ordinary a mu).1-chordX c d (ordinary a mu).2 < 0 := by
  have hcoef := (displacementCoefficient_bounds a c d ha hc hd).1
  have hmul := mul_pos hm (show 0 < displacementCoefficient a c d by linarith)
  have hprod : 0 < (a-c)*(a-d) := by
    rcases hside with h|h
    · exact mul_pos (sub_pos.mpr h.1) (sub_pos.mpr h.2)
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr h.1) (sub_neg.mpr h.2)
  rw [ordinary_chord_difference]
  nlinarith

theorem chord_margin_nonzero (a c d mu : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hm : 0 < mu)
    (hcurve : 1200*mu < |c-a| * |d-a|) :
    (ordinary a mu).1-chordX c d (ordinary a mu).2 ≠ 0 := by
  have hs := curvature_implies_separation a c d mu ha hc hd hm hcurve
  have hca : c ≠ a := by intro he; simp only [he,sub_self,abs_zero] at hs; linarith [hs.1]
  have hda : d ≠ a := by intro he; simp only [he,sub_self,abs_zero] at hs; linarith [hs.2]
  rcases lt_or_gt_of_ne hca with hca|hac <;> rcases lt_or_gt_of_ne hda with hda|had
  · exact ne_of_lt (chord_margin_outside a c d mu ha hc hd hm (Or.inl ⟨hca,hda⟩))
  · exact ne_of_gt (chord_margin_between a c d mu ha hc hd hm hcurve hca had)
  · have he := chord_margin_between a d c mu ha hd hc hm (by simpa [mul_comm] using hcurve) hda hac
    simpa only [chordX_comm d c] using ne_of_gt he
  · exact ne_of_lt (chord_margin_outside a c d mu ha hc hd hm (Or.inr ⟨hac,had⟩))

/-- Every actual nonparent core edge is excluded. This includes two distinct
clones from the same nonparent macro block and does not use a collapsed chord. -/
theorem ordinary_nonincident_no_cross (a c d mu t : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (ht : |t| ≤ 1) (hm : 0 < mu)
    (hcurve : 1200*mu < |c-a| * |d-a|) :
    ¬ProperCross (ordinary a mu) (frame t) (original c) (original d) := by
  have hs := curvature_implies_separation a c d mu ha hc hd hm hcurve
  have hsc := ordinary_nonparent_sign a c mu t ha hc ht hm hs.1
  have hsd := ordinary_nonparent_sign a d mu t ha hd ht hm hs.2
  have hca : c ≠ a := by intro he; simp only [he,sub_self,abs_zero] at hs; linarith [hs.1]
  have hda : d ≠ a := by intro he; simp only [he,sub_self,abs_zero] at hs; linarith [hs.2]
  have hsame (hside : (c < a ∧ d < a) ∨ (a < c ∧ a < d)) :
      ¬ProperCross (ordinary a mu) (frame t) (original c) (original d) := by
    intro hcross
    have hneg := hcross.1
    rw [orient_reverse_last (ordinary a mu) (frame t) (original c),
      orient_reverse_last (ordinary a mu) (frame t) (original d),neg_mul_neg] at hneg
    rcases hside with h|h
    · have hp := mul_pos (hsc.1.mpr h.1) (hsd.1.mpr h.2)
      linarith
    · have hp := mul_pos_of_neg_of_neg (hsc.2.mpr h.1) (hsd.2.mpr h.2)
      linarith
  have hbetween (hca : c < a) (had : a < d) :
      ¬ProperCross (ordinary a mu) (frame t) (original c) (original d) := by
    have hmargin := chord_margin_between a c d mu ha hc hd hm hcurve hca had
    have hbri := bridge_positive c d t hc hd
    have hprod : 0 ≤ orient (original c) (original d) (ordinary a mu)*
        orient (original c) (original d) (frame t) := by
      rw [original_chord_orientation,original_pair_frame]
      have hp := mul_nonneg (mul_nonneg (sq_nonneg (d-c)) hmargin.le) hbri.le
      nlinarith
    exact fun hx => not_lt_of_ge hprod hx.2
  rcases lt_or_gt_of_ne hca with hca|hac <;> rcases lt_or_gt_of_ne hda with hda|had
  · exact hsame (Or.inl ⟨hca,hda⟩)
  · exact hbetween hca had
  · intro hx
    have hmargin := chord_margin_between a d c mu ha hd hc hm (by simpa [mul_comm] using hcurve) hda hac
    have hbri := bridge_positive c d t hc hd
    rw [chordX_comm d c] at hmargin
    have hneg := hx.2
    rw [original_chord_orientation,original_pair_frame] at hneg
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (d-c)) hmargin.le) hbri.le]
  · exact hsame (Or.inr ⟨hac,had⟩)


/-- All moving determinants are strictly nonzero, except the identically zero
core determinant of a repeated fixed endpoint, which is explicitly separated. -/
theorem ordinary_nonincident_determinants (a c d mu t : ℚ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (ht : |t| ≤ 1) (hm : 0 < mu)
    (hcurve : 1200*mu < |c-a| * |d-a|) :
    orient (frame t) (original c) (ordinary a mu) ≠ 0 ∧
    orient (frame t) (original d) (ordinary a mu) ≠ 0 ∧
    (orient (original c) (original d) (ordinary a mu) ≠ 0 ∨ original c=original d) := by
  have hs := curvature_implies_separation a c d mu ha hc hd hm hcurve
  have hfan (e : ℚ) (he : |e| ≤ 1) (hsep : 5*mu ≤ |e-a|) :
      orient (frame t) (original e) (ordinary a mu) ≠ 0 := by
    have heq : e ≠ a := by intro hh; simp only [hh,sub_self,abs_zero] at hsep; linarith
    have hsign := ordinary_nonparent_sign a e mu t ha he ht hm hsep
    have hnz : orient (ordinary a mu) (original e) (frame t) ≠ 0 := by
      rcases lt_or_gt_of_ne heq with h|h
      · exact ne_of_gt (hsign.1.mpr h)
      · exact ne_of_lt (hsign.2.mpr h)
    rw [orient_cycle,orient_cycle,orient_reverse_last]
    exact neg_ne_zero.mpr hnz
  refine ⟨hfan c hc hs.1,hfan d hd hs.2,?_⟩
  by_cases he : c=d
  · exact Or.inr (congrArg original he)
  · left
    rw [original_chord_orientation]
    exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm he)))
      (chord_margin_nonzero a c d mu ha hc hd hm hcurve)

/-- The actual final general-position copy preserves the no-crossing table
under precisely the same common radius used for all other one-program tables. -/
theorem placed_ordinary_nonincident_no_cross (M : ℕ) (B R : Finset Point)
    (a c d mu t : ℚ) (p : Point)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (ht : |t| ≤ 1) (hm : 0 < mu)
    (hcurve : 1200*mu < |c-a| * |d-a|)
    (hframe : frame t ∈ B) (hcoreC : original c ∈ B) (hcoreD : original d ∈ B)
    (hr : ordinary a mu ∈ R) (hproto : ∀ r ∈ R, phi r < 0 ∧ |r.2| < 2)
    (hp : Placed M (constructionRadius B R) (ordinary a mu) p) :
    ¬ProperCross p (frame t) (original c) (original d) := by
  have hdelta := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hdelta _ p hp
  have hnz := ordinary_nonincident_determinants a c d mu t ha hc hd ht hm hcurve
  have he := one_program_crossing_preserved B R _ _ _ _ p hframe hcoreC hcoreD hr
    (Or.inl hnz.1) (Or.inl hnz.2.1) hnz.2.2 _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  exact fun hx => ordinary_nonincident_no_cross a c d mu t ha hc hd ht hm hcurve (he.mp hx)

/-- Distances from a different macro are preserved uniformly in its clone box. -/
theorem clone_macro_distance (a c center eta : ℚ)
    (hmacro : eta ≤ |center-a|) (hclone : |c-center| ≤ eta/2) :
    eta/2 ≤ |c-a| := by
  have hh := abs_sub_le center c a
  rw [abs_sub_comm center c] at hh
  linarith

/-- One quadratic macro-margin condition suffices for every actual pair of
nonparent clones, including two clones belonging to the same other macro. -/
theorem curvature_from_macro_boxes (a c d macroC macroD eta mu : ℚ)
    (heta : 0 < eta) (hm : 4800*mu < eta^2)
    (hC : eta ≤ |macroC-a|) (hD : eta ≤ |macroD-a|)
    (hc : |c-macroC| ≤ eta/2) (hd : |d-macroD| ≤ eta/2) :
    1200*mu < |c-a| * |d-a| := by
  have hca := clone_macro_distance a c macroC eta hC hc
  have hda := clone_macro_distance a d macroD eta hD hd
  have hprod := mul_le_mul hca hda (by linarith : (0:ℚ) ≤ eta/2) (abs_nonneg _)
  nlinarith

def macroMargins (A : Finset ℚ) : Finset ℚ :=
  insert 1 (((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => |p.1-p.2|))
def macroSpacing (A : Finset ℚ) : ℚ := (macroMargins A).min' (Finset.insert_nonempty _ _)

theorem macroSpacing_positive (A : Finset ℚ) : 0 < macroSpacing A := by
  have hm := Finset.min'_mem (macroMargins A) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with hm|hm
  · change 0 < macroSpacing A
    unfold macroSpacing
    rw [hm]
    norm_num
  · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
    unfold macroSpacing
    rw [←he]
    exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)

theorem macroSpacing_le_one (A : Finset ℚ) : macroSpacing A ≤ 1 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem macroSpacing_le (A : Finset ℚ) (a c : ℚ) (ha : a ∈ A) (hc : c ∈ A) (hne : c ≠ a) :
    macroSpacing A ≤ |c-a| := by
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(c,a),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc,ha⟩,hne⟩,rfl⟩

/-- Concrete positive rational ordinary scales for a finite macro family and
any frame count. They jointly pay for the nonincident curvature gap and the
ordinary parent-clone ray margins. This is existence, not a bit-size bound. -/
theorem simultaneous_scales (A : Finset ℚ) (B : ℕ) :
    ∃ mu tau : ℚ, 0 < mu ∧ mu ≤ 1 ∧ 0 < tau ∧ tau ≤ macroSpacing A ∧
      4800*mu < (macroSpacing A)^2 ∧ 3*((B:ℚ)+1)*(tau/2) ≤ mu := by
  let eta := macroSpacing A
  let mu := eta^2/9600
  let tau := min eta (mu/(3*((B:ℚ)+1)))
  have heta : 0 < eta := macroSpacing_positive A
  have heta1 : eta ≤ 1 := macroSpacing_le_one A
  have hmu : 0 < mu := by dsimp [mu]; positivity
  have hden : 0 < 3*((B:ℚ)+1) := by positivity
  have htau : 0 < tau := lt_min heta (div_pos hmu hden)
  refine ⟨mu,tau,hmu,?_,htau,min_le_left _ _,?_,?_⟩
  · dsimp [mu]
    nlinarith [mul_nonneg heta.le (sub_nonneg.mpr heta1)]
  · change 4800*(eta^2/9600) < eta^2
    nlinarith [sq_pos_of_pos heta]
  · have hh : tau ≤ mu/(3*((B:ℚ)+1)) := min_le_right _ _
    have hm := (le_div_iff₀ hden).mp hh
    nlinarith

end Q4.Candidate.OrdinaryNonincident

#print axioms Q4.Candidate.OrdinaryNonincident.chord_margin_between
#print axioms Q4.Candidate.OrdinaryNonincident.chord_margin_nonzero
#print axioms Q4.Candidate.OrdinaryNonincident.ordinary_nonincident_no_cross
#print axioms Q4.Candidate.OrdinaryNonincident.ordinary_nonincident_determinants
#print axioms Q4.Candidate.OrdinaryNonincident.placed_ordinary_nonincident_no_cross
#print axioms Q4.Candidate.OrdinaryNonincident.curvature_from_macro_boxes
#print axioms Q4.Candidate.OrdinaryNonincident.simultaneous_scales
