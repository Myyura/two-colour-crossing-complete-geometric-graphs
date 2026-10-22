import Q4.Candidate.RankGapPreservation
import Q4.Candidate.OrdinaryNonincident

namespace Q4.Candidate.RankNonselected
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.RankGap Q4.Candidate.RankGapPreservation
open Q4.Candidate.OrdinaryFan Q4.Candidate.OrdinaryNonincident

/-- Actual chord perturbation, uniform throughout the unit parameter box. -/
theorem chord_parameter_perturbation (a b c d y tau : ℚ)
    (_ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (hy : |y| ≤ 1)
    (hca : |c-a| ≤ tau/2) (hdb : |d-b| ≤ tau/2) :
    |chordX c d y-chordX a b y| ≤ tau/50 := by
  have hyb : |y-b| ≤ 2 := (abs_sub y b).trans (by linarith)
  have hyc : |y-c| ≤ 2 := (abs_sub y c).trans (by linarith)
  have hprod1 : |(c-a)*(y-b)| ≤ tau := by
    rw [abs_mul]
    nlinarith [mul_le_mul hca hyb (abs_nonneg _) (by linarith [abs_nonneg (c-a)] : 0 ≤ tau/2)]
  have hprod2 : |(d-b)*(y-c)| ≤ tau := by
    rw [abs_mul]
    nlinarith [mul_le_mul hdb hyc (abs_nonneg _) (by linarith [abs_nonneg (d-b)] : 0 ≤ tau/2)]
  have he : chordX c d y-chordX a b y = -((c-a)*(y-b)+(d-b)*(y-c))/100 := by
    unfold chordX
    ring
  rw [he,abs_div,abs_neg]
  norm_num
  nlinarith [abs_add_le ((c-a)*(y-b)) ((d-b)*(y-c))]

theorem clone_macro_near (a tau w s : ℚ) (htau : 0 ≤ tau) (hw : 2 ≤ w)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) : |cloneAt a tau w s-a| ≤ tau/2 := by
  have hb := clone_bounds a tau w s htau hw hs hs1
  exact abs_le.mpr ⟨by linarith [hb.1],by linarith [hb.2]⟩

/-- Actual left rank steering is at most tau/50 from its unsteered chord
center, simultaneously for all allowed internal gaps. -/
theorem leftRank_steering_bound (a b tau w mu ell : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) :
    |(leftRank a b tau w mu ell).1-chordX a b (leftHeight a b mu)| ≤ tau/50 := by
  have ha : |a| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hb : |b| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hmu1 := (scale_bounds (b-a) tau w mu (sub_pos.mpr hab) hw hmu hmuW htau htauMu).1
  have hprod := mul_le_mul_of_nonneg_right hmu1 (sub_pos.mpr hab).le
  have hy : |leftHeight a b mu| ≤ 1 := by
    unfold leftHeight
    apply abs_le.mpr
    constructor <;> nlinarith [(abs_le.mp ha).1,(abs_le.mp hb).2,mul_pos hmu (sub_pos.mpr hab)]
  have hlo := clones_in_unit a b tau w ell hab.le htau.le hw hboxA hboxB hell (by linarith)
  have hhi := clones_in_unit a b tau w (ell+1) hab.le htau.le hw hboxA hboxB (by linarith) hell1
  have hleft := chord_parameter_perturbation a b (cloneAt a tau w ell) (cloneAt b tau w 0)
    (leftHeight a b mu) tau ha hb hlo.1 hy
    (clone_macro_near a tau w ell htau.le hw hell (by linarith))
    (clone_macro_near b tau w 0 htau.le hw (by rfl) (by linarith))
  have hright := chord_parameter_perturbation a b (cloneAt a tau w (ell+1)) (cloneAt b tau w (w-1))
    (leftHeight a b mu) tau ha hb hhi.1 hy
    (clone_macro_near a tau w (ell+1) htau.le hw (by linarith) hell1)
    (clone_macro_near b tau w (w-1) htau.le hw (by linarith) (by rfl))
  dsimp [leftRank,gapLowerX,gapUpperX]
  have hsum := abs_add_le
    (chordX (cloneAt a tau w ell) (cloneAt b tau w 0) (leftHeight a b mu)-chordX a b (leftHeight a b mu))
    (chordX (cloneAt a tau w (ell+1)) (cloneAt b tau w (w-1)) (leftHeight a b mu)-chordX a b (leftHeight a b mu))
  rw [show (chordX (cloneAt a tau w ell) (cloneAt b tau w 0) (leftHeight a b mu)+
      chordX (cloneAt a tau w (ell+1)) (cloneAt b tau w (w-1)) (leftHeight a b mu))/2-
      chordX a b (leftHeight a b mu) =
      ((chordX (cloneAt a tau w ell) (cloneAt b tau w 0) (leftHeight a b mu)-chordX a b (leftHeight a b mu))+
      (chordX (cloneAt a tau w (ell+1)) (cloneAt b tau w (w-1)) (leftHeight a b mu)-chordX a b (leftHeight a b mu)))/2 by ring,
    abs_div]
  norm_num
  linarith


/-- Both actual coordinates of the steered rank point remain within the
vertical macro displacement of the parent. -/
theorem leftRank_displacement (a b tau w mu ell : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) :
    |(leftRank a b tau w mu ell).1-(original a).1| ≤ mu*(b-a) ∧
    |(leftRank a b tau w mu ell).2-(original a).2| ≤ mu*(b-a) := by
  have ha : |a| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hb : |b| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hdelta := mul_pos hmu (sub_pos.mpr hab)
  have hsteer := leftRank_steering_bound a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hbase : |chordX a b (leftHeight a b mu)-(original a).1| ≤ mu*(b-a)/50 := by
    have he : chordX a b (leftHeight a b mu)-(original a).1 = -(a+b)*(mu*(b-a))/100 := by
      unfold chordX leftHeight original
      ring
    rw [he,abs_div,abs_mul,abs_neg,abs_of_pos hdelta]
    norm_num
    have habs : |a+b| ≤ 2 := (abs_add_le a b).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right habs hdelta.le]
  constructor
  · have hh := abs_sub_le (leftRank a b tau w mu ell).1 (chordX a b (leftHeight a b mu)) (original a).1
    linarith
  · change |a+mu*(b-a)-a| ≤ mu*(b-a)
    simp only [add_sub_cancel_left,abs_of_pos hdelta]
    exact le_rfl

/-- A nonparent fan-ray determinant keeps its exact macro sign under a
coordinate displacement bounded by delta and an explicit actual separation. -/
theorem ray_sign_of_close (r : Point) (a z t delta : ℚ)
    (ha : |a| ≤ 1) (hz : |z| ≤ 1) (ht : |t| ≤ 1) (hd : 0 < delta)
    (hx : |r.1-(original a).1| ≤ delta) (hy : |r.2-(original a).2| ≤ delta)
    (hsep : 2*delta ≤ |z-a|) :
    (0 < orient r (original z) (frame t) ↔ z < a) ∧
    (orient r (original z) (frame t) < 0 ↔ a < z) := by
  have hchange := Q4.Candidate.OrientationPreservation.orient_change_bound
    (original z) (frame t) (original a) r delta hx hy
  have hxb := cap_frame_x_bound z t hz ht
  have hyb : |(frame t).2-(original z).2| ≤ 2 := by
    change |t-z| ≤ 2
    exact (abs_sub t z).trans (by linarith)
  have herr : |orient r (original z) (frame t)-orient (original a) (original z) (frame t)| ≤ 14*delta := by
    rw [orient_cycle r,orient_cycle (original a)]
    nlinarith [mul_le_mul_of_nonneg_right (show |(frame t).1-(original z).1|+
      |(frame t).2-(original z).2| ≤ 14 by linarith) hd.le]
  have hbase := original_pair_frame a z t
  have hbri := bridge_lower a z t ha hz
  have hne : z ≠ a := by intro he; simp only [he,sub_self,abs_zero] at hsep; linarith
  rcases lt_or_gt_of_ne hne with hza|haz
  · rw [abs_of_neg (sub_neg.mpr hza)] at hsep
    have hp := mul_le_mul_of_nonneg_left hbri (by linarith : 0 ≤ a-z)
    have hs : 0 < orient r (original z) (frame t) := by
      nlinarith [(abs_le.mp herr).1,(abs_le.mp herr).2]
    exact ⟨by constructor <;> intro _ <;> assumption,by constructor <;> intro h <;> linarith⟩
  · rw [abs_of_pos (sub_pos.mpr haz)] at hsep
    have hp := mul_le_mul_of_nonneg_left hbri (by linarith : 0 ≤ z-a)
    have hs : orient r (original z) (frame t) < 0 := by
      nlinarith [(abs_le.mp herr).1,(abs_le.mp herr).2]
    exact ⟨by constructor <;> intro h <;> linarith,by constructor <;> intro _ <;> assumption⟩

theorem leftRank_nonparent_ray_sign (a b tau w mu ell z t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) (hz : |z| ≤ 1) (ht : |t| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-a|) :
    (0 < orient (leftRank a b tau w mu ell) (original z) (frame t) ↔ z < a) ∧
    (orient (leftRank a b tau w mu ell) (original z) (frame t) < 0 ↔ a < z) := by
  have hdisp := leftRank_displacement a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  exact ray_sign_of_close _ a z t (mu*(b-a)) (abs_le.mpr ⟨by linarith,by linarith⟩)
    hz ht (mul_pos hmu (sub_pos.mpr hab)) hdisp.1 hdisp.2 (by nlinarith)


/-- Quantitative supporting-line signs for the actual parent clone. The
nonselected partner gap pays for both horizontal steering and cloning. -/
theorem support_signs_of_steering (r : Point) (a b c z mu tau : ℚ)
    (hz : |z| ≤ 1) (hy : |r.2| ≤ 1) (htau : 0 < tau)
    (hheight : r.2 = a+mu*(b-a))
    (hsteer : |r.1-chordX a b r.2| ≤ tau/50)
    (hclone : |c-a| ≤ tau/2) (hgap : 20*tau ≤ mu*(b-a)*|b-z|) :
    ((r.1-chordX c z r.2 < 0) ↔ z < b) ∧
    ((0 < r.1-chordX c z r.2) ↔ b < z) := by
  have hyz : |r.2-z| ≤ 2 := (abs_sub r.2 z).trans (by linarith)
  have hcloneErr : |(c-a)*(r.2-z)/100| ≤ tau/100 := by
    rw [abs_div,abs_mul]
    norm_num
    nlinarith [mul_le_mul hclone hyz (abs_nonneg _) (by linarith : (0:ℚ) ≤ tau/2)]
  have he : r.1-chordX c z r.2+mu*(b-a)*(b-z)/100 =
      (r.1-chordX a b r.2)+(c-a)*(r.2-z)/100 := by
    rw [hheight]
    unfold chordX
    ring
  have herr : |r.1-chordX c z r.2+mu*(b-a)*(b-z)/100| ≤ 3*tau/100 := by
    rw [he]
    have hh := abs_add_le (r.1-chordX a b r.2) ((c-a)*(r.2-z)/100)
    linarith
  have hne : b ≠ z := by
    intro hz
    rw [hz,sub_self,abs_zero,mul_zero] at hgap
    linarith
  rcases lt_or_gt_of_ne hne with hbz|hzb
  · rw [abs_of_neg (sub_neg.mpr hbz)] at hgap
    have hsign : 0 < r.1-chordX c z r.2 := by nlinarith [(abs_le.mp herr).1]
    exact ⟨by constructor <;> intro h <;> linarith,by constructor <;> intro _ <;> assumption⟩
  · rw [abs_of_pos (sub_pos.mpr hzb)] at hgap
    have hsign : r.1-chordX c z r.2 < 0 := by nlinarith [(abs_le.mp herr).2]
    exact ⟨by constructor <;> intro _ <;> assumption,by constructor <;> intro h <;> linarith⟩

/-- Both strict segment endpoint tests, specialized to the already proved
parent ray and the actual supporting-line gap. -/
theorem core_crossing_test (r : Point) (a b c z t : ℚ)
    (hc : |c| ≤ 1) (hz : |z| ≤ 1) (hne : c ≠ z)
    (hparent : orient r (frame t) (original c) < 0)
    (hother : 0 < orient r (frame t) (original z) ↔ a < z)
    (hsupport : r.1-chordX c z r.2 < 0 ↔ z < b) :
    ProperCross r (frame t) (original c) (original z) ↔ a < z ∧ z < b := by
  have hbridge := bridge_positive c z t hc hz
  have hpos : 0 < (z-c)^2*bridge c z t :=
    mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hne))) hbridge
  have hfirst : orient r (frame t) (original c)*orient r (frame t) (original z) < 0 ↔
      0 < orient r (frame t) (original z) := by
    rw [mul_neg_iff]
    constructor
    · rintro (⟨h,_⟩|⟨_,h⟩)
      · linarith
      · exact h
    · intro h; exact Or.inr ⟨hparent,h⟩
  have hsecond : orient (original c) (original z) r*orient (original c) (original z) (frame t) < 0 ↔
      r.1-chordX c z r.2 < 0 := by
    rw [original_chord_orientation,original_pair_frame]
    have he : (-(z-c)*(r.1-chordX c z r.2))*(-(z-c)*bridge c z t) =
        ((z-c)^2*bridge c z t)*(r.1-chordX c z r.2) := by ring
    rw [he]
    simpa only [mul_zero] using (mul_lt_mul_iff_of_pos_left hpos :
      ((z-c)^2*bridge c z t)*(r.1-chordX c z r.2) < ((z-c)^2*bridge c z t)*0 ↔ _)
  exact (and_congr hfirst hsecond).trans (and_congr hother hsupport)

/-- The actual left rank prototype has the claimed all-frame/zero-frame table
for every nonselected incident core edge, including an actual parent clone.
The partner exclusion is quantitative rather than an assumed determinant sign. -/
theorem leftRank_nonselected_core (a b tau w mu ell s z t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (hz : |z| ≤ 1) (ht : |t| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-a|) (hgap : 20*tau ≤ mu*(b-a)*|b-z|) :
    ProperCross (leftRank a b tau w mu ell) (frame t)
      (original (cloneAt a tau w s)) (original z) ↔ a < z ∧ z < b := by
  have hunit := clones_in_unit a b tau w s hab.le htau.le hw hboxA hboxB hs hs1
  have hnear := clone_macro_near a tau w s htau.le hw hs hs1
  have hparent := (leftRank_endpoint_sides a b tau w mu ell s 0 t hab hw hmu hmuW
    htau htauMu hboxA hboxB ht hell hell1 hs hs1 (by rfl) (by linarith)).1
  have hotherSign := leftRank_nonparent_ray_sign a b tau w mu ell z t hab hw hmu hmuW
    htau htauMu hboxA hboxB hell hell1 hz ht hsep
  have hother : 0 < orient (leftRank a b tau w mu ell) (frame t) (original z) ↔ a < z := by
    rw [orient_reverse_last,neg_pos]
    exact hotherSign.2
  have hheight := height_between_all_clones a b tau w mu s 0 hab hw hmu hmuW htau htauMu hs hs1 (by rfl) (by linarith)
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
  exact core_crossing_test _ a b _ z t hunit.1 hz hne hparent hother hsupport.1


theorem clone_reverse (a tau w s : ℚ) (hw : 2 ≤ w) :
    cloneAt (-a) tau w (w-1-s) = -cloneAt a tau w s := by
  unfold cloneAt
  field_simp [show w-1 ≠ 0 by linarith]
  ring

/-- The right-side all/zero table follows by the actual coordinate reflection,
including reversed parent-clone ranks and the same frame point reflected. -/
theorem rightRank_nonselected_core (a b tau w mu ell s z t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (hz : |z| ≤ 1) (ht : |t| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-b|) (hgap : 20*tau ≤ mu*(b-a)*|a-z|) :
    ProperCross (rightRank a b tau w mu ell) (frame t)
      (original (cloneAt b tau w s)) (original z) ↔ a < z ∧ z < b := by
  have hspan : -a-(-b) = b-a := by ring
  have hsep' : 2*mu*(-a-(-b)) ≤ |-z-(-b)| := by
    simpa only [hspan,neg_sub_neg,abs_sub_comm b z] using hsep
  have hgap' : 20*tau ≤ mu*(-a-(-b))*|-a-(-z)| := by
    simpa only [hspan,neg_sub_neg,abs_sub_comm z a] using hgap
  have htbl := leftRank_nonselected_core (-b) (-a) tau w mu (w-2-ell) (w-1-s) (-z) (-t)
    (by linarith) hw hmu hmuW htau (by simpa only [hspan] using htauMu)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by simpa using hz) (by simpa using ht) hsep' hgap'
  rw [clone_reverse b tau w s hw,←rightRank_reflection a b tau w mu ell hw,
    ←reflect_frame,←reflect_original,←reflect_original,properCross_reflect] at htbl
  exact htbl.trans (by constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith)

/-- The actual strict cap and height certificate for every left rank prototype. -/
theorem leftRank_valid (a b tau w mu ell : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) :
    (Vertex.program (leftRank a b tau w mu ell)).valid := by
  have hbt0 := height_between_all_clones a b tau w mu ell 0 hab hw hmu hmuW htau htauMu
    hell (by linarith) (by rfl) (by linarith)
  have hbt1 := height_between_all_clones a b tau w mu (ell+1) (w-1) hab hw hmu hmuW htau htauMu
    (by linarith) hell1 (by linarith) (by rfl)
  have hphi : phi (leftRank a b tau w mu ell) < 0 :=
    rank_midpoint_inside _ _ _ _ _ hbt0.1 hbt0.2 hbt1.1 hbt1.2
  have hl := (clones_in_unit a b tau w ell hab.le htau.le hw hboxA hboxB hell (by linarith)).1
  have hr := (clones_in_unit a b tau w 0 hab.le htau.le hw hboxA hboxB (by rfl) (by linarith)).2
  refine ⟨hphi,?_⟩
  change -2 ≤ leftHeight a b mu ∧ leftHeight a b mu ≤ 2
  constructor <;> linarith [(abs_le.mp hl).1,(abs_le.mp hr).2]

/-- Every entire parent block precedes the left marker: its full parent fan
neighborhood is the row prefix, independently of the steering gap. -/
theorem leftRank_parent_fan_indexed (B : ℕ) (i k : Fin B) (a b tau w mu ell s : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) (hs : 0 ≤ s) (hs1 : s ≤ w-1) :
    ProperCross (leftRank a b tau w mu ell) (frame (frameParameter B k))
      (original (cloneAt a tau w s)) (frame (frameParameter B i)) ↔ i < k := by
  have hr := leftRank_valid a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hpos (j : Fin B) : 0 < orient (leftRank a b tau w mu ell)
      (original (cloneAt a tau w s)) (frame (frameParameter B j)) := by
    have hh := (leftRank_endpoint_sides a b tau w mu ell s 0 (frameParameter B j) hab hw hmu hmuW
      htau htauMu hboxA hboxB (frameParameter_unit B j).le hell hell1 hs hs1 (by rfl) (by linarith)).1
    rw [orient_reverse_last] at hh
    linarith
  rw [fan_crossing_epsilon _ _ _ _ hr (frameParameter_unit B i).le (frameParameter_unit B k).le,
    (frameParameter_antitone B).lt_iff_gt,(frameParameter_antitone B).lt_iff_gt]
  simp only [hpos i,hpos k,and_true,not_lt_of_ge (hpos i).le,
    not_lt_of_ge (hpos k).le,and_false,or_false]

/-- All nonparent originals have the exact virtual macro-column neighborhood,
with all frame rows and all allowed steering gaps covered simultaneously. -/
theorem leftRank_nonparent_fan_indexed (B : ℕ) (i k : Fin B) (a b tau w mu ell z : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) (hz : |z| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-a|) :
    ProperCross (leftRank a b tau w mu ell) (frame (frameParameter B k))
      (original z) (frame (frameParameter B i)) ↔ (i < k ∧ z < a) ∨ (k < i ∧ a < z) := by
  have hr := leftRank_valid a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hs (j : Fin B) := leftRank_nonparent_ray_sign a b tau w mu ell z (frameParameter B j)
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hz (frameParameter_unit B j).le hsep
  rw [fan_crossing_epsilon _ z _ _ hr (frameParameter_unit B i).le (frameParameter_unit B k).le,
    (hs i).1,(hs k).1,(hs i).2,(hs k).2,
    (frameParameter_antitone B).lt_iff_gt,(frameParameter_antitone B).lt_iff_gt]
  tauto


theorem rightRank_valid (a b tau w mu ell : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) :
    (Vertex.program (rightRank a b tau w mu ell)).valid := by
  have hspan : -a-(-b)=b-a := by ring
  have hh := leftRank_valid (-b) (-a) tau w mu (w-2-ell) (by linarith) hw hmu hmuW htau
    (by simpa only [hspan] using htauMu)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [←rightRank_reflection a b tau w mu ell hw] at hh
  change phi (reflect (rightRank a b tau w mu ell)) < 0 ∧
    -2 ≤ -(rightRank a b tau w mu ell).2 ∧ -(rightRank a b tau w mu ell).2 ≤ 2 at hh
  have hphi : phi (reflect (rightRank a b tau w mu ell)) = phi (rightRank a b tau w mu ell) := by
    unfold phi reflect
    ring
  rw [hphi] at hh
  exact ⟨hh.1,by linarith [hh.2.2],by linarith [hh.2.1]⟩

theorem rightRank_nonparent_ray_sign (a b tau w mu ell z t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) (hz : |z| ≤ 1) (ht : |t| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-b|) :
    (0 < orient (rightRank a b tau w mu ell) (original z) (frame t) ↔ z < b) ∧
    (orient (rightRank a b tau w mu ell) (original z) (frame t) < 0 ↔ b < z) := by
  have hspan : -a-(-b)=b-a := by ring
  have hh := leftRank_nonparent_ray_sign (-b) (-a) tau w mu (w-2-ell) (-z) (-t)
    (by linarith) hw hmu hmuW htau (by simpa only [hspan] using htauMu)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by simpa using hz) (by simpa using ht)
    (by simpa only [hspan,neg_sub_neg,abs_sub_comm b z] using hsep)
  rw [←rightRank_reflection a b tau w mu ell hw,←reflect_original,←reflect_frame] at hh
  simp only [orient_reflect,neg_pos,neg_lt_zero,neg_lt_neg_iff] at hh
  exact ⟨hh.2,hh.1⟩

theorem rightRank_parent_ray_negative (a b tau w mu ell s t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1)
    (hs : 0 ≤ s) (hs1 : s ≤ w-1) (ht : |t| ≤ 1) :
    orient (rightRank a b tau w mu ell) (original (cloneAt b tau w s)) (frame t) < 0 := by
  have hspan : -a-(-b)=b-a := by ring
  have hh := (leftRank_endpoint_sides (-b) (-a) tau w mu (w-2-ell) (w-1-s) 0 (-t)
    (by linarith) hw hmu hmuW htau (by simpa only [hspan] using htauMu)
    (by linarith) (by linarith) (by simpa using ht) (by linarith) (by linarith)
    (by linarith) (by linarith) (by rfl) (by linarith)).1
  rw [clone_reverse b tau w s hw,←rightRank_reflection a b tau w mu ell hw,
    ←reflect_frame,←reflect_original,orient_reflect,orient_reverse_last,neg_neg] at hh
  exact hh

/-- Every entire parent block follows the right marker: the full row suffix
is its parent fan neighborhood, independently of the steering gap. -/
theorem rightRank_parent_fan_indexed (B : ℕ) (i k : Fin B) (a b tau w mu ell s : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) (hs : 0 ≤ s) (hs1 : s ≤ w-1) :
    ProperCross (rightRank a b tau w mu ell) (frame (frameParameter B k))
      (original (cloneAt b tau w s)) (frame (frameParameter B i)) ↔ k < i := by
  have hr := rightRank_valid a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hn (j : Fin B) := rightRank_parent_ray_negative a b tau w mu ell s (frameParameter B j)
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hs hs1 (frameParameter_unit B j).le
  rw [fan_crossing_epsilon _ _ _ _ hr (frameParameter_unit B i).le (frameParameter_unit B k).le,
    (frameParameter_antitone B).lt_iff_gt,(frameParameter_antitone B).lt_iff_gt]
  simp only [hn i,hn k,and_true,not_lt_of_ge (hn i).le,
    not_lt_of_ge (hn k).le,and_false,false_or]

theorem rightRank_nonparent_fan_indexed (B : ℕ) (i k : Fin B) (a b tau w mu ell z : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100*w*mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100*tau ≤ mu*(b-a))
    (hboxA : -1 ≤ a-tau/2) (hboxB : b+tau/2 ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell+1 ≤ w-1) (hz : |z| ≤ 1)
    (hsep : 2*mu*(b-a) ≤ |z-b|) :
    ProperCross (rightRank a b tau w mu ell) (frame (frameParameter B k))
      (original z) (frame (frameParameter B i)) ↔ (i < k ∧ z < b) ∨ (k < i ∧ b < z) := by
  have hr := rightRank_valid a b tau w mu ell hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1
  have hs (j : Fin B) := rightRank_nonparent_ray_sign a b tau w mu ell z (frameParameter B j)
    hab hw hmu hmuW htau htauMu hboxA hboxB hell hell1 hz (frameParameter_unit B j).le hsep
  rw [fan_crossing_epsilon _ z _ _ hr (frameParameter_unit B i).le (frameParameter_unit B k).le,
    (hs i).1,(hs k).1,(hs i).2,(hs k).2,
    (frameParameter_antitone B).lt_iff_gt,(frameParameter_antitone B).lt_iff_gt]
  tauto

end Q4.Candidate.RankNonselected

#print axioms Q4.Candidate.RankNonselected.leftRank_steering_bound
#print axioms Q4.Candidate.RankNonselected.leftRank_nonparent_ray_sign
#print axioms Q4.Candidate.RankNonselected.leftRank_nonselected_core
#print axioms Q4.Candidate.RankNonselected.rightRank_nonselected_core
#print axioms Q4.Candidate.RankNonselected.leftRank_parent_fan_indexed
#print axioms Q4.Candidate.RankNonselected.leftRank_nonparent_fan_indexed
#print axioms Q4.Candidate.RankNonselected.rightRank_parent_fan_indexed
#print axioms Q4.Candidate.RankNonselected.rightRank_nonparent_fan_indexed
