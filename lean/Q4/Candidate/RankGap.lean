import Q4.Candidate.ConvexSeparation

/-!
Actual clone coordinates and full opposite-rank gaps for candidate Lemma 4.3.
Ranks here are zero-based. The real parameter w may be instantiated with any
integer W≥2; using rational ranks first makes the uniform interval bounds clear.
-/

namespace Q4.Candidate.RankGap

open Q4.Candidate.ConvexSeparation

def cloneAt (a tau w s : ℚ) : ℚ := a + tau * (s / (w - 1) - 1 / 2)
def leftHeight (a b mu : ℚ) : ℚ := a + mu * (b - a)

theorem clone_zero (a tau w : ℚ) : cloneAt a tau w 0 = a - tau / 2 := by
  unfold cloneAt
  ring

theorem clone_last (a tau w : ℚ) (hw : 2 ≤ w) :
    cloneAt a tau w (w - 1) = a + tau / 2 := by
  unfold cloneAt
  rw [div_self (by linarith : w - 1 ≠ 0)]
  ring

theorem clone_mono (a tau w s t : ℚ) (htau : 0 ≤ tau) (hw : 2 ≤ w) (hst : s ≤ t) :
    cloneAt a tau w s ≤ cloneAt a tau w t := by
  have hd := (div_le_div_iff_of_pos_right (by linarith : 0 < w - 1)).2 hst
  have hp := mul_le_mul_of_nonneg_left hd htau
  unfold cloneAt
  linarith

theorem clone_bounds (a tau w s : ℚ) (htau : 0 ≤ tau) (hw : 2 ≤ w)
    (hs : 0 ≤ s) (hs' : s ≤ w - 1) :
    a - tau / 2 ≤ cloneAt a tau w s ∧ cloneAt a tau w s ≤ a + tau / 2 := by
  have hlo := clone_mono a tau w 0 s htau hw hs
  have hhi := clone_mono a tau w s (w - 1) htau hw hs'
  rw [clone_zero] at hlo
  rw [clone_last a tau w hw] at hhi
  exact ⟨hlo, hhi⟩

/-- The clone/displacement restrictions in the candidate imply these useful
division-free bounds. In particular, the full clone width pays only O(1/10000)
of the macro separation even after multiplication by W. -/
theorem scale_bounds (d tau w mu : ℚ) (hd : 0 < d) (hw : 2 ≤ w)
    (hmu : 0 < mu) (hmuW : 100 * w * mu ≤ 1)
    (_htau : 0 < tau) (htauMu : 100 * tau ≤ mu * d) :
    mu ≤ 1 / 200 ∧ 10000 * w * tau ≤ d ∧ tau ≤ mu * d / 100 := by
  have hmuw := mul_nonneg (by linarith : 0 ≤ w - 2) (le_of_lt hmu)
  have hmul := mul_le_mul_of_nonneg_right htauMu (by linarith : 0 ≤ 100 * w)
  have hmul2 := mul_le_mul_of_nonneg_right hmuW (le_of_lt hd)
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem height_between_all_clones (a b tau w mu s t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100 * w * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a))
    (hs : 0 ≤ s) (hs' : s ≤ w - 1) (ht : 0 ≤ t) (ht' : t ≤ w - 1) :
    cloneAt a tau w s < leftHeight a b mu ∧ leftHeight a b mu < cloneAt b tau w t := by
  have hb := scale_bounds (b - a) tau w mu (sub_pos.mpr hab) hw hmu hmuW htau htauMu
  have haS := clone_bounds a tau w s (le_of_lt htau) hw hs hs'
  have hbT := clone_bounds b tau w t (le_of_lt htau) hw ht ht'
  have hprod := mul_pos hmu (sub_pos.mpr hab)
  have hsmall := mul_le_mul_of_nonneg_right hb.1 (le_of_lt (sub_pos.mpr hab))
  unfold leftHeight
  constructor <;> nlinarith

theorem chord_mono_left (a c b y : ℚ) (hac : a ≤ c) (hy : y ≤ b) :
    chordX a b y ≤ chordX c b y := by
  have hp := mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hy)
  unfold chordX
  nlinarith

theorem chord_antitone_right (a b d y : ℚ) (hbd : b ≤ d) (hy : a ≤ y) :
    chordX a d y ≤ chordX a b y := by
  have hp := mul_nonneg (sub_nonneg.mpr hbd) (sub_nonneg.mpr hy)
  unfold chordX
  nlinarith

def gapLowerX (a b tau w mu ell : ℚ) : ℚ :=
  chordX (cloneAt a tau w ell) (cloneAt b tau w 0) (leftHeight a b mu)

def gapUpperX (a b tau w mu ell : ℚ) : ℚ :=
  chordX (cloneAt a tau w (ell + 1)) (cloneAt b tau w (w - 1)) (leftHeight a b mu)

def leftRank (a b tau w mu ell : ℚ) : Point :=
  ((gapLowerX a b tau w mu ell + gapUpperX a b tau w mu ell) / 2,
    leftHeight a b mu)

theorem full_gap_identity (a b tau w mu ell : ℚ) (hw : 2 ≤ w) :
    (gapUpperX a b tau w mu ell - gapLowerX a b tau w mu ell) * (100 * (w - 1)) =
      tau * ((b - a) * (1 - w * mu) + tau * (ell + 1 - w / 2)) := by
  unfold gapUpperX gapLowerX chordX cloneAt leftHeight
  field_simp [show w - 1 ≠ 0 by linarith]
  ring

/-- The complete opposite-rank ranges are separated by at least the manuscript's
τ(b-a)/(200W), for every internal gap. This is a proved positive numerical lower
bound, not an assumed orientation or an assumed gap-existence certificate. -/
theorem full_gap_lower_bound (a b tau w mu ell : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100 * w * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a)) (hell : 0 ≤ ell) :
    tau * (b - a) / (200 * w) ≤
      gapUpperX a b tau w mu ell - gapLowerX a b tau w mu ell := by
  have hb := scale_bounds (b - a) tau w mu (sub_pos.mpr hab) hw hmu hmuW htau htauMu
  have hmuD := mul_le_mul_of_nonneg_right hmuW (le_of_lt (sub_pos.mpr hab))
  have htell := mul_nonneg (le_of_lt htau) hell
  have hbracket : (b - a) / 2 ≤ (b - a) * (1 - w * mu) + tau * (ell + 1 - w / 2) := by
    nlinarith [hb.2.1]
  have hscaled := mul_le_mul_of_nonneg_left hbracket (le_of_lt htau)
  have he := full_gap_identity a b tau w mu ell hw
  have hprod := mul_pos htau (sub_pos.mpr hab)
  have hg : 0 < gapUpperX a b tau w mu ell - gapLowerX a b tau w mu ell := by
    by_contra hneg
    have hx := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hneg)
      (show 0 ≤ 100 * (w - 1) by linarith)
    nlinarith
  apply (div_le_iff₀ (show 0 < 200 * w by linarith)).2
  nlinarith

theorem full_gap_positive (a b tau w mu ell : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100 * w * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a)) (hell : 0 ≤ ell) :
    gapLowerX a b tau w mu ell < gapUpperX a b tau w mu ell := by
  have hg := full_gap_lower_bound a b tau w mu ell hab hw hmu hmuW htau htauMu hell
  have hp : 0 < tau * (b - a) / (200 * w) := by positivity
  linarith

/-- Every opposite rank is below the gap at a selected lower source rank. -/
theorem lower_ranks_below_midpoint (a b tau w mu ell s t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100 * w * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a))
    (hell : 0 ≤ ell) (hell' : ell + 1 ≤ w - 1)
    (_hs : 0 ≤ s) (hsel : s ≤ ell) (ht : 0 ≤ t) (ht' : t ≤ w - 1) :
    chordX (cloneAt a tau w s) (cloneAt b tau w t) (leftHeight a b mu) <
      (leftRank a b tau w mu ell).1 := by
  have hbetween := height_between_all_clones a b tau w mu ell t hab hw hmu hmuW htau htauMu
    hell (by linarith) ht ht'
  have h1 := chord_mono_left (cloneAt a tau w s) (cloneAt a tau w ell)
    (cloneAt b tau w t) (leftHeight a b mu)
    (clone_mono a tau w s ell (le_of_lt htau) hw hsel) (le_of_lt hbetween.2)
  have h2 := chord_antitone_right (cloneAt a tau w ell) (cloneAt b tau w 0)
    (cloneAt b tau w t) (leftHeight a b mu)
    (clone_mono b tau w 0 t (le_of_lt htau) hw ht) (le_of_lt hbetween.1)
  have hg := full_gap_positive a b tau w mu ell hab hw hmu hmuW htau htauMu hell
  dsimp [leftRank, gapLowerX] at *
  linarith

/-- Every opposite rank is above the gap at a selected upper source rank. -/
theorem upper_ranks_above_midpoint (a b tau w mu ell s t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100 * w * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a))
    (hell : 0 ≤ ell) (hell' : ell + 1 ≤ w - 1)
    (hsel : ell + 1 ≤ s) (_hs' : s ≤ w - 1) (ht : 0 ≤ t) (ht' : t ≤ w - 1) :
    (leftRank a b tau w mu ell).1 <
      chordX (cloneAt a tau w s) (cloneAt b tau w t) (leftHeight a b mu) := by
  have hbetween := height_between_all_clones a b tau w mu (ell + 1) t
    hab hw hmu hmuW htau htauMu (by linarith) hell' ht ht'
  have h1 := chord_antitone_right (cloneAt a tau w (ell + 1)) (cloneAt b tau w t)
    (cloneAt b tau w (w - 1)) (leftHeight a b mu)
    (clone_mono b tau w t (w - 1) (le_of_lt htau) hw ht') (le_of_lt hbetween.1)
  have h2 := chord_mono_left (cloneAt a tau w (ell + 1)) (cloneAt a tau w s)
    (cloneAt b tau w t) (leftHeight a b mu)
    (clone_mono a tau w (ell + 1) s (le_of_lt htau) hw hsel) (le_of_lt hbetween.2)
  have hg := full_gap_positive a b tau w mu ell hab hw hmu hmuW htau htauMu hell
  dsimp [leftRank, gapUpperX] at *
  linarith

theorem abs_two_of_unit (a b : ℚ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a - b| ≤ 2 := by
  have hh := abs_sub a b
  linarith

theorem chordX_swap (a b y : ℚ) : chordX a b y = chordX b a y := by
  unfold chordX
  ring

theorem chord_to_endpoint_identity (a b s y : ℚ) :
    chordX a b y - (original s).1 =
      ((s - a) * (s - b) - (a + b) * (y - s)) / 100 := by
  unfold chordX original
  ring

/-- A chord point at height y is almost vertically aligned with any endpoint
in the same width-τ clone block, once its height gap is at least τ. -/
theorem chord_endpoint_slope (a b s y tau : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hs : |s| ≤ 1)
    (hneara : |s - a| ≤ tau) (hgap : tau ≤ |y - s|) :
    |chordX a b y - (original s).1| ≤ |y - s| / 10 := by
  have hsb := abs_two_of_unit s b hs hb
  have hab : |a + b| ≤ 2 := le_trans (abs_add_le a b) (by linarith)
  have hp1 : |(s - a) * (s - b)| ≤ tau * 2 := by
    rw [abs_mul]
    exact mul_le_mul hneara hsb (abs_nonneg _) (le_trans (abs_nonneg _) hneara)
  have hp2 : |(a + b) * (y - s)| ≤ 2 * |y - s| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hab (abs_nonneg _)
  rw [chord_to_endpoint_identity, abs_div]
  norm_num
  have hsub := abs_sub ((s - a) * (s - b)) ((a + b) * (y - s))
  nlinarith [abs_nonneg (y - s)]

theorem chord_endpoint_slope_either (a b s y tau : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hs : |s| ≤ 1)
    (hnear : |s - a| ≤ tau ∨ |s - b| ≤ tau) (hgap : tau ≤ |y - s|) :
    |chordX a b y - (original s).1| ≤ |y - s| / 10 := by
  rcases hnear with hnear | hnear
  · exact chord_endpoint_slope a b s y tau ha hb hs hnear hgap
  · rw [chordX_swap]
    exact chord_endpoint_slope b a s y tau hb ha hs hnear hgap

theorem midpoint_endpoint_slope (a b c d s y tau : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hs : |s| ≤ 1)
    (hnear1 : |s - a| ≤ tau ∨ |s - b| ≤ tau)
    (hnear2 : |s - c| ≤ tau ∨ |s - d| ≤ tau) (hgap : tau ≤ |y - s|) :
    |(chordX a b y + chordX c d y) / 2 - (original s).1| ≤ |y - s| / 10 := by
  have h1 := chord_endpoint_slope_either a b s y tau ha hb hs hnear1 hgap
  have h2 := chord_endpoint_slope_either c d s y tau hc hd hs hnear2 hgap
  have he : (chordX a b y + chordX c d y) / 2 - (original s).1 =
      ((chordX a b y - (original s).1) + (chordX c d y - (original s).1)) / 2 := by ring
  rw [he, abs_div]
  norm_num
  have hh := abs_add_le (chordX a b y - (original s).1) (chordX c d y - (original s).1)
  linarith

/-- These are the endpoint-side tests for a real frame fan, derived from the
explicit horizontal/vertical coordinate bounds. No orientation sign is assumed. -/
theorem frame_endpoint_signs (r : Point) (s t : ℚ)
    (hr : phi r ≤ 0) (hry : |r.2| ≤ 1) (ht : |t| ≤ 1)
    (hslope : |r.1 - (original s).1| ≤ |r.2 - s| / 10) :
    (s < r.2 → orient r (frame t) (original s) < 0) ∧
      (r.2 < s → 0 < orient r (frame t) (original s)) := by
  have hrx := phi_nonpos_x_bound r hr
  have hhorizontal : 11 ≤ (frame t).1 - r.1 := by
    dsimp [frame]
    nlinarith [sq_nonneg t]
  have hdy := abs_two_of_unit t r.2 ht hry
  have hterm : |(t - r.2) * ((original s).1 - r.1)| ≤ 2 * (|r.2 - s| / 10) := by
    rw [abs_mul, abs_sub_comm (original s).1 r.1]
    exact mul_le_mul hdy hslope (abs_nonneg _) (by norm_num)
  have hterm' := abs_le.mp hterm
  constructor
  · intro hbelow
    have hg : 0 < r.2 - s := sub_pos.mpr hbelow
    have hscaled := mul_le_mul_of_nonneg_right hhorizontal (le_of_lt hg)
    rw [abs_of_pos hg] at hterm'
    dsimp [orient, original, frame] at *
    nlinarith [hterm'.1, hterm'.2]
  · intro habove
    have hg : 0 < s - r.2 := sub_pos.mpr habove
    have hscaled := mul_le_mul_of_nonneg_right hhorizontal (le_of_lt hg)
    rw [abs_of_neg (by linarith : r.2 - s < 0)] at hterm'
    dsimp [orient, original, frame] at *
    nlinarith [hterm'.1, hterm'.2]

theorem source_orientation (a b : ℚ) (r : Point) :
    orient (original a) (original b) r = (b - a) * (chordX a b r.2 - r.1) := by
  unfold orient original chordX
  ring

theorem source_frame_negative (a b t : ℚ) (hab : a < b) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    orient (original a) (original b) (frame t) < 0 := by
  have haa := unit_square_bound a (abs_le.mp ha).1 (abs_le.mp ha).2
  have hbb := unit_square_bound b (abs_le.mp hb).1 (abs_le.mp hb).2
  have hx : chordX a b t < (frame t).1 := by
    unfold chordX frame
    nlinarith [sq_nonneg (t + a), sq_nonneg (t + b), sq_nonneg (a - b)]
  rw [source_orientation]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr hab) (sub_neg.mpr hx)

/-- Full proper-crossing criterion, with both endpoint orientations proved
from numeric geometry. This holds simultaneously for every frame height t in
[-1,1] and any selected source edge whose numeric corridor bounds hold. -/
theorem frame_fan_crossing_iff (r : Point) (a b t : ℚ)
    (hab : a < b) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1)
    (hr : phi r ≤ 0) (hry : |r.2| ≤ 1) (hay : a < r.2) (hyb : r.2 < b)
    (hslopeA : |r.1 - (original a).1| ≤ |r.2 - a| / 10)
    (hslopeB : |r.1 - (original b).1| ≤ |r.2 - b| / 10) :
    ProperCross r (frame t) (original a) (original b) ↔ r.1 < chordX a b r.2 := by
  have hA := (frame_endpoint_signs r a t hr hry ht hslopeA).1 hay
  have hB := (frame_endpoint_signs r b t hr hry ht hslopeB).2 hyb
  have hframe := source_frame_negative a b t hab ha hb
  have hfirst := mul_neg_of_neg_of_pos hA hB
  have hd : 0 < b - a := sub_pos.mpr hab
  constructor
  · intro hc
    have hp := hc.2
    have hsource : 0 < orient (original a) (original b) r := by
      rcases mul_neg_iff.mp hp with h | h
      · exact h.1
      · linarith [h.2]
    rw [source_orientation] at hsource
    have hpos : 0 < chordX a b r.2 - r.1 := (mul_pos_iff_of_pos_left hd).mp hsource
    linarith
  · intro hx
    refine ⟨hfirst, ?_⟩
    apply mul_neg_of_pos_of_neg _ hframe
    rw [source_orientation]
    exact mul_pos hd (sub_pos.mpr hx)

theorem clone_near_same_block (a tau w s t : ℚ) (htau : 0 ≤ tau) (hw : 2 ≤ w)
    (hs : 0 ≤ s) (hs' : s ≤ w - 1) (ht : 0 ≤ t) (ht' : t ≤ w - 1) :
    |cloneAt a tau w s - cloneAt a tau w t| ≤ tau := by
  have h1 := clone_bounds a tau w s htau hw hs hs'
  have h2 := clone_bounds a tau w t htau hw ht ht'
  exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

theorem clones_in_unit (a b tau w s : ℚ) (hab : a ≤ b) (htau : 0 ≤ tau) (hw : 2 ≤ w)
    (hboxA : -1 ≤ a - tau / 2) (hboxB : b + tau / 2 ≤ 1)
    (hs : 0 ≤ s) (hs' : s ≤ w - 1) :
    |cloneAt a tau w s| ≤ 1 ∧ |cloneAt b tau w s| ≤ 1 := by
  have h1 := clone_bounds a tau w s htau hw hs hs'
  have h2 := clone_bounds b tau w s htau hw hs hs'
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem height_gaps_pay_width (a b tau w mu s t : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100 * w * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a))
    (hs : 0 ≤ s) (hs' : s ≤ w - 1) (ht : 0 ≤ t) (ht' : t ≤ w - 1) :
    tau ≤ leftHeight a b mu - cloneAt a tau w s ∧
      tau ≤ cloneAt b tau w t - leftHeight a b mu := by
  have hb := scale_bounds (b - a) tau w mu (sub_pos.mpr hab) hw hmu hmuW htau htauMu
  have haS := clone_bounds a tau w s (le_of_lt htau) hw hs hs'
  have hbT := clone_bounds b tau w t (le_of_lt htau) hw ht ht'
  have hsmall := mul_le_mul_of_nonneg_right hb.1 (le_of_lt (sub_pos.mpr hab))
  unfold leftHeight
  constructor <;> nlinarith

/-- Actual left rank prototype, all source clone pairs, and every frame point
simultaneously. Both endpoint-side signs and the source-line sign are derived
from the coordinates and scales; the equivalence is not a line-extension test. -/
theorem leftRank_actual_fan_crossing (a b tau w mu ell s t z : ℚ)
    (hab : a < b) (hw : 2 ≤ w) (hmu : 0 < mu) (hmuW : 100 * w * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a))
    (hboxA : -1 ≤ a - tau / 2) (hboxB : b + tau / 2 ≤ 1) (hz : |z| ≤ 1)
    (hell : 0 ≤ ell) (hell' : ell + 1 ≤ w - 1)
    (hs : 0 ≤ s) (hs' : s ≤ w - 1) (ht : 0 ≤ t) (ht' : t ≤ w - 1) :
    ProperCross (leftRank a b tau w mu ell) (frame z)
      (original (cloneAt a tau w s)) (original (cloneAt b tau w t)) ↔
        (leftRank a b tau w mu ell).1 <
          chordX (cloneAt a tau w s) (cloneAt b tau w t) (leftHeight a b mu) := by
  have hell0 : ell ≤ w - 1 := by linarith
  have hell1 : 0 ≤ ell + 1 := by linarith
  have hw0 : 0 ≤ w - 1 := by linarith
  have huu := clones_in_unit a b tau w s (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB hs hs'
  have hvv := clones_in_unit a b tau w t (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB ht ht'
  have he0 := clones_in_unit a b tau w ell (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB hell hell0
  have he1 := clones_in_unit a b tau w (ell + 1) (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB hell1 hell'
  have hb0 := clones_in_unit a b tau w 0 (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB (by rfl) hw0
  have hb1 := clones_in_unit a b tau w (w - 1) (le_of_lt hab) (le_of_lt htau) hw hboxA hboxB hw0 (by rfl)
  have hbetween := height_between_all_clones a b tau w mu s t hab hw hmu hmuW htau htauMu hs hs' ht ht'
  have hbetween0 := height_between_all_clones a b tau w mu ell 0 hab hw hmu hmuW htau htauMu hell hell0 (by rfl) hw0
  have hbetween1 := height_between_all_clones a b tau w mu (ell + 1) (w - 1) hab hw hmu hmuW htau htauMu hell1 hell' hw0 (by rfl)
  have hphi : phi (leftRank a b tau w mu ell) ≤ 0 := by
    apply le_of_lt
    exact rank_midpoint_inside _ _ _ _ _ hbetween0.1 hbetween0.2 hbetween1.1 hbetween1.2
  have hry : |(leftRank a b tau w mu ell).2| ≤ 1 := by
    apply abs_le.mpr
    dsimp [leftRank]
    constructor
    · linarith [(abs_le.mp huu.1).1, hbetween.1]
    · linarith [(abs_le.mp hvv.2).2, hbetween.2]
  have hgap := height_gaps_pay_width a b tau w mu s t hab hw hmu hmuW htau htauMu hs hs' ht ht'
  have hgapA : tau ≤ |leftHeight a b mu - cloneAt a tau w s| := by
    rw [abs_of_pos (sub_pos.mpr hbetween.1)]
    exact hgap.1
  have hgapB : tau ≤ |leftHeight a b mu - cloneAt b tau w t| := by
    rw [abs_of_neg (sub_neg.mpr hbetween.2)]
    linarith [hgap.2]
  have hslopeA : |(leftRank a b tau w mu ell).1 - (original (cloneAt a tau w s)).1| ≤
      |(leftRank a b tau w mu ell).2 - cloneAt a tau w s| / 10 := by
    exact midpoint_endpoint_slope _ _ _ _ _ _ tau he0.1 hb0.2 he1.1 hb1.2 huu.1
      (Or.inl (clone_near_same_block a tau w s ell (le_of_lt htau) hw hs hs' hell hell0))
      (Or.inl (clone_near_same_block a tau w s (ell + 1) (le_of_lt htau) hw hs hs' hell1 hell')) hgapA
  have hslopeB : |(leftRank a b tau w mu ell).1 - (original (cloneAt b tau w t)).1| ≤
      |(leftRank a b tau w mu ell).2 - cloneAt b tau w t| / 10 := by
    exact midpoint_endpoint_slope _ _ _ _ _ _ tau he0.1 hb0.2 he1.1 hb1.2 hvv.2
      (Or.inr (clone_near_same_block b tau w t 0 (le_of_lt htau) hw ht ht' (by rfl) hw0))
      (Or.inr (clone_near_same_block b tau w t (w - 1) (le_of_lt htau) hw ht ht' hw0 (by rfl))) hgapB
  exact frame_fan_crossing_iff _ _ _ z (lt_trans hbetween.1 hbetween.2) huu.1 hvv.2 hz
    hphi hry hbetween.1 hbetween.2 hslopeA hslopeB

/-- Full discrete selected-bundle table of the left rank prototype. Indices
are zero-based; ell is the last rank on the noncrossing side of the gap. -/
theorem leftRank_crossing_table (a b tau mu z : ℚ) (W ell : ℕ) (s t : Fin W)
    (hab : a < b) (hW : 2 ≤ W) (hmu : 0 < mu) (hmuW : 100 * (W : ℚ) * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a))
    (hboxA : -1 ≤ a - tau / 2) (hboxB : b + tau / 2 ≤ 1) (hz : |z| ≤ 1)
    (hell : ell + 1 < W) :
    ProperCross (leftRank a b tau W mu ell) (frame z)
      (original (cloneAt a tau W s.val)) (original (cloneAt b tau W t.val)) ↔ ell < s.val := by
  have hw : (2 : ℚ) ≤ W := by exact_mod_cast hW
  have he0 : (0 : ℚ) ≤ ell := by positivity
  have he1 : (ell : ℚ) + 1 ≤ (W : ℚ) - 1 := by
    have hh : (ell : ℚ) + 2 ≤ W := by exact_mod_cast (by omega : ell + 2 ≤ W)
    linarith
  have hs : (0 : ℚ) ≤ s.val := by positivity
  have hs' : (s.val : ℚ) ≤ (W : ℚ) - 1 := by
    have hh : (s.val : ℚ) + 1 ≤ W := by exact_mod_cast (by omega : s.val + 1 ≤ W)
    linarith
  have ht : (0 : ℚ) ≤ t.val := by positivity
  have ht' : (t.val : ℚ) ≤ (W : ℚ) - 1 := by
    have hh : (t.val : ℚ) + 1 ≤ W := by exact_mod_cast (by omega : t.val + 1 ≤ W)
    linarith
  rw [leftRank_actual_fan_crossing a b tau W mu ell s.val t.val z
    hab hw hmu hmuW htau htauMu hboxA hboxB hz he0 he1 hs hs' ht ht']
  by_cases hlow : s.val ≤ ell
  · have hh := lower_ranks_below_midpoint a b tau W mu ell s.val t.val
      hab hw hmu hmuW htau htauMu he0 he1 hs (by exact_mod_cast hlow) ht ht'
    constructor
    · intro hx
      linarith
    · omega
  · have hhigh : ell + 1 ≤ s.val := by omega
    have hh := upper_ranks_above_midpoint a b tau W mu ell s.val t.val
      hab hw hmu hmuW htau htauMu he0 he1 (by exact_mod_cast hhigh) hs' ht ht'
    exact ⟨fun _ => by omega, fun _ => hh⟩

def reflect (p : Point) : Point := (p.1, -p.2)

theorem reflect_original (a : ℚ) : reflect (original a) = original (-a) := by
  apply Prod.ext <;> dsimp [reflect, original] <;> ring

theorem reflect_frame (t : ℚ) : reflect (frame t) = frame (-t) := by
  apply Prod.ext <;> dsimp [reflect, frame] <;> ring

theorem properCross_reflect (a b c d : Point) :
    ProperCross (reflect a) (reflect b) (reflect c) (reflect d) ↔ ProperCross a b c d := by
  have hh (a b c : Point) : orient (reflect a) (reflect b) (reflect c) = -orient a b c := by
    unfold orient reflect
    ring
  simp only [ProperCross, hh, neg_mul_neg]

theorem properCross_reverse_second (a b c d : Point) :
    ProperCross a b c d ↔ ProperCross a b d c := by
  rw [properCross_swap_edges a b c d, properCross_reverse_first c d a b,
    properCross_swap_edges d c a b]

def rightHeight (a b mu : ℚ) : ℚ := b - mu * (b - a)

def rightRank (a b tau w mu ell : ℚ) : Point :=
  ((chordX (cloneAt a tau w (w - 1)) (cloneAt b tau w (ell + 1)) (rightHeight a b mu) +
    chordX (cloneAt a tau w 0) (cloneAt b tau w ell) (rightHeight a b mu)) / 2,
    rightHeight a b mu)

/-- The reflected left midpoint is exactly the manuscript's actual right
midpoint, with reversed clone orders. -/
theorem rightRank_reflection (a b tau w mu ell : ℚ) (hw : 2 ≤ w) :
    reflect (rightRank a b tau w mu ell) = leftRank (-b) (-a) tau w mu (w - 2 - ell) := by
  apply Prod.ext <;> dsimp [reflect, rightRank, leftRank, gapLowerX, gapUpperX,
    rightHeight, leftHeight, chordX, cloneAt] <;>
    field_simp [show w - 1 ≠ 0 by linarith] <;> ring

theorem clone_rev_fin (a tau : ℚ) (W : ℕ) (i : Fin W) (hW : 2 ≤ W) :
    cloneAt (-a) tau W i.rev.val = -cloneAt a tau W i.val := by
  have hsum : i.rev.val + i.val + 1 = W := by simp [Fin.val_rev]; omega
  have hsumR : (i.rev.val : ℚ) + i.val + 1 = W := by exact_mod_cast hsum
  have he : (i.rev.val : ℚ) = (W : ℚ) - 1 - i.val := by linarith
  rw [he]
  unfold cloneAt
  have hw : (2 : ℚ) ≤ W := by exact_mod_cast hW
  field_simp [show (W : ℚ) - 1 ≠ 0 by linarith]
  ring

/-- Full discrete selected-bundle table of the right rank prototype. For every
left endpoint rank s, every frame fan crosses precisely at right ranks t≤ell. -/
theorem rightRank_crossing_table (a b tau mu z : ℚ) (W ell : ℕ) (s t : Fin W)
    (hab : a < b) (hW : 2 ≤ W) (hmu : 0 < mu) (hmuW : 100 * (W : ℚ) * mu ≤ 1)
    (htau : 0 < tau) (htauMu : 100 * tau ≤ mu * (b - a))
    (hboxA : -1 ≤ a - tau / 2) (hboxB : b + tau / 2 ≤ 1) (hz : |z| ≤ 1)
    (hell : ell + 1 < W) :
    ProperCross (rightRank a b tau W mu ell) (frame z)
      (original (cloneAt a tau W s.val)) (original (cloneAt b tau W t.val)) ↔ t.val ≤ ell := by
  let L : ℕ := W - 2 - ell
  have hLsum : L + ell + 2 = W := by dsimp [L]; omega
  have hLsumR : (L : ℚ) + ell + 2 = W := by exact_mod_cast hLsum
  have hL : (L : ℚ) = (W : ℚ) - 2 - ell := by linarith
  have hLbound : L + 1 < W := by omega
  have hw : (2 : ℚ) ≤ W := by exact_mod_cast hW
  have htbl := leftRank_crossing_table (-b) (-a) tau mu (-z) W L t.rev s.rev
    (by linarith) hW hmu hmuW htau (by linarith) (by linarith) (by linarith)
    (by simpa using hz) hLbound
  rw [clone_rev_fin b tau W t hW, clone_rev_fin a tau W s hW] at htbl
  rw [hL, ← rightRank_reflection a b tau W mu ell hw,
    ← reflect_frame, ← reflect_original, ← reflect_original,
    properCross_reflect, ← properCross_reverse_second] at htbl
  have hrev : t.rev.val + t.val + 1 = W := by simp [Fin.val_rev]; omega
  exact htbl.trans (by omega)

end Q4.Candidate.RankGap

#print axioms Q4.Candidate.RankGap.height_between_all_clones
#print axioms Q4.Candidate.RankGap.full_gap_identity
#print axioms Q4.Candidate.RankGap.full_gap_lower_bound
#print axioms Q4.Candidate.RankGap.full_gap_positive
#print axioms Q4.Candidate.RankGap.lower_ranks_below_midpoint
#print axioms Q4.Candidate.RankGap.upper_ranks_above_midpoint
#print axioms Q4.Candidate.RankGap.frame_endpoint_signs
#print axioms Q4.Candidate.RankGap.frame_fan_crossing_iff
#print axioms Q4.Candidate.RankGap.leftRank_actual_fan_crossing
#print axioms Q4.Candidate.RankGap.leftRank_crossing_table
#print axioms Q4.Candidate.RankGap.rightRank_reflection
#print axioms Q4.Candidate.RankGap.rightRank_crossing_table
