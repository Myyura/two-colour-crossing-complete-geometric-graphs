import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Q4.CleanWire

/-!
Exact rational geometry for Lemma 4.7 of `two_colour_crossing_candidate.pdf`.
The caps use the actual constants of §6: D = 10, F = 1, κ = κf = 1/100.
The strict orientation crossing test is connected below to intersection of two
open segments; separation is therefore a statement about geometric crossings,
not an input hypothesis about a proposed crossing graph.

This module does not construct the rank gaps or the final general-position
insertion, and does not establish coordinate bit bounds or reduction hardness.
-/

namespace Q4.Candidate.ConvexSeparation

abbrev Point := ℚ × ℚ

def orient (a b c : Point) : ℚ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def ProperCross (a b c d : Point) : Prop :=
  orient a b c * orient a b d < 0 ∧ orient c d a * orient c d b < 0

def fromInt (p : Q4.CleanWire.Point) : Point := ((p.1 : ℚ), (p.2 : ℚ))

/-- Compatibility with the existing project crossing predicate on integer
coordinates. The rational predicate uses precisely the same strict signs. -/
theorem properCross_fromInt (a b c d : Q4.CleanWire.Point) :
    ProperCross (fromInt a) (fromInt b) (fromInt c) (fromInt d) ↔
      Q4.CleanWire.properCross a b c d = true := by
  simp only [ProperCross, orient, fromInt, Q4.CleanWire.properCross,
    Q4.CleanWire.orient]
  norm_cast
  simp

theorem properCross_swap_edges (a b c d : Point) :
    ProperCross a b c d ↔ ProperCross c d a b := and_comm

theorem properCross_reverse_first (a b c d : Point) :
    ProperCross a b c d ↔ ProperCross b a c d := by
  have h1 : orient b a c = -orient a b c := by unfold orient; ring
  have h2 : orient b a d = -orient a b d := by unfold orient; ring
  simp only [ProperCross, h1, h2, neg_mul_neg, mul_comm]

def mix (a b : Point) (l : ℚ) : Point :=
  ((1 - l) * a.1 + l * b.1, (1 - l) * a.2 + l * b.2)

theorem opposite_ratio (u v : ℚ) (h : u * v < 0) :
    0 < u / (u - v) ∧ u / (u - v) < 1 := by
  rcases mul_neg_iff.mp h with h | h
  · constructor
    · exact div_pos h.1 (by linarith)
    · apply (div_lt_one (by linarith : 0 < u - v)).2
      linarith
  · constructor
    · exact div_pos_of_neg_of_neg h.1 (by linarith)
    · apply (div_lt_one_of_neg (by linarith : u - v < 0)).2
      linarith

/-- The orientation-sign predicate entails an actual common open-segment point.
No distinctness or general-position axiom is needed: strict signs imply all
nondegeneracy needed for the division in the explicit intersection parameters. -/
theorem properCross_has_open_intersection (a b c d : Point)
    (h : ProperCross a b c d) :
    ∃ l m : ℚ, 0 < l ∧ l < 1 ∧ 0 < m ∧ m < 1 ∧ mix a b l = mix c d m := by
  have hl := opposite_ratio (orient c d a) (orient c d b) h.2
  have hm := opposite_ratio (orient a b c) (orient a b d) h.1
  have hden : orient c d a - orient c d b ≠ 0 := by
    intro he
    have he' : orient c d a = orient c d b := sub_eq_zero.mp he
    have hcd := h.2
    rw [he'] at hcd
    have hs := sq_nonneg (orient c d b)
    nlinarith
  have hden' : orient a b c - orient a b d = -(orient c d a - orient c d b) := by
    unfold orient
    ring
  refine ⟨_, _, hl.1, hl.2, hm.1, hm.2, ?_⟩
  rw [hden']
  apply Prod.ext <;> dsimp [mix] <;> field_simp [hden] <;> unfold orient <;> ring

theorem no_cross_of_segment_separation (f : Point → ℚ) (a b c d : Point)
    (hout : ∀ l : ℚ, 0 < l → l < 1 → 0 < f (mix a b l))
    (hin : ∀ m : ℚ, 0 ≤ m → m ≤ 1 → f (mix c d m) ≤ 0) :
    ¬ ProperCross a b c d := by
  intro hc
  obtain ⟨l, m, hl, hl', hm, hm', he⟩ := properCross_has_open_intersection a b c d hc
  have hpos := hout l hl hl'
  rw [he] at hpos
  have hnonpos := hin m (le_of_lt hm) (le_of_lt hm')
  linarith

def original (a : ℚ) : Point := (-10 - a ^ 2 / 100, a)
def frame (t : ℚ) : Point := (1 + t ^ 2 / 100, t)
def phi (p : Point) : ℚ := p.1 + 10 + p.2 ^ 2 / 100
def psi (p : Point) : ℚ := 1 + p.2 ^ 2 / 100 - p.1

theorem phi_original (a : ℚ) : phi (original a) = 0 := by
  unfold phi original
  ring

theorem psi_frame (t : ℚ) : psi (frame t) = 0 := by
  unfold psi frame
  ring

theorem phi_mix (p q : Point) (l : ℚ) :
    phi (mix p q l) = (1 - l) * phi p + l * phi q -
      l * (1 - l) * (q.2 - p.2) ^ 2 / 100 := by
  unfold phi mix
  ring

theorem psi_mix (p q : Point) (l : ℚ) :
    psi (mix p q l) = (1 - l) * psi p + l * psi q -
      l * (1 - l) * (q.2 - p.2) ^ 2 / 100 := by
  unfold psi mix
  ring

theorem phi_segment_nonpos (p q : Point) (hp : phi p ≤ 0) (hq : phi q ≤ 0)
    (l : ℚ) (hl : 0 ≤ l) (hl' : l ≤ 1) : phi (mix p q l) ≤ 0 := by
  rw [phi_mix]
  have h1 := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - l) hp
  have h2 := mul_nonpos_of_nonneg_of_nonpos hl hq
  have h3 := mul_nonneg (mul_nonneg hl (by linarith : 0 ≤ 1 - l))
    (sq_nonneg (q.2 - p.2))
  linarith

theorem psi_segment_nonpos (p q : Point) (hp : psi p ≤ 0) (hq : psi q ≤ 0)
    (l : ℚ) (hl : 0 ≤ l) (hl' : l ≤ 1) : psi (mix p q l) ≤ 0 := by
  rw [psi_mix]
  have h1 := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - l) hp
  have h2 := mul_nonpos_of_nonneg_of_nonpos hl hq
  have h3 := mul_nonneg (mul_nonneg hl (by linarith : 0 ≤ 1 - l))
    (sq_nonneg (q.2 - p.2))
  linarith

theorem unit_square_bound (a : ℚ) (ha : -1 ≤ a) (ha' : a ≤ 1) : a ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - a) (by linarith : 0 ≤ 1 + a)]

theorem two_square_bound (a : ℚ) (ha : -2 ≤ a) (ha' : a ≤ 2) : a ^ 2 ≤ 4 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ 2 - a) (by linarith : 0 ≤ 2 + a)]

theorem phi_original_frame (a t l : ℚ) :
    phi (mix (original a) (frame t) l) =
      l * (11 + t ^ 2 / 100 + (2 * a * t - a ^ 2) / 100) +
        l ^ 2 * (t - a) ^ 2 / 100 := by
  unfold phi mix original frame
  ring

/-- Every open X segment is strictly outside the original cap region.
The conclusion even holds on the whole positive ray; no frame-height bound
is needed for this particular separator. -/
theorem original_frame_outside (a t l : ℚ) (ha : -1 ≤ a) (ha' : a ≤ 1)
    (hl : 0 < l) : 0 < phi (mix (original a) (frame t) l) := by
  rw [phi_original_frame]
  have haa := unit_square_bound a ha ha'
  have hb : 0 < 11 + t ^ 2 / 100 + (2 * a * t - a ^ 2) / 100 := by
    nlinarith [sq_nonneg (a + t)]
  have hprod := mul_pos hl hb
  have hquad := mul_nonneg (sq_nonneg l) (sq_nonneg (t - a))
  linarith

/-- This is the exact X-C and X-Y zero: the second edge may have arbitrary
endpoints inside H, including a shared original endpoint. -/
theorem original_frame_no_cross_inside (a t : ℚ) (p q : Point)
    (ha : -1 ≤ a) (ha' : a ≤ 1) (hp : phi p ≤ 0) (hq : phi q ≤ 0) :
    ¬ ProperCross (original a) (frame t) p q := by
  apply no_cross_of_segment_separation phi
  · intro l hl _
    exact original_frame_outside a t l ha ha' hl
  · exact phi_segment_nonpos p q hp hq

theorem X_C_zero (a t b c : ℚ) (ha : -1 ≤ a) (ha' : a ≤ 1) :
    ¬ ProperCross (original a) (frame t) (original b) (original c) := by
  exact original_frame_no_cross_inside a t _ _ ha ha'
    (le_of_eq (phi_original b)) (le_of_eq (phi_original c))

theorem X_Y_original_zero (a t b : ℚ) (p : Point)
    (ha : -1 ≤ a) (ha' : a ≤ 1) (hp : phi p ≤ 0) :
    ¬ ProperCross (original a) (frame t) p (original b) := by
  exact original_frame_no_cross_inside a t _ _ ha ha' hp (le_of_eq (phi_original b))

theorem X_Y_program_zero (a t : ℚ) (p q : Point)
    (ha : -1 ≤ a) (ha' : a ≤ 1) (hp : phi p ≤ 0) (hq : phi q ≤ 0) :
    ¬ ProperCross (original a) (frame t) p q :=
  original_frame_no_cross_inside a t p q ha ha' hp hq

theorem phi_nonpos_x_bound (p : Point) (hp : phi p ≤ 0) : p.1 ≤ -10 := by
  unfold phi at hp
  nlinarith [sq_nonneg p.2]

theorem psi_frame_fan (t l : ℚ) (r : Point) :
    psi (mix (frame t) r l) =
      l * (1 - r.1 + (2 * t * r.2 - t ^ 2) / 100) +
        l ^ 2 * (r.2 - t) ^ 2 / 100 := by
  unfold psi mix frame
  ring

theorem frame_fan_outside (t l : ℚ) (r : Point)
    (ht : -1 ≤ t) (ht' : t ≤ 1) (hrx : r.1 ≤ -10)
    (hry : -2 ≤ r.2) (hry' : r.2 ≤ 2) (hl : 0 < l) :
    0 < psi (mix (frame t) r l) := by
  rw [psi_frame_fan]
  have htt := unit_square_bound t ht ht'
  have hrr := two_square_bound r.2 hry hry'
  have hb : 0 < 1 - r.1 + (2 * t * r.2 - t ^ 2) / 100 := by
    nlinarith [sq_nonneg (t + r.2)]
  have hprod := mul_pos hl hb
  have hquad := mul_nonneg (sq_nonneg l) (sq_nonneg (r.2 - t))
  linarith

/-- No frame fan (X or T) crosses an I edge. -/
theorem frame_fan_no_cross_I (t u v : ℚ) (r : Point)
    (ht : -1 ≤ t) (ht' : t ≤ 1) (hr : phi r ≤ 0)
    (hry : -2 ≤ r.2) (hry' : r.2 ≤ 2) :
    ¬ ProperCross (frame t) r (frame u) (frame v) := by
  apply no_cross_of_segment_separation psi
  · intro l hl _
    exact frame_fan_outside t l r ht ht' (phi_nonpos_x_bound r hr) hry hry' hl
  · exact psi_segment_nonpos _ _ (le_of_eq (psi_frame u)) (le_of_eq (psi_frame v))

/-- C and Y are also disjoint from I: their entire segments have x ≤ -10. -/
theorem nonframe_no_cross_I (p q : Point) (u v : ℚ)
    (hp : phi p ≤ 0) (hq : phi q ≤ 0) :
    ¬ ProperCross p q (frame u) (frame v) := by
  apply no_cross_of_segment_separation psi
  · intro l hl hl'
    have hphi := phi_segment_nonpos p q hp hq l (le_of_lt hl) (le_of_lt hl')
    have hx := phi_nonpos_x_bound (mix p q l) hphi
    unfold psi
    nlinarith [sq_nonneg (mix p q l).2]
  · exact psi_segment_nonpos _ _ (le_of_eq (psi_frame u)) (le_of_eq (psi_frame v))

def ordinary (a mu : ℚ) : Point := mix (original a) (frame 0) (-mu)

/-- The actual ordinary prototype lies strictly inside H. -/
theorem ordinary_inside (a mu : ℚ) (ha : -1 ≤ a) (ha' : a ≤ 1)
    (hmu : 0 < mu) (hmu' : mu ≤ 1) : phi (ordinary a mu) < 0 := by
  unfold ordinary
  rw [phi_original_frame]
  have haa := unit_square_bound a ha ha'
  have hprod : mu * a ^ 2 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hmu' (sq_nonneg a)
    nlinarith
  have hb : 0 < 11 - a ^ 2 / 100 - mu * a ^ 2 / 100 := by linarith
  have hpos := mul_pos hmu hb
  nlinarith

theorem ordinary_height (a mu : ℚ) (ha : -1 ≤ a) (ha' : a ≤ 1)
    (hmu : 0 ≤ mu) (hmu' : mu ≤ 1) :
    -2 ≤ (ordinary a mu).2 ∧ (ordinary a mu).2 ≤ 2 := by
  have hlo := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ 1 + mu)
  have hhi := mul_le_mul_of_nonneg_left ha' (by linarith : 0 ≤ 1 + mu)
  dsimp [ordinary, mix, original, frame]
  constructor <;> nlinarith

def chordX (a b y : ℚ) : ℚ := -10 - ((a + b) * y - a * b) / 100

theorem phi_chord (a b y : ℚ) :
    phi (chordX a b y, y) = -(y - a) * (b - y) / 100 := by
  unfold phi chordX
  ring

/-- Actual steered rank points use a midpoint of two source-chord coordinates.
Both source chords may have different endpoints; only their already-asserted
strict height gaps are required, not any crossing or abstract rank assumption. -/
theorem rank_midpoint_inside (a b c d y : ℚ)
    (hay : a < y) (hyb : y < b) (hcy : c < y) (hyd : y < d) :
    phi ((chordX a b y + chordX c d y) / 2, y) < 0 := by
  have h1 := mul_pos (sub_pos.mpr hay) (sub_pos.mpr hyb)
  have h2 := mul_pos (sub_pos.mpr hcy) (sub_pos.mpr hyd)
  have he : phi ((chordX a b y + chordX c d y) / 2, y) =
      (phi (chordX a b y, y) + phi (chordX c d y, y)) / 2 := by
    unfold phi
    ring
  rw [he, phi_chord, phi_chord]
  linarith

def perturb (p : Point) (dx dy : ℚ) : Point := (p.1 + dx, p.2 + dy)

/-- The paper's prescribed coordinatewise perturbation bound preserves strict
inwardness. The argument is uniform over every prototype in the height box. -/
theorem perturbation_inside (p : Point) (eta delta dx dy : ℚ)
    (heta : 0 < eta) (hp : phi p ≤ -eta)
    (hpy : |p.2| ≤ 2) (hdelta : 0 ≤ delta) (hquarter : delta ≤ 1 / 4)
    (hmargin : delta ≤ eta / 8) (hdx : |dx| ≤ delta) (hdy : |dy| ≤ delta) :
    phi (perturb p dx dy) < 0 := by
  have hprod : |p.2 * dy| ≤ 2 * delta := by
    rw [abs_mul]
    exact mul_le_mul hpy hdy (abs_nonneg dy) (by norm_num)
  have hprod' : p.2 * dy ≤ 2 * delta := le_trans (le_abs_self _) hprod
  have hdx' : dx ≤ delta := le_trans (le_abs_self _) hdx
  have hdy' : -delta ≤ dy ∧ dy ≤ delta := abs_le.mp hdy
  have hdysq : dy ^ 2 ≤ delta ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ delta - dy)
      (by linarith : 0 ≤ delta + dy)]
  have hdeltasq : delta ^ 2 ≤ delta / 4 := by
    nlinarith [mul_nonneg hdelta (by linarith : 0 ≤ 1 / 4 - delta)]
  have he : phi (perturb p dx dy) = phi p + dx + (2 * p.2 * dy + dy ^ 2) / 100 := by
    unfold phi perturb
    ring
  rw [he]
  linarith

/-- Endpoint tags record actual edge identities in the complete drawing. -/
inductive Vertex where
  | original : ℚ → Vertex
  | frame : ℚ → Vertex
  | program : Point → Vertex

def Vertex.point : Vertex → Point
  | .original a => Q4.Candidate.ConvexSeparation.original a
  | .frame t => Q4.Candidate.ConvexSeparation.frame t
  | .program p => p

def Vertex.valid : Vertex → Prop
  | .original a => -1 ≤ a ∧ a ≤ 1
  | .frame t => -1 ≤ t ∧ t ≤ 1
  | .program p => phi p < 0 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2

def Vertex.isFrame : Vertex → Bool
  | .frame _ => true
  | _ => false

theorem ordinary_valid (a mu : ℚ) (ha : -1 ≤ a) (ha' : a ≤ 1)
    (hmu : 0 < mu) (hmu' : mu ≤ 1) :
    (Vertex.program (ordinary a mu)).valid :=
  ⟨ordinary_inside a mu ha ha' hmu hmu',
    ordinary_height a mu ha ha' (le_of_lt hmu) hmu'⟩

theorem rank_midpoint_valid (a b c d y : ℚ)
    (hay : a < y) (hyb : y < b) (hcy : c < y) (hyd : y < d)
    (ha : -1 ≤ a) (hb : b ≤ 1) :
    (Vertex.program ((chordX a b y + chordX c d y) / 2, y)).valid := by
  refine ⟨rank_midpoint_inside a b c d y hay hyb hcy hyd, ?_, ?_⟩ <;> dsimp <;> linarith

inductive EdgeKind where
  | X | T | C | Y | I
  deriving DecidableEq

/-- Five exhaustive classes of all point-pair edges. No omission of completion
edges is made by this classification; loops, if supplied, simply cannot cross. -/
def edgeKind : Vertex → Vertex → EdgeKind
  | .frame _, .frame _ => .I
  | .original _, .frame _ | .frame _, .original _ => .X
  | .program _, .frame _ | .frame _, .program _ => .T
  | .original _, .original _ => .C
  | _, _ => .Y

theorem nonframe_region (v : Vertex) (hv : v.valid) (hn : v.isFrame = false) :
    phi v.point ≤ 0 ∧ -2 ≤ v.point.2 ∧ v.point.2 ≤ 2 := by
  cases v with
  | original a =>
      simp only [Vertex.point, Vertex.valid] at hv ⊢
      refine ⟨le_of_eq (phi_original a), ?_, ?_⟩ <;> dsimp [original] <;> linarith [hv.1, hv.2]
  | frame t => simp [Vertex.isFrame] at hn
  | program p => exact ⟨le_of_lt hv.1, hv.2⟩

/-- X is separated from every actual C or Y edge in the complete drawing. -/
theorem X_no_cross_C_or_Y (a t : ℚ) (v w : Vertex)
    (ha : -1 ≤ a) (ha' : a ≤ 1) (hv : v.valid) (hw : w.valid)
    (hk : edgeKind v w = .C ∨ edgeKind v w = .Y) :
    ¬ ProperCross (original a) (frame t) v.point w.point := by
  have hn : v.isFrame = false ∧ w.isFrame = false := by
    cases v <;> cases w <;> simp_all [edgeKind, Vertex.isFrame]
  exact original_frame_no_cross_inside a t _ _ ha ha'
    (nonframe_region v hv hn.1).1 (nonframe_region w hw hn.2).1

/-- I has no crossing-graph neighbor outside I, with edge classes derived
from concrete endpoints rather than supplied as zero-crossing hypotheses. -/
theorem I_isolated (u v : ℚ) (a b : Vertex) (ha : a.valid) (hb : b.valid)
    (hk : edgeKind a b ≠ .I) :
    ¬ ProperCross a.point b.point (frame u) (frame v) := by
  by_cases haf : a.isFrame = true
  · cases a with
    | original x => simp [Vertex.isFrame] at haf
    | program p => simp [Vertex.isFrame] at haf
    | frame t =>
      have hbn : b.isFrame = false := by
        cases b <;> simp_all [edgeKind, Vertex.isFrame]
      have hr := nonframe_region b hb hbn
      exact frame_fan_no_cross_I t u v b.point ha.1 ha.2 hr.1 hr.2.1 hr.2.2
  · have han : a.isFrame = false := Bool.eq_false_iff.mpr haf
    have har := nonframe_region a ha han
    by_cases hbf : b.isFrame = true
    · cases b with
      | original x => simp [Vertex.isFrame] at hbf
      | program p => simp [Vertex.isFrame] at hbf
      | frame t =>
        intro hc
        exact frame_fan_no_cross_I t u v a.point hb.1 hb.2 har.1 har.2.1 har.2.2
          ((properCross_reverse_first a.point (frame t) (frame u) (frame v)).mp hc)
    · have hbn : b.isFrame = false := Bool.eq_false_iff.mpr hbf
      exact nonframe_no_cross_I a.point b.point u v har.1 (nonframe_region b hb hbn).1

end Q4.Candidate.ConvexSeparation

#print axioms Q4.Candidate.ConvexSeparation.properCross_has_open_intersection
#print axioms Q4.Candidate.ConvexSeparation.properCross_fromInt
#print axioms Q4.Candidate.ConvexSeparation.original_frame_no_cross_inside
#print axioms Q4.Candidate.ConvexSeparation.X_C_zero
#print axioms Q4.Candidate.ConvexSeparation.frame_fan_no_cross_I
#print axioms Q4.Candidate.ConvexSeparation.nonframe_no_cross_I
#print axioms Q4.Candidate.ConvexSeparation.ordinary_inside
#print axioms Q4.Candidate.ConvexSeparation.ordinary_valid
#print axioms Q4.Candidate.ConvexSeparation.rank_midpoint_inside
#print axioms Q4.Candidate.ConvexSeparation.rank_midpoint_valid
#print axioms Q4.Candidate.ConvexSeparation.perturbation_inside
#print axioms Q4.Candidate.ConvexSeparation.X_no_cross_C_or_Y
#print axioms Q4.Candidate.ConvexSeparation.I_isolated
