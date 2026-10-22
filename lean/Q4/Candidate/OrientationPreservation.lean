import Q4.Candidate.UniformInsertion
import Mathlib.Data.Finset.Max

/-!
One common rational radius preserves every nonzero one-program orientation
against fixed base pairs. The minimum is constructed from the actual finite
determinant list; its positivity is proved, not assumed. Crossing preservation
is for genuine proper segment crossings, including shared base endpoints.
An unrelated zero prototype determinant is deliberately not claimed stable.
The final theorem combines these signs with the fixed-grid batch insertion.
Binary bit-length bounds and the manuscript's dyadic rounding are separate.
-/

namespace Q4.Candidate.OrientationPreservation

open Q4.Candidate.ConvexSeparation Q4.Candidate.UniformInsertion

def SameSigns (x y : ℚ) : Prop := (x < 0 ↔ y < 0) ∧ (0 < x ↔ 0 < y)

theorem sameSigns_of_close (x y eta : ℚ) (heta : 0 < eta)
    (hmargin : eta ≤ |y|) (hclose : |x-y| < eta) : SameSigns x y := by
  have hc := abs_lt.mp hclose
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [abs_of_neg hy] at hmargin
    have hx : x < 0 := by linarith
    exact ⟨by simp [hx,hy], by simp [not_lt_of_ge (le_of_lt hx), not_lt_of_ge (le_of_lt hy)]⟩
  · subst y
    norm_num at hmargin
    linarith
  · rw [abs_of_pos hy] at hmargin
    have hx : 0 < x := by linarith
    exact ⟨by simp [not_lt_of_ge (le_of_lt hx), not_lt_of_ge (le_of_lt hy)], by simp [hx,hy]⟩

theorem sameSigns_mul_neg (x y x' y' : ℚ)
    (hx : SameSigns x x') (hy : SameSigns y y') :
    x*y < 0 ↔ x'*y' < 0 := by
  rw [mul_neg_iff, mul_neg_iff]
  exact or_congr (and_congr hx.2 hy.1) (and_congr hx.1 hy.2)

theorem orient_change (a b r p : Point) :
    orient a b p-orient a b r =
      (b.1-a.1)*(p.2-r.2) - (b.2-a.2)*(p.1-r.1) := by
  unfold orient
  ring

theorem orient_change_bound (a b r p : Point) (delta : ℚ)
    (hx : |p.1-r.1| ≤ delta) (hy : |p.2-r.2| ≤ delta) :
    |orient a b p-orient a b r| ≤ (|b.1-a.1|+|b.2-a.2|)*delta := by
  rw [orient_change]
  calc
    _ ≤ |(b.1-a.1)*(p.2-r.2)| + |(b.2-a.2)*(p.1-r.1)| := abs_sub _ _
    _ = |b.1-a.1| * |p.2-r.2| + |b.2-a.2| * |p.1-r.1| := by rw [abs_mul,abs_mul]
    _ ≤ |b.1-a.1| * delta + |b.2-a.2| * delta :=
      add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
    _ = _ := by ring

def baseBudget (B : Finset Point) : ℚ := 1 + 2*∑ a ∈ B, (|a.1|+|a.2|)

theorem baseBudget_positive (B : Finset Point) : 0 < baseBudget B := by
  have hs : 0 ≤ ∑ a ∈ B, (|a.1|+|a.2|) :=
    Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  unfold baseBudget
  linarith

theorem base_pair_budget (B : Finset Point) (a b : Point) (ha : a ∈ B) (hb : b ∈ B) :
    |b.1-a.1|+|b.2-a.2| < baseBudget B := by
  have hs (c : Point) (hc : c ∈ B) : |c.1|+|c.2| ≤ ∑ a ∈ B, (|a.1|+|a.2|) :=
    Finset.single_le_sum (fun (a : Point) _ => add_nonneg (abs_nonneg a.1) (abs_nonneg a.2)) hc
  have hx := abs_sub b.1 a.1
  have hy := abs_sub b.2 a.2
  unfold baseBudget
  linarith [hs a ha, hs b hb]

def determinantValues (B R : Finset Point) : Finset ℚ :=
  ((B ×ˢ B) ×ˢ R).image (fun abr => orient abr.1.1 abr.1.2 abr.2)

def positiveMargins (B R : Finset Point) : Finset ℚ :=
  insert 1 (((determinantValues B R).filter (fun x => x ≠ 0)).image abs)

def orientationMargin (B R : Finset Point) : ℚ :=
  (positiveMargins B R).min' (Finset.insert_nonempty _ _)

theorem orientationMargin_positive (B R : Finset Point) : 0 < orientationMargin B R := by
  unfold orientationMargin
  have hm := Finset.min'_mem (positiveMargins B R) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with hm | hm
  · simpa only [hm] using (show (0:ℚ) < 1 by norm_num)
  · obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hm
    rw [← he]
    exact abs_pos.mpr (Finset.mem_filter.mp hv).2

theorem orientationMargin_le (B R : Finset Point) (a b r : Point)
    (ha : a ∈ B) (hb : b ∈ B) (hr : r ∈ R) (hnz : orient a b r ≠ 0) :
    orientationMargin B R ≤ |orient a b r| := by
  unfold orientationMargin
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨orient a b r, Finset.mem_filter.mpr ⟨?_,hnz⟩,rfl⟩
  exact Finset.mem_image.mpr ⟨((a,b),r),Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hr⟩,rfl⟩

def orientationRadius (B R : Finset Point) : ℚ := orientationMargin B R/(8*baseBudget B)

theorem orientationRadius_positive (B R : Finset Point) : 0 < orientationRadius B R :=
  div_pos (orientationMargin_positive B R) (mul_pos (by norm_num) (baseBudget_positive B))

theorem fixed_base_orientation_preserved (B R : Finset Point) (a b r p : Point)
    (ha : a ∈ B) (hb : b ∈ B) (hr : r ∈ R) (hnz : orient a b r ≠ 0)
    (delta : ℚ) (hd : 0 < delta) (hdr : delta ≤ orientationRadius B R)
    (hx : |p.1-r.1| ≤ delta) (hy : |p.2-r.2| ≤ delta) :
    SameSigns (orient a b p) (orient a b r) := by
  have hb0 := baseBudget_positive B
  have he0 := orientationMargin_positive B R
  have hscale : 8*baseBudget B*delta ≤ orientationMargin B R := by
    dsimp [orientationRadius] at hdr
    nlinarith [((le_div_iff₀ (show 0 < 8*baseBudget B by positivity)).mp hdr)]
  apply sameSigns_of_close _ _ (orientationMargin B R) he0 (orientationMargin_le B R a b r ha hb hr hnz)
  have hbd := orient_change_bound a b r p delta hx hy
  have hpair := mul_lt_mul_of_pos_right (base_pair_budget B a b ha hb) hd
  nlinarith

/-- A zero caused by equal fixed endpoints stays zero. Other zero prototype
determinants are excluded only at the use site, not deleted from the geometry. -/
theorem fixed_base_orientation_preserved_or_equal (B R : Finset Point) (a b r p : Point)
    (ha : a ∈ B) (hb : b ∈ B) (hr : r ∈ R)
    (hstable : orient a b r ≠ 0 ∨ a = b)
    (delta : ℚ) (hd : 0 < delta) (hdr : delta ≤ orientationRadius B R)
    (hx : |p.1-r.1| ≤ delta) (hy : |p.2-r.2| ≤ delta) :
    SameSigns (orient a b p) (orient a b r) := by
  rcases hstable with hnz | rfl
  · exact fixed_base_orientation_preserved B R a b r p ha hb hr hnz delta hd hdr hx hy
  · simp [SameSigns,orient]

/-- Every proper crossing with precisely one moved program endpoint is
preserved whenever its three relevant base-pair determinants are nonzero
(or identically zero from a repeated base endpoint). -/
theorem one_program_crossing_preserved (B R : Finset Point) (a b c r p : Point)
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (hr : r ∈ R)
    (hab : orient a b r ≠ 0 ∨ a = b) (hac : orient a c r ≠ 0 ∨ a = c)
    (hbc : orient b c r ≠ 0 ∨ b = c)
    (delta : ℚ) (hd : 0 < delta) (hdr : delta ≤ orientationRadius B R)
    (hx : |p.1-r.1| ≤ delta) (hy : |p.2-r.2| ≤ delta) :
    ProperCross p a b c ↔ ProperCross r a b c := by
  have h1 := fixed_base_orientation_preserved_or_equal B R a b r p ha hb hr hab delta hd hdr hx hy
  have h2 := fixed_base_orientation_preserved_or_equal B R a c r p ha hc hr hac delta hd hdr hx hy
  have h3 := fixed_base_orientation_preserved_or_equal B R b c r p hb hc hr hbc delta hd hdr hx hy
  have h4 : SameSigns (orient b c a) (orient b c a) := ⟨Iff.rfl,Iff.rfl⟩
  unfold ProperCross
  rw [orient_cycle p a b,orient_cycle p a c,orient_cycle r a b,orient_cycle r a c]
  exact and_congr (sameSigns_mul_neg _ _ _ _ h1 h2) (sameSigns_mul_neg _ _ _ _ h3 h4)

def finiteMargin (R : Finset Point) (f : Point → ℚ) : ℚ :=
  (insert 1 (R.image f)).min' (Finset.insert_nonempty _ _)

theorem finiteMargin_positive (R : Finset Point) (f : Point → ℚ)
    (hf : ∀ r ∈ R, 0 < f r) : 0 < finiteMargin R f := by
  unfold finiteMargin
  have hm := Finset.min'_mem (insert 1 (R.image f)) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with hm | hm
  · rw [hm]; norm_num
  · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hm
    rw [← he]
    exact hf r hr

theorem finiteMargin_le (R : Finset Point) (f : Point → ℚ) (r : Point) (hr : r ∈ R) :
    finiteMargin R f ≤ f r := by
  unfold finiteMargin
  exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩))

def capMargin (R : Finset Point) : ℚ := finiteMargin R (fun r => -phi r)
def heightMargin (R : Finset Point) : ℚ := finiteMargin R (fun r => 2-|r.2|)

/-- A single exact rational radius, fixed before any copy is inserted. The
three actual finite minima pay for cap, height, and orientation preservation. -/
def constructionRadius (B R : Finset Point) : ℚ :=
  min (1/4) (min (capMargin R/8) (min (heightMargin R) (orientationRadius B R)))

theorem constructionRadius_positive (B R : Finset Point)
    (hproto : ∀ r ∈ R, phi r < 0 ∧ |r.2| < 2) : 0 < constructionRadius B R := by
  have hc : 0 < capMargin R := finiteMargin_positive R _ (by intro r hr; exact neg_pos.mpr (hproto r hr).1)
  have hh : 0 < heightMargin R := finiteMargin_positive R _ (by intro r hr; exact sub_pos.mpr (hproto r hr).2)
  unfold constructionRadius
  exact lt_min (by norm_num) (lt_min (div_pos hc (by norm_num))
    (lt_min hh (orientationRadius_positive B R)))

theorem constructionRadius_bounds (B R : Finset Point) :
    constructionRadius B R ≤ 1/4 ∧ constructionRadius B R ≤ capMargin R/8 ∧
    constructionRadius B R ≤ heightMargin R ∧ constructionRadius B R ≤ orientationRadius B R := by
  unfold constructionRadius
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

def TablesPreserved (B : Finset Point) (r p : Point) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B,
    (orient a b r ≠ 0 ∨ a = b) → (orient a c r ≠ 0 ∨ a = c) →
    (orient b c r ≠ 0 ∨ b = c) → (ProperCross p a b c ↔ ProperCross r a b c)

/-- The exact, common construction radius gives joint general position and
preserves every applicable one-program crossing table for every inserted copy.
Only strict prototype cap/height conditions and initial base GP are inputs;
neither a nonzero numerical margin nor a small-enough radius is postulated. -/
theorem batch_insertion_preserving_tables (M : ℕ) (B : Finset Point) (rs : List Point)
    (hsize : B.card+rs.length ≤ M) (hgp : GeneralPosition B)
    (hproto : ∀ r ∈ rs, phi r < 0 ∧ |r.2| < 2) :
    let delta := constructionRadius B rs.toFinset
    0 < delta ∧ ∃ ps : List Point,
      ps.length = rs.length ∧ ps.Nodup ∧ (∀ p ∈ ps, p ∉ B) ∧
      GeneralPosition (B ∪ ps.toFinset) ∧ List.Forall₂ (Placed M delta) rs ps ∧
      (∀ r ∈ rs, ∀ p, Placed M delta r p → TablesPreserved B r p) := by
  dsimp only
  let R := rs.toFinset
  let delta := constructionRadius B R
  have hpr : ∀ r ∈ R, phi r < 0 ∧ |r.2| < 2 := by
    intro r hr
    exact hproto r (List.mem_toFinset.mp hr)
  have hd : 0 < delta := constructionRadius_positive B R hpr
  have hc : 0 < capMargin R := finiteMargin_positive R _ (by intro r hr; exact neg_pos.mpr (hpr r hr).1)
  have hb := constructionRadius_bounds B R
  have hmargin : ∀ r ∈ rs, phi r ≤ -capMargin R ∧ |r.2|+delta/2 ≤ 2 := by
    intro r hr
    have hrR : r ∈ R := List.mem_toFinset.mpr hr
    have hcap := finiteMargin_le R (fun r => -phi r) r hrR
    have hheight := finiteMargin_le R (fun r => 2-|r.2|) r hrR
    change capMargin R ≤ -phi r at hcap
    change heightMargin R ≤ 2-|r.2| at hheight
    dsimp [delta]
    constructor <;> linarith [hb.2.2.1]
  obtain ⟨ps,hlen,hnd,hout,hgp',hplaced⟩ := batch_program_insertion M B rs hsize hgp
    (capMargin R) delta hc hd hb.1 hb.2.1 hmargin
  refine ⟨hd, ps,hlen,hnd,hout,hgp',hplaced,?_⟩
  intro r hr p hp a ha b hb' c hc' hab hac hbc
  have hbox := placed_in_box M delta hd r p hp
  exact one_program_crossing_preserved B R a b c r p ha hb' hc'
    (List.mem_toFinset.mpr hr) hab hac hbc delta hd hb.2.2.2
    (by linarith [hbox.1]) (by linarith [hbox.2])

/-- For the actual two-cap bases, initial general position is already proved.
This specializes the complete batch construction to the paper's base geometry. -/
theorem double_cap_batch_insertion (M : ℕ) (ys ts : Finset ℚ) (rs : List Point)
    (hsize : ys.card+ts.card+rs.length ≤ M)
    (hys : ∀ a ∈ ys, |a| ≤ 1) (hts : ∀ t ∈ ts, |t| ≤ 1)
    (hproto : ∀ r ∈ rs, phi r < 0 ∧ |r.2| < 2) :
    let B := Q4.Candidate.DoubleCapGrid.basePoints ys ts
    let delta := constructionRadius B rs.toFinset
    0 < delta ∧ ∃ ps : List Point,
      ps.length = rs.length ∧ ps.Nodup ∧ (∀ p ∈ ps, p ∉ B) ∧
      GeneralPosition (B ∪ ps.toFinset) ∧ List.Forall₂ (Placed M delta) rs ps ∧
      (∀ r ∈ rs, ∀ p, Placed M delta r p → TablesPreserved B r p) := by
  apply batch_insertion_preserving_tables
  · simpa only [Q4.Candidate.DoubleCapGrid.base_card] using hsize
  · exact Q4.Candidate.DoubleCapGrid.base_general_position ys ts hys hts
  · exact hproto

end Q4.Candidate.OrientationPreservation

#print axioms Q4.Candidate.OrientationPreservation.orient_change_bound
#print axioms Q4.Candidate.OrientationPreservation.orientationMargin_positive
#print axioms Q4.Candidate.OrientationPreservation.fixed_base_orientation_preserved
#print axioms Q4.Candidate.OrientationPreservation.one_program_crossing_preserved
#print axioms Q4.Candidate.OrientationPreservation.constructionRadius_positive
#print axioms Q4.Candidate.OrientationPreservation.batch_insertion_preserving_tables
#print axioms Q4.Candidate.OrientationPreservation.double_cap_batch_insertion
