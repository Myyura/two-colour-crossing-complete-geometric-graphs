import Q4.Candidate.DoubleCapGrid

/-!
Actual rational-coordinate ordinary-program fan tables. Both strict endpoint
tests in ProperCross are retained. Numerical prototype/clone margins are
kept explicit; no abstract crossing table is an input to the final theorems.
-/

namespace Q4.Candidate.OrdinaryFan

open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid

def frameSide (t u : ℚ) (r : Point) : ℚ :=
  1 + ((t + u) * r.2 - t * u) / 100 - r.1

theorem frame_side_orientation (t u : ℚ) (r : Point) :
    orient (frame t) (frame u) r = (u-t) * frameSide t u r := by
  unfold orient frame frameSide
  ring

theorem frameSide_positive (t u : ℚ) (r : Point)
    (ht : |t| ≤ 1) (hu : |u| ≤ 1) (hr : (Vertex.program r).valid) :
    0 < frameSide t u r := by
  have hx := phi_nonpos_x_bound r (le_of_lt hr.1)
  have hy : |r.2| ≤ 2 := abs_le.mpr hr.2
  have hty : |t*r.2| ≤ 2 := by
    rw [abs_mul]
    simpa using mul_le_mul ht hy (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 1)
  have huy : |u*r.2| ≤ 2 := by
    rw [abs_mul]
    simpa using mul_le_mul hu hy (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 1)
  have htu : |t*u| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul ht hu (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 1)
  have hty' := (abs_le.mp hty).1
  have huy' := (abs_le.mp huy).1
  have htu' := (abs_le.mp htu).2
  unfold frameSide
  nlinarith

/-- The full geometric epsilon test (4.5), with actual frame-side separation
proved from the cap/height conditions rather than assumed crossing behavior. -/
theorem fan_crossing_epsilon (r : Point) (a ti tk : ℚ)
    (hr : (Vertex.program r).valid)
    (hi : |ti| ≤ 1) (hk : |tk| ≤ 1) :
    ProperCross r (frame tk) (original a) (frame ti) ↔
      (tk < ti ∧ 0 < orient r (original a) (frame ti) ∧
        0 < orient r (original a) (frame tk)) ∨
      (ti < tk ∧ orient r (original a) (frame ti) < 0 ∧
        orient r (original a) (frame tk) < 0) := by
  have hR := frameSide_positive tk ti r hk hi hr
  have hP := bridge_positive ti tk a hi hk
  have h1 : orient r (frame tk) (original a) = -orient r (original a) (frame tk) :=
    orient_reverse_last _ _ _
  have h2 : orient r (frame tk) (frame ti) = (ti-tk) * frameSide tk ti r := by
    rw [orient_cycle, frame_side_orientation]
  have h3 : orient (original a) (frame ti) r = orient r (original a) (frame ti) := by
    rw [orient_cycle, orient_cycle]
  have h4 : orient (original a) (frame ti) (frame tk) = (tk-ti) * bridge ti tk a :=
    fan_orientation_frame _ _ _
  unfold ProperCross
  rw [h1,h2,h3,h4]
  have hfirst : -orient r (original a) (frame tk) * ((ti-tk)*frameSide tk ti r) < 0 ↔
      0 < orient r (original a) (frame tk) * (ti-tk) := by
    have he : -orient r (original a) (frame tk) * ((ti-tk)*frameSide tk ti r) =
      -(orient r (original a) (frame tk) * (ti-tk)) * frameSide tk ti r := by ring
    rw [he, mul_neg_iff]
    constructor
    · rintro (⟨h,_⟩|⟨_,h⟩) <;> linarith
    · intro h; exact Or.inr ⟨by linarith,hR⟩
  have hsecond : orient r (original a) (frame ti) * ((tk-ti)*bridge ti tk a) < 0 ↔
      0 < orient r (original a) (frame ti) * (ti-tk) := by
    have he : orient r (original a) (frame ti) * ((tk-ti)*bridge ti tk a) =
      -(orient r (original a) (frame ti) * (ti-tk)) * bridge ti tk a := by ring
    rw [he, mul_neg_iff]
    constructor
    · rintro (⟨h,_⟩|⟨_,h⟩) <;> linarith
    · intro h; exact Or.inr ⟨by linarith,hP⟩
  rw [hfirst,hsecond]
  rcases lt_trichotomy ti tk with hlt | heq | hgt
  · have hd : ti-tk < 0 := sub_neg.mpr hlt
    rw [mul_pos_iff,mul_pos_iff]
    constructor
    · rintro ⟨h1,h2⟩
      have he1 : orient r (original a) (frame tk) < 0 := by rcases h1 with h|h <;> linarith [h.1,h.2]
      have he2 : orient r (original a) (frame ti) < 0 := by rcases h2 with h|h <;> linarith [h.1,h.2]
      exact Or.inr ⟨hlt,he2,he1⟩
    · rintro (⟨h,_,_⟩|⟨_,hi',hk'⟩)
      · linarith
      · exact ⟨Or.inr ⟨hk',hd⟩,Or.inr ⟨hi',hd⟩⟩
  · subst tk; simp
  · have hd : 0 < ti-tk := sub_pos.mpr hgt
    rw [mul_pos_iff,mul_pos_iff]
    constructor
    · rintro ⟨h1,h2⟩
      have he1 : 0 < orient r (original a) (frame tk) := by rcases h1 with h|h <;> linarith [h.1,h.2]
      have he2 : 0 < orient r (original a) (frame ti) := by rcases h2 with h|h <;> linarith [h.1,h.2]
      exact Or.inl ⟨hgt,he2,he1⟩
    · rintro (⟨_,hi',hk'⟩|⟨h,_,_⟩)
      · exact ⟨Or.inl ⟨hk',hd⟩,Or.inl ⟨hi',hd⟩⟩
      · linarith

theorem ordinary_parent_orientation (a mu t : ℚ) :
    orient (ordinary a mu) (original a) (frame t) = mu * t * bridge 0 t a := by
  unfold orient ordinary mix original frame bridge
  ring

theorem ordinary_parent_sign (a mu t : ℚ) (hmu : 0 < mu) (ht : |t| ≤ 1) :
    (0 < orient (ordinary a mu) (original a) (frame t) ↔ 0 < t) ∧
    (orient (ordinary a mu) (original a) (frame t) < 0 ↔ t < 0) := by
  have hb := bridge_positive 0 t a (by norm_num) ht
  have hf : 0 < mu * bridge 0 t a := mul_pos hmu hb
  have he : orient (ordinary a mu) (original a) (frame t) = t * (mu * bridge 0 t a) := by
    rw [ordinary_parent_orientation]; ring
  rw [he]
  exact ⟨by simpa using (mul_pos_iff_of_pos_right hf), by simpa using (mul_lt_mul_iff_of_pos_right hf : t * (mu * bridge 0 t a) < 0 * (mu * bridge 0 t a) ↔ t < 0)⟩

/-- Exact parent-macro version of the ordinary prefix/suffix table. The whole
prefix/suffix is retained; it is not truncated at the central frame gap. -/
theorem ordinary_parent_crossing (a mu ti tk : ℚ) (ha : |a| ≤ 1)
    (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hi : |ti| ≤ 1) (hk : |tk| ≤ 1) :
    ProperCross (ordinary a mu) (frame tk) (original a) (frame ti) ↔
      (tk < ti ∧ 0 < tk) ∨ (ti < tk ∧ tk < 0) := by
  have hr := ordinary_valid a mu (abs_le.mp ha).1 (abs_le.mp ha).2 hmu hmu1
  rw [fan_crossing_epsilon _ a ti tk hr hi hk,
    (ordinary_parent_sign a mu ti hmu hi).1,(ordinary_parent_sign a mu tk hmu hk).1,
    (ordinary_parent_sign a mu ti hmu hi).2,(ordinary_parent_sign a mu tk hmu hk).2]
  constructor
  · rintro (⟨h,_,hk'⟩|⟨h,_,hk'⟩)
    · exact Or.inl ⟨h,hk'⟩
    · exact Or.inr ⟨h,hk'⟩
  · rintro (⟨h,hk'⟩|⟨h,hk'⟩)
    · exact Or.inl ⟨h,lt_trans hk' h,hk'⟩
    · exact Or.inr ⟨h,lt_trans h hk',hk'⟩

theorem frameParameter_half_sign (B : ℕ) (hB : Even B) (i : Fin B) :
    (0 < frameParameter B i ↔ i.val < B / 2) ∧
    (frameParameter B i < 0 ↔ B / 2 ≤ i.val) := by
  obtain ⟨b,hb⟩ := hB
  have hd : (0:ℚ) < (B:ℚ)+1 := by positivity
  have hp : 0 < frameParameter B i ↔ 2 * (i.val+1) < B+1 := by
    unfold frameParameter
    have hh := (div_lt_one hd : 2*((i.val:ℚ)+1)/((B:ℚ)+1) < 1 ↔ _)
    constructor
    · intro h
      have hh' := hh.mp (by linarith)
      exact_mod_cast hh'
    · intro h
      have hh' : (2:ℚ)*((i.val:ℚ)+1) < (B:ℚ)+1 := by exact_mod_cast h
      linarith [hh.mpr hh']
  have hn : frameParameter B i < 0 ↔ B+1 < 2 * (i.val+1) := by
    unfold frameParameter
    have hh := (one_lt_div hd : 1 < 2*((i.val:ℚ)+1)/((B:ℚ)+1) ↔ _)
    constructor
    · intro h
      have hh' := hh.mp (by linarith)
      exact_mod_cast hh'
    · intro h
      have hh' : (B:ℚ)+1 < (2:ℚ)*((i.val:ℚ)+1) := by exact_mod_cast h
      linarith [hh.mpr hh']
  rw [hp,hn]
  omega

/-- Actual zero-based frame indices, with an even frame count. The manuscript
uses a multiple of eight, so this assumption is strictly weaker. -/
theorem ordinary_parent_indexed (B : ℕ) (hB : Even B) (i k : Fin B)
    (a mu : ℚ) (ha : |a| ≤ 1) (hmu : 0 < mu) (hmu1 : mu ≤ 1) :
    ProperCross (ordinary a mu) (frame (frameParameter B k))
      (original a) (frame (frameParameter B i)) ↔
      (i < k ∧ k.val < B/2) ∨ (k < i ∧ B/2 ≤ k.val) := by
  rw [ordinary_parent_crossing a mu _ _ ha hmu hmu1
    (le_of_lt (frameParameter_unit B i)) (le_of_lt (frameParameter_unit B k)),
    (frameParameter_antitone B).lt_iff_gt,(frameParameter_antitone B).lt_iff_gt,
    (frameParameter_half_sign B hB k).1,(frameParameter_half_sign B hB k).2]

theorem ordinary_x_bound (a mu : ℚ) (ha : |a| ≤ 1) (hm : 0 ≤ mu) (hm1 : mu ≤ 1) :
    |(ordinary a mu).1| ≤ 22 := by
  have haa := unit_square_bound a (abs_le.mp ha).1 (abs_le.mp ha).2
  have hprod : mu*a^2 ≤ 1 := by
    calc
      mu*a^2 ≤ 1*a^2 := mul_le_mul_of_nonneg_right hm1 (sq_nonneg _)
      _ ≤ 1 := by linarith
  have hprod0 := mul_nonneg hm (sq_nonneg a)
  rw [abs_le]
  unfold ordinary mix original frame
  constructor <;> nlinarith [sq_nonneg a]

theorem parent_bridge_lower (a t : ℚ) (ht : |t| ≤ 1) : 10 ≤ bridge 0 t a := by
  have ht2 := unit_square_bound t (abs_le.mp ht).1 (abs_le.mp ht).2
  unfold bridge
  nlinarith [sq_nonneg (2*a+t)]

/-- Actual determinant sensitivity when a parent original parameter is cloned.
The estimate is uniform throughout the stated rational boxes. -/
theorem original_parameter_lipschitz (r : Point) (a b t : ℚ)
    (hx : |r.1| ≤ 22) (hy : |r.2| ≤ 2)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1) :
    |orient r (original b) (frame t) - orient r (original a) (frame t)| ≤
      25 * |b-a| := by
  have ht2 := unit_square_bound t (abs_le.mp ht).1 (abs_le.mp ht).2
  have hfx : |(frame t).1| ≤ 2 := by
    unfold frame
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg t]
  have hxd : |r.1-(frame t).1| ≤ 24 :=
    by
    have hh := abs_sub_le r.1 0 (frame t).1
    simp only [sub_zero,zero_sub,abs_neg] at hh
    linarith
  have hab : |a+b| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hty : |t-r.2| ≤ 3 := by
    have hh := abs_sub_le t 0 r.2
    simp only [sub_zero,zero_sub,abs_neg] at hh
    linarith
  have hmul : |(a+b)*(t-r.2)/100| ≤ 6/100 := by
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℚ)<100)]
    exact div_le_div_of_nonneg_right
      (by nlinarith [mul_le_mul hab hty (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 2)]) (by norm_num)
  have hcoef : |r.1-(frame t).1-(a+b)*(t-r.2)/100| ≤ 25 :=
    by
    have hh := abs_sub_le (r.1-(frame t).1) 0 ((a+b)*(t-r.2)/100)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    linarith
  have he : orient r (original b) (frame t) - orient r (original a) (frame t) =
      (b-a)*(r.1-(frame t).1-(a+b)*(t-r.2)/100) := by
    unfold orient original frame
    ring
  rw [he,abs_mul]
  calc
    _ ≤ |b-a| * 25 := mul_le_mul_of_nonneg_left hcoef (abs_nonneg _)
    _ = _ := by ring

/-- Explicit finite clone margin preserving the parent ray signs. This is a
numerical coordinate condition, not a sign or crossing-table hypothesis. -/
theorem ordinary_clone_sign (a b mu t : ℚ) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hm : 0 < mu) (hm1 : mu ≤ 1) (ht : |t| ≤ 1) (ht0 : t ≠ 0)
    (hclone : 3*|b-a| ≤ mu*|t|) :
    (0 < orient (ordinary a mu) (original b) (frame t) ↔ 0 < t) ∧
    (orient (ordinary a mu) (original b) (frame t) < 0 ↔ t < 0) := by
  have hy := ordinary_height a mu (abs_le.mp ha).1 (abs_le.mp ha).2 (le_of_lt hm) hm1
  have he := original_parameter_lipschitz (ordinary a mu) a b t
    (ordinary_x_bound a mu ha (le_of_lt hm) hm1) (abs_le.mpr hy) ha hb ht
  have herr := abs_le.mp he
  have hbridge := parent_bridge_lower a t ht
  have hbase := ordinary_parent_orientation a mu t
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · rw [abs_of_neg htneg] at hclone
    have hp : 0 < mu*(-t) := mul_pos hm (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hbridge (le_of_lt hp)
    have hsign : orient (ordinary a mu) (original b) (frame t) < 0 := by
      nlinarith [herr.1,herr.2,abs_nonneg (b-a)]
    exact ⟨by constructor <;> intro h <;> linarith,
      by constructor <;> intro _ <;> assumption⟩
  · rw [abs_of_pos htpos] at hclone
    have hp : 0 < mu*t := mul_pos hm htpos
    have hmul := mul_le_mul_of_nonneg_left hbridge (le_of_lt hp)
    have hsign : 0 < orient (ordinary a mu) (original b) (frame t) := by
      nlinarith [herr.1,herr.2,abs_nonneg (b-a)]
    exact ⟨by constructor <;> intro _ <;> assumption,
      by constructor <;> intro h <;> linarith⟩

theorem frameParameter_gap (B : ℕ) (hB : Even B) (i : Fin B) :
    1 ≤ ((B:ℚ)+1)*|frameParameter B i| := by
  have hd : (B:ℚ)+1 ≠ 0 := by positivity
  have he : ((B:ℚ)+1)*frameParameter B i = (B:ℚ)+1-2*((i.val:ℚ)+1) := by
    unfold frameParameter
    field_simp
  obtain ⟨b,hb⟩ := hB
  by_cases hi : i.val < B/2
  · have hp := (frameParameter_half_sign B ⟨b,hb⟩ i).1.mpr hi
    rw [abs_of_pos hp,he]
    have hn : 2*(i.val+1) ≤ B := by omega
    have hq : (2:ℚ)*((i.val:ℚ)+1) ≤ (B:ℚ) := by exact_mod_cast hn
    linarith
  · have hp := (frameParameter_half_sign B ⟨b,hb⟩ i).2.mpr (by omega)
    rw [abs_of_neg hp,mul_neg,he]
    have hn : B+2 ≤ 2*(i.val+1) := by omega
    have hq : (B:ℚ)+2 ≤ (2:ℚ)*((i.val:ℚ)+1) := by exact_mod_cast hn
    linarith

theorem indexed_clone_margin (B : ℕ) (hB : Even B) (i : Fin B) (a b mu : ℚ)
    (hclone : 3*((B:ℚ)+1)*|b-a| ≤ mu) :
    3*|b-a| ≤ mu*|frameParameter B i| := by
  have hg := mul_le_mul_of_nonneg_left (frameParameter_gap B hB i)
    (by positivity : (0:ℚ) ≤ 3*|b-a|)
  have hh := mul_le_mul_of_nonneg_right hclone (abs_nonneg (frameParameter B i))
  nlinarith

/-- The actual ordinary parent-clone table (4.4), with one explicit uniform
clone radius for all frame rows. It applies simultaneously to any family of
parent clones satisfying this same parameter bound. -/
theorem ordinary_clone_indexed (B : ℕ) (hB : Even B) (i k : Fin B)
    (a b mu : ℚ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*((B:ℚ)+1)*|b-a| ≤ mu) :
    ProperCross (ordinary a mu) (frame (frameParameter B k))
      (original b) (frame (frameParameter B i)) ↔
      (i < k ∧ k.val < B/2) ∨ (k < i ∧ B/2 ≤ k.val) := by
  have hr := ordinary_valid a mu (abs_le.mp ha).1 (abs_le.mp ha).2 hm hm1
  have hs (j : Fin B) := ordinary_clone_sign a b mu (frameParameter B j) ha hb hm hm1
    (le_of_lt (frameParameter_unit B j))
    (by
      intro hz
      have hg := frameParameter_gap B hB j
      rw [hz,abs_zero,mul_zero] at hg
      norm_num at hg)
    (indexed_clone_margin B hB j a b mu hclone)
  rw [fan_crossing_epsilon _ b _ _ hr (le_of_lt (frameParameter_unit B i))
    (le_of_lt (frameParameter_unit B k)),(hs i).1,(hs k).1,(hs i).2,(hs k).2,
    (frameParameter_antitone B).lt_iff_gt,(frameParameter_antitone B).lt_iff_gt,
    (frameParameter_half_sign B hB i).1,(frameParameter_half_sign B hB k).1,
    (frameParameter_half_sign B hB i).2,(frameParameter_half_sign B hB k).2]
  constructor
  · rintro (⟨h,_,hk⟩|⟨h,_,hk⟩)
    · exact Or.inl ⟨h,hk⟩
    · exact Or.inr ⟨h,hk⟩
  · rintro (⟨h,hk⟩|⟨h,hk⟩)
    · exact Or.inl ⟨h,by omega,hk⟩
    · exact Or.inr ⟨h,by omega,hk⟩

theorem bridge_lower (a b t : ℚ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    10 ≤ bridge a b t := by
  have haa := unit_square_bound a (abs_le.mp ha).1 (abs_le.mp ha).2
  have hbb := unit_square_bound b (abs_le.mp hb).1 (abs_le.mp hb).2
  unfold bridge
  nlinarith [sq_nonneg (t+a),sq_nonneg (t+b),sq_nonneg (a-b)]

theorem cap_frame_x_bound (a t : ℚ) (ha : |a| ≤ 1) (ht : |t| ≤ 1) :
    |(frame t).1-(original a).1| ≤ 12 := by
  have haa := unit_square_bound a (abs_le.mp ha).1 (abs_le.mp ha).2
  have htt := unit_square_bound t (abs_le.mp ht).1 (abs_le.mp ht).2
  rw [abs_le]
  unfold frame original
  constructor <;> nlinarith [sq_nonneg a,sq_nonneg t]

/-- The actual ordinary displacement changes any nonparent fan-ray determinant
by at most 36 mu, uniformly over the two cap parameter intervals. -/
theorem ordinary_displacement_lipschitz (a b mu t : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1) (hm : 0 ≤ mu) :
    |orient (ordinary a mu) (original b) (frame t) -
      orient (original a) (original b) (frame t)| ≤ 36*mu := by
  have hx0 := cap_frame_x_bound a 0 ha (by norm_num)
  have hx1 := cap_frame_x_bound b t hb ht
  have hy0 : |(frame 0).2-(original a).2| ≤ 1 := by simpa [frame,original] using ha
  have hy1 : |(frame t).2-(original b).2| ≤ 2 := by
    have hh := abs_sub_le t 0 b
    simp only [sub_zero,zero_sub,abs_neg] at hh
    simpa only [frame,original] using (show |t-b| ≤ 2 by linarith)
  have hmul0 : |((frame 0).1-(original a).1)*((frame t).2-(original b).2)| ≤ 24 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hx0 hy1 (abs_nonneg _) (by norm_num : (0:ℚ)≤12)]
  have hmul1 : |((frame 0).2-(original a).2)*((frame t).1-(original b).1)| ≤ 12 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hy0 hx1 (abs_nonneg _) (by norm_num : (0:ℚ)≤1)]
  have hh := abs_sub_le
    (((frame 0).1-(original a).1)*((frame t).2-(original b).2)) 0
    (((frame 0).2-(original a).2)*((frame t).1-(original b).1))
  simp only [sub_zero,zero_sub,abs_neg] at hh
  have hcoef : |((frame 0).1-(original a).1)*((frame t).2-(original b).2)-
      ((frame 0).2-(original a).2)*((frame t).1-(original b).1)| ≤ 36 := by linarith
  have he : orient (ordinary a mu) (original b) (frame t) -
      orient (original a) (original b) (frame t) =
      mu * (((frame 0).1-(original a).1)*((frame t).2-(original b).2)-
        ((frame 0).2-(original a).2)*((frame t).1-(original b).1)) := by
    unfold orient ordinary mix frame original
    ring
  rw [he,abs_mul,abs_of_nonneg hm]
  nlinarith [mul_le_mul_of_nonneg_left hcoef hm]

/-- Actual nonparent ray signs from a numerical separation bound. All frame
rows are covered at once; no nonparent incidence predicate is assumed. -/
theorem ordinary_nonparent_sign (a b mu t : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1) (hm : 0 < mu)
    (hsep : 5*mu ≤ |b-a|) :
    (0 < orient (ordinary a mu) (original b) (frame t) ↔ b < a) ∧
    (orient (ordinary a mu) (original b) (frame t) < 0 ↔ a < b) := by
  have he := ordinary_displacement_lipschitz a b mu t ha hb ht (le_of_lt hm)
  have herr := abs_le.mp he
  have hbase := original_pair_frame a b t
  have hbri := bridge_lower a b t ha hb
  have hne : b ≠ a := by intro h; subst b; simp only [sub_self,abs_zero] at hsep; linarith
  rcases lt_or_gt_of_ne hne with hba | hab
  · rw [abs_of_neg (sub_neg.mpr hba)] at hsep
    have hmul := mul_le_mul_of_nonneg_left hbri (by linarith : (0:ℚ)≤a-b)
    have hsign : 0 < orient (ordinary a mu) (original b) (frame t) := by
      nlinarith [herr.1,herr.2]
    exact ⟨by constructor <;> intro _ <;> assumption,by constructor <;> intro h <;> linarith⟩
  · rw [abs_of_pos (sub_pos.mpr hab)] at hsep
    have hmul := mul_le_mul_of_nonneg_left hbri (by linarith : (0:ℚ)≤b-a)
    have hsign : orient (ordinary a mu) (original b) (frame t) < 0 := by
      nlinarith [herr.1,herr.2]
    exact ⟨by constructor <;> intro h <;> linarith,by constructor <;> intro _ <;> assumption⟩

/-- Every sufficiently separated actual nonparent original has exactly the
virtual-column neighborhood of the parent macro position. -/
theorem ordinary_nonparent_indexed (B : ℕ) (i k : Fin B) (a b mu : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hsep : 5*mu ≤ |b-a|) :
    ProperCross (ordinary a mu) (frame (frameParameter B k))
      (original b) (frame (frameParameter B i)) ↔
      (i < k ∧ b < a) ∨ (k < i ∧ a < b) := by
  have hr := ordinary_valid a mu (abs_le.mp ha).1 (abs_le.mp ha).2 hm hm1
  have hs (j : Fin B) := ordinary_nonparent_sign a b mu (frameParameter B j)
    ha hb (le_of_lt (frameParameter_unit B j)) hm hsep
  rw [fan_crossing_epsilon _ b _ _ hr (le_of_lt (frameParameter_unit B i))
    (le_of_lt (frameParameter_unit B k)),(hs i).1,(hs k).1,(hs i).2,(hs k).2,
    (frameParameter_antitone B).lt_iff_gt,(frameParameter_antitone B).lt_iff_gt]
  tauto

theorem ordinary_core_side (a b mu : ℚ) :
    orient (original a) (original b) (ordinary a mu) = mu*(b-a)*bridge a b 0 := by
  unfold orient ordinary mix original frame bridge
  ring

/-- The full strict proper-crossing test for an incident core edge at the
macro parent. The other macro is separated numerically, uniformly in the row. -/
theorem ordinary_core_crossing (a b mu t : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1) (hm : 0 < mu)
    (hsep : 5*mu ≤ |b-a|) :
    ProperCross (ordinary a mu) (frame t) (original a) (original b) ↔
      (0 < t ∧ a < b) ∨ (t < 0 ∧ b < a) := by
  have hsign := ordinary_nonparent_sign a b mu t ha hb ht hm hsep
  have hparent := ordinary_parent_sign a mu t hm ht
  have hb0 := bridge_positive a b 0 ha hb
  have hbt := bridge_positive a b t ha hb
  have hab : b-a ≠ 0 := by
    intro h
    rw [h,abs_zero] at hsep
    linarith
  have hsecond : orient (original a) (original b) (ordinary a mu) *
      orient (original a) (original b) (frame t) < 0 := by
    rw [ordinary_core_side,original_pair_frame]
    have hp := mul_pos (mul_pos hm (sq_pos_of_ne_zero hab)) (mul_pos hb0 hbt)
    nlinarith
  unfold ProperCross
  rw [and_iff_left hsecond,orient_reverse_last (ordinary a mu) (frame t) (original a),
    orient_reverse_last (ordinary a mu) (frame t) (original b),neg_mul_neg,mul_neg_iff]
  rw [hparent.1,hsign.2,hparent.2,hsign.1]

theorem ordinary_core_indexed (B : ℕ) (hB : Even B) (k : Fin B) (a b mu : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hm : 0 < mu) (hsep : 5*mu ≤ |b-a|) :
    ProperCross (ordinary a mu) (frame (frameParameter B k)) (original a) (original b) ↔
      (k.val < B/2 ∧ a < b) ∨ (B/2 ≤ k.val ∧ b < a) := by
  rw [ordinary_core_crossing a b mu _ ha hb (le_of_lt (frameParameter_unit B k)) hm hsep,
    (frameParameter_half_sign B hB k).1,(frameParameter_half_sign B hB k).2]

theorem ordinary_clone_core_margin (a c b mu : ℚ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*|c-a| ≤ mu) :
    (ordinary a mu).1 - chordX c b (ordinary a mu).2 < 0 := by
  have hy := ordinary_height a mu (abs_le.mp ha).1 (abs_le.mp ha).2 (le_of_lt hm) hm1
  have habs : |(ordinary a mu).2-b| ≤ 3 := by
    have hh := abs_sub_le (ordinary a mu).2 0 b
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have hyabs := abs_le.mpr hy
    linarith
  have hprod : |(c-a)*((ordinary a mu).2-b)/100| ≤ 3*|c-a|/100 := by
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℚ)<100)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left habs (abs_nonneg (c-a))]
  have hbridge := bridge_lower a b 0 ha hb
  have hmain := mul_le_mul_of_nonneg_left hbridge (le_of_lt hm)
  have he : (ordinary a mu).1 - chordX c b (ordinary a mu).2 =
      -mu*bridge a b 0 + (c-a)*((ordinary a mu).2-b)/100 := by
    unfold ordinary mix original frame chordX bridge
    ring
  rw [he]
  have heup := (abs_le.mp hprod).2
  linarith

theorem original_chord_orientation (c b : ℚ) (r : Point) :
    orient (original c) (original b) r = -(b-c)*(r.1-chordX c b r.2) := by
  unfold orient original chordX
  ring

/-- The ordinary half-frame core interface for an actual parent clone and any
actual nonparent original. Both endpoints may therefore already be cloned.
Only explicit rational parameter distances are assumed. -/
theorem ordinary_clone_core_indexed (B : ℕ) (hB : Even B) (k : Fin B)
    (a c b mu : ℚ) (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hb : |b| ≤ 1)
    (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*((B:ℚ)+1)*|c-a| ≤ mu) (hsep : 5*mu ≤ |b-a|) :
    ProperCross (ordinary a mu) (frame (frameParameter B k)) (original c) (original b) ↔
      (k.val < B/2 ∧ a < b) ∨ (B/2 ≤ k.val ∧ b < a) := by
  have hsmall : 3*|c-a| ≤ mu := by
    have hB0 : (0:ℚ)≤B := Nat.cast_nonneg _
    nlinarith [mul_nonneg hB0 (abs_nonneg (c-a))]
  have hmargin := ordinary_clone_core_margin a c b mu ha hb hm hm1 hsmall
  have hne : b-c ≠ 0 := by
    intro he
    have he' : b = c := sub_eq_zero.mp he
    rw [he'] at hsep
    linarith
  have hbridge := bridge_positive c b (frameParameter B k) hc hb
  have hsecond : orient (original c) (original b) (ordinary a mu) *
      orient (original c) (original b) (frame (frameParameter B k)) < 0 := by
    rw [original_chord_orientation,original_pair_frame]
    have hp := mul_pos (sq_pos_of_ne_zero hne) hbridge
    have hn := mul_neg_of_pos_of_neg hp hmargin
    nlinarith
  have hsign := ordinary_nonparent_sign a b mu (frameParameter B k) ha hb
    (le_of_lt (frameParameter_unit B k)) hm hsep
  have hparent := ordinary_clone_sign a c mu (frameParameter B k) ha hc hm hm1
    (le_of_lt (frameParameter_unit B k))
    (by
      intro hz
      have hg := frameParameter_gap B hB k
      rw [hz,abs_zero,mul_zero] at hg
      norm_num at hg)
    (indexed_clone_margin B hB k a c mu hclone)
  unfold ProperCross
  rw [and_iff_left hsecond,
    orient_reverse_last (ordinary a mu) (frame (frameParameter B k)) (original c),
    orient_reverse_last (ordinary a mu) (frame (frameParameter B k)) (original b),
    neg_mul_neg,mul_neg_iff,hparent.1,hsign.2,hparent.2,hsign.1,
    (frameParameter_half_sign B hB k).1,(frameParameter_half_sign B hB k).2]

end Q4.Candidate.OrdinaryFan

#print axioms Q4.Candidate.OrdinaryFan.frameSide_positive
#print axioms Q4.Candidate.OrdinaryFan.fan_crossing_epsilon
#print axioms Q4.Candidate.OrdinaryFan.ordinary_parent_crossing
#print axioms Q4.Candidate.OrdinaryFan.ordinary_parent_indexed
#print axioms Q4.Candidate.OrdinaryFan.original_parameter_lipschitz
#print axioms Q4.Candidate.OrdinaryFan.ordinary_clone_sign
#print axioms Q4.Candidate.OrdinaryFan.ordinary_clone_indexed
#print axioms Q4.Candidate.OrdinaryFan.ordinary_nonparent_indexed
#print axioms Q4.Candidate.OrdinaryFan.ordinary_core_indexed
#print axioms Q4.Candidate.OrdinaryFan.ordinary_clone_core_indexed
