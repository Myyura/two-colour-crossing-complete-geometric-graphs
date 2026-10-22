import Q4.Candidate.VirtualColumnMidpoint

/-! Actual finite virtual-field shape, via exact truncated arithmetic sums. -/
open scoped BigOperators
namespace Q4.Candidate.VirtualColumnShape
open Q4.Candidate.GridCounts Q4.Candidate.VirtualColumnField
open Q4.Candidate.VirtualColumnMidpoint

/-- Sum of the first c midpoint numerators, without division by n. -/
theorem prefix_numerators (n c : ℕ) (hc : c≤n) :
    (∑ j : Fin n, if j.val<c then (j.val:ℝ)+1/2 else 0) = (c:ℝ)^2/2 := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hcn : c<n := by omega
    have hi := ih (by omega)
    let k : Fin n := ⟨c,hcn⟩
    have he (j : Fin n) :
        (if j.val<c+1 then (j.val:ℝ)+1/2 else 0) =
        (if j.val<c then (j.val:ℝ)+1/2 else 0)+
          (if j=k then (c:ℝ)+1/2 else 0) := by
      by_cases hj : j=k
      · subst j
        simp [k]
      · have hv : j.val≠c := by intro h; exact hj (Fin.ext h)
        by_cases hjc : j.val<c
        · simp [hj,hjc,show j.val<c+1 by omega]
        · simp [hj,hjc,show ¬j.val<c+1 by omega]
    simp_rw [he]
    rw [Finset.sum_add_distrib,hi]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Nat.cast_add,Nat.cast_one]
    ring

theorem prefix_midpoints (n c : ℕ) (hc : c≤n) :
    (∑ j : Fin n, if j.val<c then u n j else 0) = (c:ℝ)^2/(2*n) := by
  have he (j : Fin n) : (if j.val<c then u n j else 0) =
      (if j.val<c then (j.val:ℝ)+1/2 else 0)/(n:ℝ) := by
    by_cases hj : j.val<c <;> simp [hj,u]
  simp_rw [he]
  have hsum := prefix_numerators n c hc
  simp_rw [div_eq_mul_inv] at hsum ⊢
  rw [←Finset.sum_mul,hsum]
  ring

noncomputable def rampPrefix (n r : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin n, if j.val<r then max (t-u n j) 0 else 0

noncomputable def rampModel (n r : ℕ) (t : ℝ) : ℝ :=
  (n:ℝ)/2*(t^2-(max (t-(r:ℝ)/n) 0)^2)

theorem rampPrefix_exact (n r : ℕ) (hn : 0<n) (hr : r≤n) (t : ℝ) :
    rampPrefix n r t =
      ((min r (Nat.ceil ((n:ℝ)*t-1/2)):ℕ):ℝ)*t-
        ((min r (Nat.ceil ((n:ℝ)*t-1/2)):ℕ):ℝ)^2/(2*n) := by
  classical
  let c := min r (Nat.ceil ((n:ℝ)*t-1/2))
  have hc : c≤n := (min_le_left _ _).trans hr
  have he (j : Fin n) : (if j.val<r then max (t-u n j) 0 else 0) =
      (if j.val<c then t else 0)-(if j.val<c then u n j else 0) := by
    have hjc : j.val<c ↔ j.val<r ∧ u n j<t := by
      simp only [c,lt_min_iff,midpoint_lt_ceil n hn j t]
    by_cases hjr : j.val<r
    · by_cases hjt : u n j<t
      · have h : j.val<c := hjc.mpr ⟨hjr,hjt⟩
        simp [hjr,h,max_eq_left (sub_nonneg.mpr (le_of_lt hjt))]
      · have h : ¬j.val<c := by rw [hjc]; tauto
        simp [hjr,h,max_eq_right (sub_nonpos.mpr (le_of_not_gt hjt))]
    · have h : ¬j.val<c := by rw [hjc]; tauto
      simp [hjr,h]
  unfold rampPrefix
  simp_rw [he]
  rw [Finset.sum_sub_distrib,prefix_midpoints n c hc]
  have hsum : (∑ j : Fin n, if j.val<c then t else 0) = (c:ℝ)*t := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hh := card_index_interval n 0 c hc
    simpa only [Nat.zero_le,true_and,Nat.sub_zero] using congrArg (fun a : ℕ => (a:ℝ)*t) hh
  rw [hsum]

/-- A half-point bound for the actual finite midpoint ramp sum; this loose
constant suffices for the manuscript's 6 rho shape estimate. -/
theorem rampPrefix_error (n r : ℕ) (hn : 0<n) (hr : r≤n)
    (t : ℝ) (ht : 0≤t) : |rampPrefix n r t-rampModel n r t| ≤ 1/2 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  by_cases htr : (r:ℝ)/n≤t
  · have hall (j : Fin n) (hj : j.val<r) : u n j<t := by
      have hj' : (j.val:ℝ)+1≤r := by exact_mod_cast hj
      unfold u
      rw [div_lt_iff₀ hn']
      have hmul := (div_le_iff₀ hn').mp htr
      nlinarith
    have he : rampPrefix n r t = (r:ℝ)*t-(r:ℝ)^2/(2*n) := by
      unfold rampPrefix
      have hpoint (j : Fin n) : (if j.val<r then max (t-u n j) 0 else 0) =
          (if j.val<r then t else 0)-(if j.val<r then u n j else 0) := by
        by_cases hj : j.val<r
        · simp [hj,max_eq_left (sub_nonneg.mpr (le_of_lt (hall j hj)))]
        · simp [hj]
      simp_rw [hpoint]
      rw [Finset.sum_sub_distrib,prefix_midpoints n r hr,←Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hh := card_index_interval n 0 r hr
      simp only [Nat.zero_le,true_and,Nat.sub_zero] at hh
      rw [hh]
    rw [he]
    have hm : rampModel n r t = (r:ℝ)*t-(r:ℝ)^2/(2*n) := by
      unfold rampModel
      rw [max_eq_left (sub_nonneg.mpr htr)]
      field_simp
      ring
    rw [hm,sub_self,abs_zero]
    norm_num
  · have htr' : t<(r:ℝ)/n := lt_of_not_ge htr
    let c := min r (Nat.ceil ((n:ℝ)*t-1/2))
    have herr : |(c:ℝ)-(n:ℝ)*t|≤1/2 := by
      have h := positiveIn_midpoint_error n 0 r hn hr t ht
      rw [positiveIn_card n 0 r hn hr t] at h
      have ht' : (n:ℝ)*t ≤ r := by nlinarith [(lt_div_iff₀ hn').mp htr']
      simpa only [Nat.sub_zero,Nat.cast_zero,sub_zero,min_eq_right ht',
        max_eq_left (mul_nonneg (le_of_lt hn') ht)] using h
    rw [rampPrefix_exact n r hn hr t]
    change |(c:ℝ)*t-(c:ℝ)^2/(2*n)-rampModel n r t|≤1/2
    have hm : rampModel n r t = (n:ℝ)*t^2/2 := by
      unfold rampModel
      rw [max_eq_right (sub_nonpos.mpr (le_of_lt htr'))]
      ring
    rw [hm]
    have he : (c:ℝ)*t-(c:ℝ)^2/(2*n)-(n:ℝ)*t^2/2 =
        -(((c:ℝ)-(n:ℝ)*t)^2/(2*n)) := by field_simp; ring
    rw [he,abs_neg,abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
    rw [div_le_iff₀ (by positivity : (0:ℝ)<2*n)]
    have he2 : ((c:ℝ)-(n:ℝ)*t)^2≤1/4 := by
      nlinarith [sq_abs ((c:ℝ)-(n:ℝ)*t),abs_nonneg ((c:ℝ)-(n:ℝ)*t)]
    nlinarith


theorem prefix_constant (n c : ℕ) (hc : c≤n) (a : ℝ) :
    (∑ j : Fin n, if j.val<c then a else 0) = (c:ℝ)*a := by
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hh := card_index_interval n 0 c hc
  simpa only [Nat.zero_le,true_and,Nat.sub_zero] using congrArg (fun z : ℕ => (z:ℝ)*a) hh

theorem suffix_constant (n c : ℕ) (hc : c≤n) (a : ℝ) :
    (∑ j : Fin n, if j.val<c then 0 else a) = ((n:ℝ)-c)*a := by
  have he (j : Fin n) : (if j.val<c then 0 else a) = a-(if j.val<c then a else 0) := by
    by_cases h : j.val<c <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,prefix_constant n c hc]
  simp
  ring

noncomputable def augmentedField (B O r k : ℕ) : ℝ :=
  ∑ i : Fin B, if i.val<k then signedIn O 0 r (1-u B i) else signedIn O r O (1-u B i)

noncomputable def modelSum (B O r k : ℕ) : ℝ :=
  ∑ i : Fin B, if i.val<k then intervalModel 0 r ((O:ℝ)*(1-u B i))
    else intervalModel r O ((O:ℝ)*(1-u B i))

theorem augmented_eq_actual (B O r : ℕ) (k : Fin B) :
    augmentedField B O r k.val =
      (virtualField (spin : Fin B × Fin O → ℤ) r k.val:ℝ)+signedIn O r O (1-u B k) := by
  have hcol (j : Fin O) : (virtualColumn (spin : Fin B × Fin O → ℤ) r k.val j:ℝ) =
      ∑ i : Fin B, if i.val<k.val then (if j.val<r then (spin (i,j):ℝ) else 0)
      else if k.val<i.val then (if r≤j.val then (spin (i,j):ℝ) else 0) else 0 := by
    unfold virtualColumn rowPrefix rowSuffix
    by_cases hj : j.val<r
    · simp only [hj,ite_true,not_le.mpr hj,ite_false,Int.cast_sum,Int.cast_ite,Int.cast_zero]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val<k.val <;> simp [hi]
    · simp only [hj,ite_false,not_lt.mp hj,ite_true,Int.cast_sum,Int.cast_ite,Int.cast_zero]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val<k.val
      · simp [hi,show ¬k.val<i.val by omega]
      · simp [hi]
  have hrows : (virtualField (spin : Fin B × Fin O → ℤ) r k.val:ℝ) =
      ∑ i : Fin B, if i.val<k.val then signedIn O 0 r (1-u B i)
      else if k.val<i.val then signedIn O r O (1-u B i) else 0 := by
    unfold virtualField
    rw [Int.cast_sum]
    simp_rw [hcol]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val<k.val
    · simp only [hi,ite_true]
      exact canonical_prefix B O r i
    · simp only [hi,ite_false]
      by_cases hik : k.val<i.val
      · simp only [hik,ite_true]
        exact canonical_suffix B O r i
      · simp [hik]
  rw [hrows]
  unfold augmentedField
  have he (i : Fin B) :
      (if i.val<k.val then signedIn O 0 r (1-u B i) else signedIn O r O (1-u B i)) =
      (if i.val<k.val then signedIn O 0 r (1-u B i)
        else if k.val<i.val then signedIn O r O (1-u B i) else 0)+
      (if i=k then signedIn O r O (1-u B k) else 0) := by
    by_cases hi : i=k
    · subst i; simp
    · have hv : i.val≠k.val := by intro h; exact hi (Fin.ext h)
      by_cases hik : i.val<k.val
      · simp [hi,hik]
      · simp [hi,hik,show k.val<i.val by omega]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

theorem augmented_model_error (B O r k : ℕ) (hB : 0<B) (hO : 0<O) (hr : r≤O) :
    |augmentedField B O r k-modelSum B O r k|≤B := by
  unfold augmentedField modelSum
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin B, |(if i.val<k then signedIn O 0 r (1-u B i) else signedIn O r O (1-u B i))-
        (if i.val<k then intervalModel 0 r ((O:ℝ)*(1-u B i)) else intervalModel r O ((O:ℝ)*(1-u B i)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin B, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have ht : 0≤1-u B i := by linarith [u_lt_one B hB i]
      by_cases hi : i.val<k
      · simp only [hi,ite_true]
        exact signedIn_midpoint_error O 0 r hO (Nat.zero_le _) hr _ ht
      · simp only [hi,ite_false]
        exact signedIn_midpoint_error O r O hO hr (le_refl _) _ ht
    _ = _ := by simp

theorem models_hinge (O r : ℕ) (hO : 0<O) (_hr : r≤O) (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    intervalModel 0 r ((O:ℝ)*(1-x)) =
      2*(O:ℝ)*(1-x)-r-2*(O:ℝ)*max (1-(r:ℝ)/O-x) 0 ∧
    intervalModel r O ((O:ℝ)*(1-x)) =
      2*(O:ℝ)*max (1-(r:ℝ)/O-x) 0-((O:ℝ)-r) := by
  have ho : (0:ℝ)<O := by exact_mod_cast hO
  have hxn : (O:ℝ)*(1-x)≤O := by nlinarith
  have hx0 : 0≤(O:ℝ)*(1-x) := by positivity
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg _
  have hfactor : (O:ℝ)*(1-x)-r = (O:ℝ)*(1-(r:ℝ)/O-x) := by field_simp; ring
  have hmax : max ((O:ℝ)*(1-x)-r) 0 = (O:ℝ)*max (1-(r:ℝ)/O-x) 0 := by
    rw [hfactor]
    simpa only [mul_zero] using (mul_max_of_nonneg (1-(r:ℝ)/O-x) 0 (le_of_lt ho)).symm
  unfold intervalModel
  norm_num only [Nat.cast_zero,sub_zero]
  rw [max_eq_left (le_min hr0 hx0),min_eq_right hxn,hmax]
  constructor
  · by_cases h : (O:ℝ)*(1-x)≤r
    · rw [min_eq_right h]
      have hm : max ((O:ℝ)*(1-x)-r) 0=0 := max_eq_right (sub_nonpos.mpr h)
      rw [hmax] at hm
      nlinarith
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [min_eq_left h']
      have hm : max ((O:ℝ)*(1-x)-r) 0=(O:ℝ)*(1-x)-r := max_eq_left (sub_nonneg.mpr h')
      rw [hmax] at hm
      nlinarith
  · ring

noncomputable def fieldPolynomial (B O r k : ℕ) (F P : ℝ) : ℝ :=
  (k:ℝ)*(2*O-r)-(O:ℝ)*(k:ℝ)^2/B+2*(O:ℝ)*F-4*(O:ℝ)*P-
    ((B:ℝ)-k)*((O:ℝ)-r)

theorem modelSum_polynomial (B O r k : ℕ) (hB : 0<B) (hO : 0<O) (hr : r≤O) (hk : k≤B) :
    modelSum B O r k = fieldPolynomial B O r k
      (rampPrefix B B (1-(r:ℝ)/O)) (rampPrefix B k (1-(r:ℝ)/O)) := by
  let t := 1-(r:ℝ)/O
  have he (i : Fin B) :
      (if i.val<k then intervalModel 0 r ((O:ℝ)*(1-u B i))
        else intervalModel r O ((O:ℝ)*(1-u B i))) =
      (if i.val<k then 2*(O:ℝ)-r else 0)-
        2*(O:ℝ)*(if i.val<k then u B i else 0)+
        2*(O:ℝ)*max (t-u B i) 0-
        4*(O:ℝ)*(if i.val<k then max (t-u B i) 0 else 0)-
        (if i.val<k then 0 else (O:ℝ)-r) := by
    have h := models_hinge O r hO hr (u B i) (le_of_lt (u_pos B hB i))
      (le_of_lt (u_lt_one B hB i))
    rw [h.1,h.2]
    by_cases hi : i.val<k <;> simp only [hi,ite_true,ite_false] <;> dsimp [t] <;> ring
  unfold modelSum
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [←Finset.mul_sum]
  rw [prefix_constant B k hk,prefix_midpoints B k hk,suffix_constant B k hk]
  have hfull : (∑ i : Fin B, max (t-u B i) 0) = rampPrefix B B t := by
    unfold rampPrefix
    simp only [Fin.is_lt,ite_true]
  rw [hfull]
  change (k:ℝ)*(2*O-r)-2*(O:ℝ)*((k:ℝ)^2/(2*B))+
    2*(O:ℝ)*rampPrefix B B t-4*(O:ℝ)*rampPrefix B k t-((B:ℝ)-k)*((O:ℝ)-r) = _
  unfold fieldPolynomial
  dsimp [t]
  ring


noncomputable def shape (s : ℝ) : ℝ := s*(1-|s|)

theorem polynomial_shape (B O r k : ℕ) (hB : 0<B) (hO : 0<O)
    (_hr : r≤O) :
    fieldPolynomial B O r k (rampModel B B (1-(r:ℝ)/O))
      (rampModel B k (1-(r:ℝ)/O)) =
      -(B:ℝ)*O*shape (1-(r:ℝ)/O-(k:ℝ)/B) := by
  have hb : (B:ℝ)≠0 := by positivity
  have ho : (O:ℝ)≠0 := by positivity
  have ht : 1-(r:ℝ)/O≤1 := by
    have hv : 0≤(r:ℝ)/O := by positivity
    linarith
  unfold fieldPolynomial rampModel shape
  rw [div_self hb,max_eq_right (sub_nonpos.mpr ht)]
  by_cases hs : 0≤1-(r:ℝ)/O-(k:ℝ)/B
  · rw [max_eq_left hs,abs_of_nonneg hs]
    field_simp
    ring
  · have hs' := le_of_lt (lt_of_not_ge hs)
    rw [max_eq_right hs',abs_of_nonpos hs']
    field_simp
    ring

theorem model_shape_error (B O r k : ℕ) (hB : 0<B) (hO : 0<O)
    (hr : r≤O) (hk : k≤B) :
    |modelSum B O r k+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k:ℝ)/B)| ≤ 3*(O:ℝ) := by
  have ho : (0:ℝ)≤O := Nat.cast_nonneg _
  have ht : 0≤1-(r:ℝ)/O := by
    rw [sub_nonneg,div_le_one (by positivity : (0:ℝ)<O)]
    exact_mod_cast hr
  have hf := rampPrefix_error B B hB (le_refl _) (1-(r:ℝ)/O) ht
  have hp := rampPrefix_error B k hB hk (1-(r:ℝ)/O) ht
  rw [modelSum_polynomial B O r k hB hO hr hk]
  have hident := polynomial_shape B O r k hB hO hr
  have he : fieldPolynomial B O r k (rampPrefix B B (1-(r:ℝ)/O))
      (rampPrefix B k (1-(r:ℝ)/O))+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k:ℝ)/B) =
      2*(O:ℝ)*(rampPrefix B B (1-(r:ℝ)/O)-rampModel B B (1-(r:ℝ)/O))-
      4*(O:ℝ)*(rampPrefix B k (1-(r:ℝ)/O)-rampModel B k (1-(r:ℝ)/O)) := by
    unfold fieldPolynomial at hident ⊢
    linarith
  rw [he]
  calc
    _ ≤ |2*(O:ℝ)*(rampPrefix B B (1-(r:ℝ)/O)-rampModel B B (1-(r:ℝ)/O))|+
        |4*(O:ℝ)*(rampPrefix B k (1-(r:ℝ)/O)-rampModel B k (1-(r:ℝ)/O))| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
        (2*(O:ℝ)*(rampPrefix B B (1-(r:ℝ)/O)-rampModel B B (1-(r:ℝ)/O))) 0
        (4*(O:ℝ)*(rampPrefix B k (1-(r:ℝ)/O)-rampModel B k (1-(r:ℝ)/O)))
    _ ≤ 3*(O:ℝ) := by
      simp only [abs_mul,abs_of_nonneg ho]
      norm_num only [abs_of_pos (show (0:ℝ)<2 by norm_num),abs_of_pos (show (0:ℝ)<4 by norm_num)]
      nlinarith

theorem signedIn_bound (n r s : ℕ) (t : ℝ) : |signedIn n r s t|≤n := by
  unfold signedIn
  calc
    _ ≤ ∑ j : Fin n, |if r≤j.val ∧ j.val<s then (if u n j<t then (1:ℝ) else -1) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      split <;> (try split) <;> norm_num
    _ = _ := by simp

theorem shape_lipschitz (s t : ℝ) (hs : |s|≤1) (ht : |t|≤1) :
    |shape s-shape t|≤3*|s-t| := by
  have h1 := abs_sub_le (s-t) 0 ((s-t)*|s|+t*(|s|-|t|))
  simp only [sub_zero,zero_sub,abs_neg] at h1
  have h2 := abs_add_le ((s-t)*|s|) (t*(|s|-|t|))
  rw [abs_mul,abs_abs,abs_mul] at h2
  have h3 : abs (abs s-abs t)≤abs (s-t) := abs_abs_sub_abs_le_abs_sub s t
  have he : shape s-shape t = (s-t)-((s-t)*|s|+t*(|s|-|t|)) := by
    unfold shape
    ring
  rw [he]
  nlinarith [abs_nonneg (s-t),abs_nonneg t,abs_nonneg s,
    mul_le_mul_of_nonneg_left h3 (abs_nonneg t)]

/-- Second inequality in manuscript (4.12).  The field is the actual finite
sum; the proof uses finite midpoint counts and arithmetic sums only. -/
theorem virtualField_shape_estimate (B O r : ℕ) (hO : 0<O) (hr : r≤O) (k : Fin B) :
    |(virtualField (spin : Fin B × Fin O → ℤ) r k.val:ℝ)/((B:ℝ)*O)+
      (1-u B k-(r:ℝ)/O)*(1-|1-u B k-(r:ℝ)/O|)| ≤ 6*rho B O := by
  have hB : 0<B := k.pos
  have hb : (0:ℝ)<B := by exact_mod_cast hB
  have ho : (0:ℝ)<O := by exact_mod_cast hO
  have hv : 0≤(r:ℝ)/O := by positivity
  have hv1 : (r:ℝ)/O≤1 := by
    rw [div_le_one ho]
    exact_mod_cast hr
  have hk0 : (0:ℝ)≤(k.val:ℝ)/B := by positivity
  have hk1 : (k.val:ℝ)/B≤1 := by
    rw [div_le_one hb]
    exact_mod_cast (le_of_lt k.isLt)
  have hs : |1-(r:ℝ)/O-(k.val:ℝ)/B|≤1 := by rw [abs_le]; constructor <;> linarith
  have ht : |1-u B k-(r:ℝ)/O|≤1 := by
    rw [abs_le]
    constructor <;> linarith [u_pos B hB k,u_lt_one B hB k]
  have hdiff : |(1-(r:ℝ)/O-(k.val:ℝ)/B)-(1-u B k-(r:ℝ)/O)| = 1/(2*B) := by
    have he : (1-(r:ℝ)/O-(k.val:ℝ)/B)-(1-u B k-(r:ℝ)/O) = 1/(2*B) := by
      unfold u
      ring
    rw [he,abs_of_pos (by positivity)]
  have hshape := shape_lipschitz _ _ hs ht
  rw [hdiff] at hshape
  have hshape' : |(B:ℝ)*O*(shape (1-(r:ℝ)/O-(k.val:ℝ)/B)-
      shape (1-u B k-(r:ℝ)/O))| ≤ 3*(O:ℝ)/2 := by
    rw [abs_mul,abs_of_pos (mul_pos hb ho)]
    have h := mul_le_mul_of_nonneg_left hshape (le_of_lt (mul_pos hb ho))
    have he : (B:ℝ)*O*(3*(1/(2*B))) = 3*(O:ℝ)/2 := by field_simp
    simpa only [he] using h
  have hmodel := augmented_model_error B O r k.val hB hO hr
  have hpoly := model_shape_error B O r k.val hB hO hr (le_of_lt k.isLt)
  have hexact := augmented_eq_actual B O r k
  have hrow := signedIn_bound O r O (1-u B k)
  let H := (virtualField (spin : Fin B × Fin O → ℤ) r k.val:ℝ)
  let S := shape (1-u B k-(r:ℝ)/O)
  have herr : |H+(B:ℝ)*O*S| ≤ (B:ℝ)+11*(O:ℝ)/2 := by
    have h1 := abs_add_le (augmentedField B O r k.val-modelSum B O r k.val)
      (modelSum B O r k.val+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k.val:ℝ)/B))
    have h2 := abs_sub_le (augmentedField B O r k.val+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k.val:ℝ)/B))
      0 (signedIn O r O (1-u B k))
    have h3 := abs_sub_le (H+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k.val:ℝ)/B)) 0
      ((B:ℝ)*O*(shape (1-(r:ℝ)/O-(k.val:ℝ)/B)-S))
    simp only [sub_zero,zero_sub,abs_neg] at h2 h3
    have he1 : (augmentedField B O r k.val-modelSum B O r k.val)+
      (modelSum B O r k.val+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k.val:ℝ)/B)) =
      augmentedField B O r k.val+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k.val:ℝ)/B) := by ring
    rw [he1] at h1
    have he2 : augmentedField B O r k.val+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k.val:ℝ)/B)-
        signedIn O r O (1-u B k) = H+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k.val:ℝ)/B) := by
      dsimp [H]
      linarith [hexact]
    rw [he2] at h2
    have he3 : H+(B:ℝ)*O*shape (1-(r:ℝ)/O-(k.val:ℝ)/B)-
      (B:ℝ)*O*(shape (1-(r:ℝ)/O-(k.val:ℝ)/B)-S) = H+(B:ℝ)*O*S := by ring
    rw [he3] at h3
    change |(B:ℝ)*O*(shape (1-(r:ℝ)/O-(k.val:ℝ)/B)-S)|≤3*(O:ℝ)/2 at hshape'
    linarith
  change |H/((B:ℝ)*O)+S|≤6*rho B O
  have he : H/((B:ℝ)*O)+S = (H+(B:ℝ)*O*S)/((B:ℝ)*O) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos hb ho),div_le_iff₀ (mul_pos hb ho)]
  have hrho : 6*rho B O*((B:ℝ)*O)=6*((B:ℝ)+O) := by
    unfold rho
    field_simp
    ring
  rw [hrho]
  linarith

end Q4.Candidate.VirtualColumnShape
#print axioms Q4.Candidate.VirtualColumnShape.rampPrefix_exact
#print axioms Q4.Candidate.VirtualColumnShape.rampPrefix_error

#print axioms Q4.Candidate.VirtualColumnShape.virtualField_shape_estimate
