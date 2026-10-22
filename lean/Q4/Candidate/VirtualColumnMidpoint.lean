import Q4.Candidate.VirtualColumnField
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.MinMax

/-! Finite midpoint-sign counting for the actual virtual-column field.
Strict midpoint ties are kept throughout, using Nat.ceil(x-1/2).
-/

open scoped BigOperators

namespace Q4.Candidate.VirtualColumnMidpoint

open Q4.Candidate.GridCounts Q4.Candidate.VirtualColumnField

theorem card_index_interval (n r s : ℕ) (hs : s ≤ n) :
    ((Finset.univ.filter (fun j : Fin n => r ≤ j.val ∧ j.val < s)).card) = s-r := by
  classical
  have he : (Finset.univ.filter (fun j : Fin n => r ≤ j.val ∧ j.val < s)).card =
      (Finset.Ico r s).card := by
    apply Finset.card_bij (fun j _ => j.val)
    · intro j hj
      simpa only [Finset.mem_Ico] using (Finset.mem_filter.mp hj).2
    · intro j _ k _ h
      exact Fin.ext h
    · intro j hj
      have hj' := Finset.mem_Ico.mp hj
      refine ⟨⟨j,lt_of_lt_of_le hj'.2 hs⟩,?_,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj'⟩
  rw [he,Nat.card_Ico]

theorem midpoint_lt_ceil (n : ℕ) (hn : 0 < n) (j : Fin n) (t : ℝ) :
    u n j < t ↔ j.val < Nat.ceil ((n:ℝ)*t-1/2) := by
  rw [Nat.lt_ceil]
  unfold u
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  rw [div_lt_iff₀ hn']
  constructor <;> intro h <;> nlinarith

noncomputable def positiveIn (n r s : ℕ) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => r ≤ j.val ∧ j.val < s ∧ u n j < t)

theorem positiveIn_card (n r s : ℕ) (hn : 0 < n) (hs : s ≤ n) (t : ℝ) :
    (positiveIn n r s t).card = min s (Nat.ceil ((n:ℝ)*t-1/2))-r := by
  have he : positiveIn n r s t = Finset.univ.filter
      (fun j : Fin n => r ≤ j.val ∧ j.val < min s (Nat.ceil ((n:ℝ)*t-1/2))) := by
    ext j
    simp only [positiveIn,Finset.mem_filter,Finset.mem_univ,true_and,
      midpoint_lt_ceil n hn j t,lt_min_iff]
  rw [he,card_index_interval n r _ ((min_le_left _ _).trans hs)]

theorem midpoint_rounding (x : ℝ) (hx : 0 ≤ x) :
    |(Nat.ceil (x-1/2):ℝ)-x| ≤ 1/2 := by
  by_cases ht : 0 ≤ x-1/2
  · have hlo := Nat.le_ceil (x-1/2)
    have hhi := Nat.ceil_lt_add_one ht
    rw [abs_le]
    constructor <;> linarith
  · have hz := Nat.ceil_eq_zero.mpr (le_of_lt (lt_of_not_ge ht))
    rw [hz]
    norm_num only [Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg hx]
    linarith

theorem cast_nat_sub (a b : ℕ) : ((a-b:ℕ):ℝ) = max ((a:ℝ)-b) 0 := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h,max_eq_left]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have hn : a ≤ b := by omega
    rw [Nat.sub_eq_zero_of_le hn,Nat.cast_zero,max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast hn)

theorem clipped_distance (r s x y : ℝ) :
    |max (min s x-r) 0 - max (min s y-r) 0| ≤ |x-y| := by
  have hm : |min s x-min s y| ≤ |x-y| := by
    simpa only [sub_self,abs_zero,max_eq_right (abs_nonneg (x-y))] using
      abs_min_sub_min_le_max s x s y
  have hc := abs_max_sub_max_le_abs (min s x-r) (min s y-r) 0
  have he : (min s x-r)-(min s y-r) = min s x-min s y := by ring
  rw [he] at hc
  exact hc.trans hm

/-- Each whole-cell interval has at most half a point of positive-count error.
This includes a midpoint lying exactly at the strict sign threshold. -/
theorem positiveIn_midpoint_error (n r s : ℕ) (hn : 0 < n) (hs : s ≤ n)
    (t : ℝ) (ht : 0 ≤ t) :
    |((positiveIn n r s t).card:ℝ)-max (min (s:ℝ) ((n:ℝ)*t)-r) 0| ≤ 1/2 := by
  rw [positiveIn_card n r s hn hs t,cast_nat_sub,Nat.cast_min]
  exact (clipped_distance r s _ _).trans
    (midpoint_rounding ((n:ℝ)*t) (mul_nonneg (Nat.cast_nonneg _) ht))

noncomputable def signedIn (n r s : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin n, if r ≤ j.val ∧ j.val < s then
    (if u n j < t then 1 else -1) else 0

noncomputable def intervalModel (r s : ℕ) (x : ℝ) : ℝ :=
  2 * max (min (s:ℝ) x-r) 0 - ((s:ℝ)-r)

theorem sum_indicator (n : ℕ) (P : Fin n → Prop) [DecidablePred P] :
    (∑ j : Fin n, if P j then (1:ℝ) else 0) =
      ((Finset.univ.filter P).card:ℝ) := by
  rw [←Finset.sum_filter]
  simp

theorem signedIn_eq_card (n r s : ℕ) (hr : r ≤ s) (hs : s ≤ n) (t : ℝ) :
    signedIn n r s t = 2*((positiveIn n r s t).card:ℝ)-((s:ℝ)-r) := by
  classical
  unfold signedIn
  have he (j : Fin n) :
      (if r ≤ j.val ∧ j.val < s then (if u n j < t then (1:ℝ) else -1) else 0) =
      2*(if r ≤ j.val ∧ j.val < s ∧ u n j < t then 1 else 0) -
        (if r ≤ j.val ∧ j.val < s then 1 else 0) := by
    by_cases h : r ≤ j.val ∧ j.val < s <;> by_cases ht : u n j < t <;>
      simp only [←and_assoc,h,ht,ite_true,ite_false,true_and,false_and] <;> norm_num
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,sum_indicator,sum_indicator,
    card_index_interval n r s hs,Nat.cast_sub hr]
  rfl

theorem signedIn_midpoint_error (n r s : ℕ) (hn : 0 < n)
    (hr : r ≤ s) (hs : s ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    |signedIn n r s t-intervalModel r s ((n:ℝ)*t)| ≤ 1 := by
  rw [signedIn_eq_card n r s hr hs t]
  unfold intervalModel
  have he : 2*((positiveIn n r s t).card:ℝ)-((s:ℝ)-r) -
      (2*max (min (s:ℝ) ((n:ℝ)*t)-r) 0-((s:ℝ)-r)) =
      2*(((positiveIn n r s t).card:ℝ)-max (min (s:ℝ) ((n:ℝ)*t)-r) 0) := by ring
  rw [he,abs_mul]
  rw [abs_of_pos (show (0:ℝ)<2 by norm_num)]
  linarith [positiveIn_midpoint_error n r s hn hs t ht]

theorem intervalModel_lipschitz (r s : ℕ) (x y : ℝ) :
    |intervalModel r s x-intervalModel r s y| ≤ 2*|x-y| := by
  unfold intervalModel
  have he : (2*max (min (s:ℝ) x-r) 0-((s:ℝ)-r)) -
      (2*max (min (s:ℝ) y-r) 0-((s:ℝ)-r)) =
      2*(max (min (s:ℝ) x-r) 0-max (min (s:ℝ) y-r) 0) := by ring
  rw [he,abs_mul]
  rw [abs_of_pos (show (0:ℝ)<2 by norm_num)]
  exact mul_le_mul_of_nonneg_left (clipped_distance r s x y) (by norm_num)

theorem split_model (n r : ℕ) (hr : r ≤ n) (x : ℝ) (hx : 0 ≤ x) (hxn : x ≤ n) :
    intervalModel 0 r x-intervalModel r n x = (n:ℝ)-2*|x-r| := by
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hrn : (r:ℝ) ≤ n := by exact_mod_cast hr
  unfold intervalModel
  norm_num only [Nat.cast_zero,sub_zero]
  rw [min_eq_right hxn,max_eq_left (le_min hr0 hx)]
  by_cases hxr : x ≤ r
  · rw [min_eq_right hxr,max_eq_right (sub_nonpos.mpr hxr),abs_of_nonpos (sub_nonpos.mpr hxr)]
    ring
  · have hrx : (r:ℝ) ≤ x := le_of_lt (lt_of_not_ge hxr)
    rw [min_eq_left hrx,max_eq_left (sub_nonneg.mpr hrx),abs_of_nonneg (sub_nonneg.mpr hrx)]
    ring


theorem spin_cast (B O : ℕ) (k : Fin B) (j : Fin O) :
    (spin (k,j):ℝ) = if u O j < 1-u B k then 1 else -1 := by
  unfold spin Q4.Candidate.CanonicalField.canonical
  have he : u B k+u O j<1 ↔ u O j<1-u B k := by constructor <;> intro h <;> linarith
  simp only [he,decide_eq_true_eq]
  split <;> norm_num

theorem canonical_prefix (B O r : ℕ) (k : Fin B) :
    ((∑ j : Fin O, if j.val<r then spin (k,j) else 0):ℝ) =
      signedIn O 0 r (1-u B k) := by
  unfold signedIn
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.zero_le,true_and]
  by_cases hj : j.val<r <;> simp [hj,spin_cast]

theorem canonical_suffix (B O r : ℕ) (k : Fin B) :
    ((∑ j : Fin O, if r≤j.val then spin (k,j) else 0):ℝ) =
      signedIn O r O (1-u B k) := by
  unfold signedIn
  apply Finset.sum_congr rfl
  intro j _
  simp only [j.isLt,and_true]
  by_cases hj : r≤j.val <;> simp [hj,spin_cast]

theorem midpoint_step (B : ℕ) (k l : Fin B) (hl : l.val=k.val+1) :
    u B l-u B k = 1/(B:ℝ) := by
  have he : (l.val:ℝ)=(k.val:ℝ)+1 := by exact_mod_cast hl
  unfold u
  rw [he]
  ring

/-- The first inequality in manuscript (4.12), derived from actual strict
canonical spins and the exact finite virtual-field recurrence. -/
theorem virtualField_increment_estimate (B O r : ℕ) (hO : 0<O) (hr : r≤O)
    (k l : Fin B) (hl : l.val=k.val+1) :
    |((virtualField (spin : Fin B × Fin O → ℤ) r l.val-virtualField (spin : Fin B × Fin O → ℤ) r k.val:ℤ):ℝ) -
      (O:ℝ)*(1-2*|1-u B k-(r:ℝ)/O|)| ≤ 2+2*(O:ℝ)/B := by
  have hB : 0<B := k.pos
  have hB' : (0:ℝ)<B := by exact_mod_cast hB
  have hO' : (0:ℝ)<O := by exact_mod_cast hO
  have htk : 0 ≤ 1-u B k := by linarith [u_lt_one B hB k]
  have htl : 0 ≤ 1-u B l := by linarith [u_lt_one B hB l]
  have htk1 : 1-u B k ≤ 1 := by linarith [u_pos B hB k]
  have hkerr := signedIn_midpoint_error O 0 r hO (Nat.zero_le _) hr (1-u B k) htk
  have hlerr := signedIn_midpoint_error O r O hO hr (le_refl _) (1-u B l) htl
  have hmodel := intervalModel_lipschitz r O ((O:ℝ)*(1-u B l)) ((O:ℝ)*(1-u B k))
  have hstep : |(O:ℝ)*(1-u B l)-(O:ℝ)*(1-u B k)| = (O:ℝ)/B := by
    have he : (O:ℝ)*(1-u B l)-(O:ℝ)*(1-u B k) = -(O:ℝ)*(u B l-u B k) := by ring
    rw [he,midpoint_step B k l hl,abs_mul,abs_neg,
      abs_of_pos hO',abs_of_pos (div_pos (by norm_num) hB')]
    ring
  rw [hstep,←mul_div_assoc] at hmodel
  have hsplit := split_model O r hr ((O:ℝ)*(1-u B k))
    (mul_nonneg (le_of_lt hO') htk)
    (by nlinarith : (O:ℝ)*(1-u B k)≤O)
  have hscaled : (O:ℝ)-2*|(O:ℝ)*(1-u B k)-r| =
      (O:ℝ)*(1-2*|1-u B k-(r:ℝ)/O|) := by
    have he : (O:ℝ)*(1-u B k)-r = (O:ℝ)*(1-u B k-(r:ℝ)/O) := by
      field_simp
    rw [he,abs_mul,abs_of_pos hO']
    ring
  rw [hscaled] at hsplit
  rw [virtualField_increment spin r k l hl]
  push_cast
  rw [canonical_prefix,canonical_suffix,←hsplit]
  have htotal := abs_sub_le
    (signedIn O 0 r (1-u B k)-signedIn O r O (1-u B l))
    (intervalModel 0 r ((O:ℝ)*(1-u B k))-signedIn O r O (1-u B l))
    (intervalModel 0 r ((O:ℝ)*(1-u B k))-intervalModel r O ((O:ℝ)*(1-u B k)))
  have hthird := abs_sub_le (signedIn O r O (1-u B l))
    (intervalModel r O ((O:ℝ)*(1-u B l)))
    (intervalModel r O ((O:ℝ)*(1-u B k)))
  have ha : |(signedIn O 0 r (1-u B k)-signedIn O r O (1-u B l))-
      (intervalModel 0 r ((O:ℝ)*(1-u B k))-signedIn O r O (1-u B l))| =
      |signedIn O 0 r (1-u B k)-intervalModel 0 r ((O:ℝ)*(1-u B k))| := by congr 1; ring
  have hb : |(intervalModel 0 r ((O:ℝ)*(1-u B k))-signedIn O r O (1-u B l))-
      (intervalModel 0 r ((O:ℝ)*(1-u B k))-intervalModel r O ((O:ℝ)*(1-u B k)))| =
      |signedIn O r O (1-u B l)-intervalModel r O ((O:ℝ)*(1-u B k))| := by
    rw [←abs_neg]
    congr 1
    ring
  rw [ha,hb] at htotal
  linarith

end Q4.Candidate.VirtualColumnMidpoint

#print axioms Q4.Candidate.VirtualColumnMidpoint.positiveIn_card
#print axioms Q4.Candidate.VirtualColumnMidpoint.positiveIn_midpoint_error

#print axioms Q4.Candidate.VirtualColumnMidpoint.signedIn_midpoint_error

#print axioms Q4.Candidate.VirtualColumnMidpoint.virtualField_increment_estimate
