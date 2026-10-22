import Q4.Candidate.GlobalGeometryScales

/-! Explicit integer numerator/denominator certificates. They need not be
reduced: such a pair is already a valid binary rational input encoding. -/
namespace Q4.Candidate.RationalEncoding

def Bounded (q : ℚ) (H : ℕ) : Prop :=
  ∃ n d : ℤ, |n| ≤ (H:ℤ) ∧ |d| ≤ (H:ℤ) ∧ d ≠ 0 ∧ q=(n:ℚ)/(d:ℚ)

theorem Bounded.mono {q : ℚ} {H K : ℕ} (h : Bounded q H) (hk : H≤K) : Bounded q K := by
  obtain ⟨n,d,hn,hd,hne,he⟩ := h
  have hcast : (H:ℤ)≤K := by exact_mod_cast hk
  exact ⟨n,d,hn.trans hcast,hd.trans hcast,hne,he⟩

theorem Bounded.one_le {q : ℚ} {H : ℕ} (h : Bounded q H) : 1≤H := by
  obtain ⟨n,d,hn,hd,hne,he⟩ := h
  have hh := abs_le.mp hd
  omega

theorem bounded_int (n : ℤ) (H : ℕ) (hn : |n|≤(H:ℤ)) (hH : 1≤H) : Bounded (n:ℚ) H := by
  refine ⟨n,1,hn,?_,by norm_num,by simp⟩
  norm_num
  exact_mod_cast hH

theorem bounded_nat (n H : ℕ) (hn : n≤H) (hH : 1≤H) : Bounded (n:ℚ) H := by
  simpa using bounded_int (n:ℤ) H (by simpa using (show (n:ℤ)≤H by exact_mod_cast hn)) hH

theorem bounded_zero (H : ℕ) (hH : 1≤H) : Bounded 0 H := by
  simpa using bounded_nat 0 H (Nat.zero_le _) hH

theorem Bounded.neg {q : ℚ} {H : ℕ} (h : Bounded q H) : Bounded (-q) H := by
  obtain ⟨n,d,hn,hd,hne,he⟩ := h
  refine ⟨-n,d,by simpa using hn,hd,hne,?_⟩
  rw [he,Int.cast_neg,neg_div]

theorem Bounded.abs {q : ℚ} {H : ℕ} (h : Bounded q H) : Bounded |q| H := by
  rcases le_total 0 q with hq|hq
  · simpa only [abs_of_nonneg hq] using h
  · simpa only [abs_of_nonpos hq] using h.neg

theorem Bounded.add {x y : ℚ} {H K : ℕ} (hx : Bounded x H) (hy : Bounded y K) :
    Bounded (x+y) (2*H*K) := by
  obtain ⟨n,d,hn,hd,hd0,he⟩ := hx
  obtain ⟨m,e,hm,hh,he0,hf⟩ := hy
  have hnprod := mul_le_mul hn hh (abs_nonneg e) (Nat.cast_nonneg H)
  have hmprod := mul_le_mul hm hd (abs_nonneg d) (Nat.cast_nonneg K)
  have hdprod := mul_le_mul hd hh (abs_nonneg e) (Nat.cast_nonneg H)
  have hp0 : (0:ℤ)≤H*K := by positivity
  refine ⟨n*e+m*d,d*e,?_,?_,mul_ne_zero hd0 he0,?_⟩
  · have htri := abs_add_le (n*e) (m*d)
    simp only [abs_mul] at htri
    push_cast
    nlinarith
  · rw [abs_mul]
    push_cast
    nlinarith
  · rw [he,hf]
    push_cast
    field_simp

theorem Bounded.sub {x y : ℚ} {H K : ℕ} (hx : Bounded x H) (hy : Bounded y K) :
    Bounded (x-y) (2*H*K) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem Bounded.mul {x y : ℚ} {H K : ℕ} (hx : Bounded x H) (hy : Bounded y K) :
    Bounded (x*y) (H*K) := by
  obtain ⟨n,d,hn,hd,hd0,he⟩ := hx
  obtain ⟨m,e,hm,hh,he0,hf⟩ := hy
  refine ⟨n*m,d*e,?_,?_,mul_ne_zero hd0 he0,?_⟩
  · rw [abs_mul,Nat.cast_mul]
    exact mul_le_mul hn hm (abs_nonneg _) (Nat.cast_nonneg _)
  · rw [abs_mul,Nat.cast_mul]
    exact mul_le_mul hd hh (abs_nonneg _) (Nat.cast_nonneg _)
  · rw [he,hf]
    push_cast
    ring

theorem Bounded.inv {q : ℚ} {H : ℕ} (h : Bounded q H) : Bounded q⁻¹ H := by
  have hH := h.one_le
  obtain ⟨n,d,hn,hd,hd0,he⟩ := h
  by_cases hn0 : n=0
  · rw [he,hn0]
    simp only [Int.cast_zero,zero_div,inv_zero]
    exact bounded_zero H hH
  · refine ⟨d,n,hd,hn,hn0,?_⟩
    rw [he,inv_div]

theorem Bounded.div {x y : ℚ} {H K : ℕ} (hx : Bounded x H) (hy : Bounded y K) :
    Bounded (x/y) (H*K) := by
  simpa only [div_eq_mul_inv] using hx.mul hy.inv

theorem Bounded.min {x y : ℚ} {H : ℕ} (hx : Bounded x H) (hy : Bounded y H) :
    Bounded (min x y) H := by
  rcases le_total x y with h|h
  · simpa only [min_eq_left h] using hx
  · simpa only [min_eq_right h] using hy

/-- Selecting the actual finite minimum costs no extra encoding bits. -/
theorem bounded_min' (S : Finset ℚ) (hS : S.Nonempty) (H : ℕ)
    (h : ∀q∈S, Bounded q H) : Bounded (S.min' hS) H :=
  h _ (Finset.min'_mem S hS)

theorem Bounded.pow_mono {q : ℚ} {H i j : ℕ} (h : Bounded q (H^i))
    (hH : 1 ≤ H) (hij : i ≤ j) : Bounded q (H^j) :=
  h.mono (pow_le_pow_right₀ hH hij)

theorem Bounded.add_pow {x y : ℚ} {H i j : ℕ}
    (hx : Bounded x (H^i)) (hy : Bounded y (H^j)) (hH : 2 ≤ H) :
    Bounded (x+y) (H^(i+j+1)) := by
  apply (hx.add hy).mono
  calc
    2*H^i*H^j ≤ H*H^i*H^j := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hH)
    _ = H^(i+j+1) := by rw [pow_add,pow_add]; ring

theorem Bounded.sub_pow {x y : ℚ} {H i j : ℕ}
    (hx : Bounded x (H^i)) (hy : Bounded y (H^j)) (hH : 2 ≤ H) :
    Bounded (x-y) (H^(i+j+1)) := by
  simpa only [sub_eq_add_neg] using hx.add_pow hy.neg hH

theorem Bounded.mul_pow {x y : ℚ} {H i j : ℕ}
    (hx : Bounded x (H^i)) (hy : Bounded y (H^j)) : Bounded (x*y) (H^(i+j)) := by
  simpa only [pow_add] using hx.mul hy

theorem Bounded.div_pow {x y : ℚ} {H i j : ℕ}
    (hx : Bounded x (H^i)) (hy : Bounded y (H^j)) : Bounded (x/y) (H^(i+j)) := by
  simpa only [pow_add] using hx.div hy

theorem Bounded.sq_pow {x : ℚ} {H i : ℕ} (hx : Bounded x (H^i)) :
    Bounded (x^2) (H^(2*i)) := by
  simpa only [pow_two,two_mul] using hx.mul_pow hx

theorem bounded_nat_pow (n H : ℕ) (hn : n ≤ H) (hH : 1 ≤ H) :
    Bounded (n:ℚ) (H^1) := by simpa using bounded_nat n H hn hH

theorem bounded_sum_pow {ι : Type*} (S : Finset ι) (f : ι → ℚ) (H k : ℕ)
    (hH : 2 ≤ H) (hf : ∀ i∈S, Bounded (f i) (H^k)) :
    Bounded (∑ i∈S, f i) (H^(S.card*(k+1))) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using bounded_zero 1 (by omega)
  | @insert a S ha ih =>
    have hs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hh := (hf a (Finset.mem_insert_self _ _)).add_pow hs hH
    simpa only [Finset.sum_insert ha,Finset.card_insert_of_notMem ha,
      Nat.add_mul,Nat.one_mul,show k+S.card*(k+1)+1=S.card*(k+1)+(k+1) by omega] using hh

open Q4.Candidate.ConvexSeparation Q4.Candidate.OrdinaryNonincident
open Q4.Candidate.GlobalGeometryScales Q4.Candidate.OrientationPreservation
open Q4.Candidate.RankGap Q4.Candidate.DoubleCapGrid Q4.Candidate.UniformInsertion

theorem macroSpacing_encoding (A : Finset ℚ) (H : ℕ) (hH : 2 ≤ H)
    (hA : ∀ a∈A, Bounded a H) : Bounded (macroSpacing A) (H^3) := by
  unfold macroSpacing
  apply bounded_min'
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact (bounded_nat_pow 1 H (by omega) (by omega)).pow_mono (by omega) (by omega)
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    have hp' := (Finset.mem_filter.mp hp).1
    have ha := hA p.1 (Finset.mem_product.mp hp').1
    have hb := hA p.2 (Finset.mem_product.mp hp').2
    simpa using ((show Bounded p.1 (H^1) by simpa using ha).sub_pow
      (show Bounded p.2 (H^1) by simpa using hb) hH).abs

theorem scales_encoding (A : Finset ℚ) (W B H : ℕ) (hH : 10000 ≤ H)
    (hW : W ≤ H) (hB : B ≤ H) (hA : ∀a∈A, Bounded a H) :
    Bounded (programScale A W) (H^10) ∧ Bounded (cloneScale A W B) (H^20) := by
  have h2 : 2 ≤ H := by omega
  have h1 : 1 ≤ H := by omega
  have he := macroSpacing_encoding A H h2 hA
  have hone := bounded_nat_pow 1 H (by omega) h1
  have h10000 := bounded_nat_pow 10000 H hH h1
  have h1000 := bounded_nat_pow 1000 H (by omega) h1
  have hw := (bounded_nat_pow W H hW h1).add_pow hone h2
  have hb := (bounded_nat_pow B H hB h1).add_pow hone h2
  have hm : Bounded (programScale A W) (H^10) := by
    exact he.sq_pow.div_pow (h10000.mul_pow hw)
  refine ⟨hm,?_⟩
  exact (hm.mul_pow he.sq_pow).div_pow (h1000.mul_pow hb)

/-- Both coordinates have explicit (not necessarily reduced) binary input pairs. -/
def PointBounded (p : Point) (H k : ℕ) : Prop :=
  Bounded p.1 (H^k) ∧ Bounded p.2 (H^k)

theorem orient_encoding (a b c : Point) (H k : ℕ) (hH : 2 ≤ H)
    (ha : PointBounded a H k) (hb : PointBounded b H k) (hc : PointBounded c H k) :
    Bounded (orient a b c) (H^(8*k+5)) := by
  have hh := ((hb.1.sub_pow ha.1 hH).mul_pow (hc.2.sub_pow ha.2 hH)).sub_pow
    ((hb.2.sub_pow ha.2 hH).mul_pow (hc.1.sub_pow ha.1 hH)) hH
  convert hh using 1; congr 1; ring

theorem orientationMargin_encoding (B R : Finset Point) (H k : ℕ) (hH : 2 ≤ H)
    (hB : ∀a∈B, PointBounded a H k) (hR : ∀r∈R, PointBounded r H k) :
    Bounded (orientationMargin B R) (H^(8*k+5)) := by
  unfold orientationMargin
  apply bounded_min'
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact (bounded_nat_pow 1 H (by omega) (by omega)).pow_mono (by omega) (by omega)
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hv).1
    have hmem := Finset.mem_product.mp hp
    exact (orient_encoding p.1.1 p.1.2 p.2 H k hH
      (hB _ (Finset.mem_product.mp hmem.1).1)
      (hB _ (Finset.mem_product.mp hmem.1).2) (hR _ hmem.2)).abs

theorem baseBudget_encoding (B : Finset Point) (H k : ℕ) (hH : 2 ≤ H)
    (hB : ∀a∈B, PointBounded a H k) :
    Bounded (baseBudget B) (H^(B.card*(2*k+2)+3)) := by
  have hs := bounded_sum_pow B (fun a => |a.1|+|a.2|) H (2*k+1) hH
    (fun a ha => by convert (hB a ha).1.abs.add_pow (hB a ha).2.abs hH using 1; congr 1; omega)
  have hh := (bounded_nat_pow 1 H (by omega) (by omega)).add_pow
    ((bounded_nat_pow 2 H hH (by omega)).mul_pow hs) hH
  convert hh using 1; congr 1; ring

theorem finiteMargin_encoding (R : Finset Point) (f : Point → ℚ) (H k : ℕ)
    (hH : 2 ≤ H) (hk : 1 ≤ k) (hf : ∀r∈R, Bounded (f r) (H^k)) :
    Bounded (finiteMargin R f) (H^k) := by
  unfold finiteMargin
  apply bounded_min'
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact (bounded_nat_pow 1 H (by omega) (by omega)).pow_mono (by omega) hk
  · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
    exact hf r hr

theorem capMargin_encoding (R : Finset Point) (H k : ℕ) (hH : 100 ≤ H)
    (hR : ∀r∈R, PointBounded r H k) :
    Bounded (capMargin R) (H^(3*k+4)) := by
  apply finiteMargin_encoding R _ H _ (by omega) (by omega)
  intro r hr
  have hh := ((hR r hr).1.add_pow (bounded_nat_pow 10 H (by omega) (by omega)) (by omega)).add_pow
    ((hR r hr).2.sq_pow.div_pow (bounded_nat_pow 100 H hH (by omega))) (by omega)
  apply Bounded.neg
  convert hh using 1; congr 1; ring

theorem heightMargin_encoding (R : Finset Point) (H k : ℕ) (hH : 2 ≤ H)
    (hR : ∀r∈R, PointBounded r H k) :
    Bounded (heightMargin R) (H^(k+2)) := by
  apply finiteMargin_encoding R _ H _ hH (by omega)
  intro r hr
  convert (bounded_nat_pow 2 H hH (by omega)).sub_pow (hR r hr).2.abs hH using 1; congr 1; omega

/-- Actual common radius: finite minima do not multiply denominators. Only
the base-budget sum incurs a factor linear in the number of base points. -/
theorem constructionRadius_encoding (B R : Finset Point) (H k : ℕ) (hH : 100 ≤ H)
    (hB : ∀a∈B, PointBounded a H k) (hR : ∀r∈R, PointBounded r H k) :
    Bounded (constructionRadius B R) (H^(B.card*(2*k+2)+8*k+9)) := by
  have h2 : 2 ≤ H := by omega
  have h1 : 1 ≤ H := by omega
  have hn (n : ℕ) (hn : n ≤ H) := bounded_nat_pow n H hn h1
  have hquarter := (hn 1 (by omega)).div_pow (hn 4 (by omega))
  have hcap := (capMargin_encoding R H k hH hR).div_pow (hn 8 (by omega))
  have hheight := heightMargin_encoding R H k h2 hR
  have horient := (orientationMargin_encoding B R H k h2 hB hR).div_pow
    ((hn 8 (by omega)).mul_pow (baseBudget_encoding B H k h2 hB))
  unfold constructionRadius
  apply Bounded.min (hquarter.pow_mono h1 (by omega))
  apply Bounded.min (hcap.pow_mono h1 (by omega))
  apply Bounded.min (hheight.pow_mono h1 (by omega))
  convert horient using 1; congr 1; ring

theorem gridSide_encoding_bound (M H : ℕ) (hH : 3 ≤ H) (hM : M ≤ H) :
    gridSide M + 1 ≤ H^3 := by
  have hm2 : M*M ≤ H*H := Nat.mul_le_mul hM hM
  have hh : H ≤ H*H := by nlinarith
  have hh3 : 3 ≤ H*H := by nlinarith
  have hp : 3*(H*H) ≤ H*(H*H) := Nat.mul_le_mul_right _ hH
  unfold gridSide
  nlinarith [show H^3=H*(H*H) by ring]

theorem insertionPoint_encoding (M H k l : ℕ) (hH : 3 ≤ H) (hM : M ≤ H)
    (r : Point) (delta : ℚ) (hr : PointBounded r H k) (hd : Bounded delta (H^l))
    (ij : Fin (gridSide M) × Fin (gridSide M)) :
    PointBounded (insertionPoint r delta ij) H (k+l+10) := by
  have h1 : 1 ≤ H := by omega
  have h3 : 1 ≤ H^3 := Nat.one_le_pow _ _ (by omega)
  have hm := gridSide_encoding_bound M H hH hM
  have hden : Bounded ((gridSide M:ℚ)+1) (H^3) := by
    exact_mod_cast bounded_nat (gridSide M+1) (H^3) hm h3
  have hnum (i : Fin (gridSide M)) : Bounded ((i.val:ℚ)+1) (H^3) := by
    have hi : i.val+1 ≤ H^3 := by omega
    exact_mod_cast bounded_nat (i.val+1) (H^3) hi h3
  have hhalf := (bounded_nat_pow 1 H (by omega) h1).div_pow
    (bounded_nat_pow 2 H (by omega) h1)
  have hc (q : ℚ) (hq : Bounded q (H^k)) (i : Fin (gridSide M)) :
      Bounded (q+delta*(((i.val:ℚ)+1)/((gridSide M:ℚ)+1)-1/2)) (H^(k+l+10)) := by
    have hh := hq.add_pow (hd.mul_pow ((hnum i).div_pow hden |>.sub_pow hhalf (by omega))) (by omega)
    convert hh using 1
  rw [insertion_coordinate]
  exact ⟨hc r.1 hr.1 ij.1,hc r.2 hr.2 ij.2⟩

/-- Every point selected by the actual fixed-grid GP construction satisfies
the same polynomial exponent; the selected index need not be predicted. -/
theorem placed_encoding (M H k : ℕ) (hH : 100 ≤ H) (hM : M ≤ H)
    (B R : Finset Point) (hB : ∀a∈B, PointBounded a H k)
    (hR : ∀r∈R, PointBounded r H k) (r p : Point) (hr : r∈R)
    (hp : Placed M (constructionRadius B R) r p) :
    PointBounded p H (B.card*(2*k+2)+9*k+19) := by
  obtain ⟨ij,rfl,hvalid⟩ := hp
  have hh := insertionPoint_encoding M H k (B.card*(2*k+2)+8*k+9)
    (by omega) hM r (constructionRadius B R) (hR r hr)
    (constructionRadius_encoding B R H k hH hB hR) ij
  convert hh using 1; ring

/-- Converting a power certificate to a binary-size certificate is exact. -/
theorem binary_certificate {q : ℚ} (L k : ℕ) (hq : Bounded q ((2^L)^k)) :
    ∃ n d : ℤ, |n| ≤ (2:ℤ)^(L*k) ∧ |d| ≤ (2:ℤ)^(L*k) ∧ d≠0 ∧ q=(n:ℚ)/(d:ℚ) := by
  simpa only [Bounded,Nat.cast_pow,Nat.cast_ofNat,pow_mul] using hq

/-- The actual GP output has signed binary numerators and nonzero signed
denominators of at most `L * (B.card*(2*k+2)+9*k+19) + 1` magnitude bits.
No lower bound on the selected determinant is an input to this statement. -/
theorem placed_binary_coordinates (M L k : ℕ) (hL : 100 ≤ 2^L) (hM : M ≤ 2^L)
    (B R : Finset Point) (hB : ∀a∈B, PointBounded a (2^L) k)
    (hR : ∀r∈R, PointBounded r (2^L) k) (r p : Point) (hr : r∈R)
    (hp : Placed M (constructionRadius B R) r p) :
    ∃ nx dx ny dy : ℤ,
      |nx| ≤ (2:ℤ)^(L*(B.card*(2*k+2)+9*k+19)) ∧
      |dx| ≤ (2:ℤ)^(L*(B.card*(2*k+2)+9*k+19)) ∧ dx≠0 ∧ p.1=(nx:ℚ)/(dx:ℚ) ∧
      |ny| ≤ (2:ℤ)^(L*(B.card*(2*k+2)+9*k+19)) ∧
      |dy| ≤ (2:ℤ)^(L*(B.card*(2*k+2)+9*k+19)) ∧ dy≠0 ∧ p.2=(ny:ℚ)/(dy:ℚ) := by
  have hh := placed_encoding M (2^L) k hL hM B R hB hR r p hr hp
  obtain ⟨nx,dx,hx⟩ := binary_certificate L _ hh.1
  obtain ⟨ny,dy,hy⟩ := binary_certificate L _ hh.2
  exact ⟨nx,dx,ny,dy,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2,hy⟩

#print axioms Bounded.add
#print axioms Bounded.mul
#print axioms Bounded.inv
#print axioms bounded_sum_pow
#print axioms macroSpacing_encoding
#print axioms scales_encoding
#print axioms orient_encoding
#print axioms orientationMargin_encoding
#print axioms baseBudget_encoding
#print axioms constructionRadius_encoding
#print axioms gridSide_encoding_bound
#print axioms insertionPoint_encoding
#print axioms placed_encoding
#print axioms binary_certificate
#print axioms placed_binary_coordinates

end Q4.Candidate.RationalEncoding

