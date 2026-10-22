import Q4.Candidate.VirtualColumnSoftSupport

/-! Actual ordinary-fan responses. The input package contains only rational
coordinate and index separation conditions, never a field/soft-row estimate. -/
open scoped BigOperators
namespace Q4.Candidate.OrdinaryResponse
open Q4.Candidate.GridCounts Q4.Candidate.VirtualColumnField
open Q4.Candidate.VirtualColumnMidpoint Q4.Candidate.VirtualColumnShape
open Q4.Candidate.VirtualColumnSoftRows

structure Geometry (B O r : ℕ) where
  ys : Fin O → ℚ
  a : ℚ
  mu : ℚ
  parent : Finset (Fin O)
  even : Even B
  unit_a : |a|≤1
  unit_y : ∀j, |ys j|≤1
  mu_pos : 0<mu
  mu_le : mu≤1
  clone : ∀j∈parent, 3*((B:ℚ)+1)*|ys j-a|≤mu
  sep : ∀j∉parent, 5*mu≤|ys j-a|
  left : ∀j∉parent, ys j<a ↔ j.val<r
  right : ∀j∉parent, a<ys j ↔ r≤j.val

noncomputable def actualField {B O r : ℕ} (d : Geometry B O r) (k : Fin B) : ℝ :=
  (ordinaryField (spin : Fin B × Fin O → ℤ) d.ys d.a d.mu k:ℝ)

noncomputable def response {B O r : ℕ} (d : Geometry B O r) (k : Fin B) : Bool :=
  decide (actualField d k<0)

noncomputable def responseSpin {B O r : ℕ} (d : Geometry B O r) (k : Fin B) : ℝ :=
  if response d k then 1 else -1

theorem actual_comparison {B O r : ℕ} (d : Geometry B O r) (k : Fin B) :
    |actualField d k-field B O r k|≤2*(B:ℝ)*d.parent.card := by
  have h := ordinary_field_error (spin : Fin B × Fin O → ℤ)
    (fun p => le_of_eq (spin_abs p)) d.ys d.a d.mu r d.parent k
    d.unit_a d.unit_y d.mu_pos d.mu_le d.sep d.left d.right
  have h' : |(ordinaryField (spin : Fin B × Fin O → ℤ) d.ys d.a d.mu k:ℝ)-
      (virtualField (spin : Fin B × Fin O → ℤ) r k.val:ℝ)|≤2*(B:ℝ)*d.parent.card := by
    exact_mod_cast h
  exact h'

theorem actual_increment_comparison {B O r : ℕ} (d : Geometry B O r)
    (k l : Fin B) (hl : l.val=k.val+1) (hcut : l.val≠B/2) :
    |(actualField d l-actualField d k)-(field B O r l-field B O r k)|≤2*(d.parent.card:ℝ) := by
  have h := ordinary_field_increment_error (spin : Fin B × Fin O → ℤ)
    (fun p => le_of_eq (spin_abs p)) d.ys d.a d.mu r d.parent k l d.even hl hcut
    d.unit_a d.unit_y d.mu_pos d.mu_le d.clone d.sep d.left d.right
  dsimp [actualField,field]
  exact_mod_cast h

theorem actual_shape_estimate {B O r : ℕ} (d : Geometry B O r) (hO : 0<O) (hr : r≤O) (k : Fin B) :
    |actualField d k/((B:ℝ)*O)+shape (coord B O r k)|≤6*rho B O+2*(d.parent.card:ℝ)/O := by
  have hb : (0:ℝ)<B := by exact_mod_cast k.pos
  have ho : (0:ℝ)<O := by exact_mod_cast hO
  have hc := actual_comparison d k
  have hdiff : |actualField d k/((B:ℝ)*O)-field B O r k/((B:ℝ)*O)|≤2*(d.parent.card:ℝ)/O := by
    rw [←sub_div,abs_div,abs_of_pos (mul_pos hb ho),div_le_iff₀ (mul_pos hb ho)]
    have he : 2*(d.parent.card:ℝ)/O*((B:ℝ)*O)=2*(B:ℝ)*d.parent.card := by field_simp
    rw [he]
    exact hc
  have hv := virtualField_shape_estimate B O r hO hr k
  change |field B O r k/((B:ℝ)*O)+shape (coord B O r k)|≤6*rho B O at hv
  have ht := abs_add_le
    (actualField d k/((B:ℝ)*O)-field B O r k/((B:ℝ)*O))
    (field B O r k/((B:ℝ)*O)+shape (coord B O r k))
  have he : (actualField d k/((B:ℝ)*O)-field B O r k/((B:ℝ)*O))+
      (field B O r k/((B:ℝ)*O)+shape (coord B O r k)) =
      actualField d k/((B:ℝ)*O)+shape (coord B O r k) := by ring
  rw [he] at ht
  linarith

theorem response_minimizes {B O r : ℕ} (d : Geometry B O r) (k : Fin B) (b : Bool) :
    probeCost Q4.Candidate.CanonicalField.canonical (response d k) d.ys d.a d.mu k ≤
      probeCost Q4.Candidate.CanonicalField.canonical b d.ys d.a d.mu k := by
  have he := ordinaryField_eq_cost_difference Q4.Candidate.CanonicalField.canonical d.ys d.a d.mu k
  rw [←canonical_spin_eq] at he
  have her : actualField d k =
      (probeCost Q4.Candidate.CanonicalField.canonical true d.ys d.a d.mu k:ℝ)-
      (probeCost Q4.Candidate.CanonicalField.canonical false d.ys d.a d.mu k:ℝ) := by
    unfold actualField
    exact_mod_cast he
  by_cases hg : actualField d k<0
  · have hc : response d k=true := by simp [response,hg]
    rw [hc]
    cases b
    · have hlt : (probeCost Q4.Candidate.CanonicalField.canonical true d.ys d.a d.mu k:ℝ)≤
          (probeCost Q4.Candidate.CanonicalField.canonical false d.ys d.a d.mu k:ℝ) := by linarith
      exact_mod_cast hlt
    · exact le_refl _
  · have hc : response d k=false := by simp [response,hg]
    rw [hc]
    cases b
    · exact le_refl _
    · have hlt : (probeCost Q4.Candidate.CanonicalField.canonical false d.ys d.a d.mu k:ℝ)≤
          (probeCost Q4.Candidate.CanonicalField.canonical true d.ys d.a d.mu k:ℝ) := by linarith
      exact_mod_cast hlt

theorem actual_shape_error_small {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514) (k : Fin B) :
    |actualField d k/((B:ℝ)*O)+shape (coord B O r k)|≤1/60 := by
  have h := actual_shape_estimate d (by omega) hr k
  have he : 2*(d.parent.card:ℝ)/O=2*((d.parent.card:ℝ)/O) := by ring
  rw [he] at h
  linarith [rho_small B O hO hBO]

theorem positive_shape (s : ℝ) (hs : 1/9≤s) (hs' : s≤8/9) : 8/81≤shape s := by
  unfold shape
  rw [abs_of_nonneg (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs')]

theorem negative_shape (s : ℝ) (hs : -8/9≤s) (hs' : s≤ -1/9) : shape s≤ -8/81 := by
  have h := positive_shape (-s) (by linarith) (by linarith)
  simp only [shape,abs_neg] at h ⊢
  nlinarith

theorem early_middle_response {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
    (hearly : (r:ℝ)/O≤1/514) (k : Fin B) (hk : 1/8≤u B k ∧ u B k≤7/8) :
    actualField d k<0 ∧ response d k=true ∧ responseSpin d k=1 := by
  have hv0 : 0≤(r:ℝ)/O := by positivity
  have hs1 : 1/9≤coord B O r k := by unfold coord; linarith [hk.2]
  have hs2 : coord B O r k≤8/9 := by unfold coord; linarith [hk.1]
  have hshape := positive_shape _ hs1 hs2
  have herr := (abs_le.mp (actual_shape_error_small d hO hBO hr hW k)).2
  have hnorm : actualField d k/((B:ℝ)*O)<0 := by linarith
  have hB : 0<B := k.pos
  have hOp : 0<O := by omega
  have hg : actualField d k<0 := by
    have h := (div_lt_iff₀ (by positivity : (0:ℝ)<(B:ℝ)*O)).mp hnorm
    simpa only [zero_mul] using h
  have hc : response d k=true := by simp [response,hg]
  exact ⟨hg,hc,by simp [responseSpin,hc]⟩

theorem late_middle_response {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
    (hlate : 1-1/514≤(r:ℝ)/O) (k : Fin B) (hk : 1/8≤u B k ∧ u B k≤7/8) :
    0<actualField d k ∧ response d k=false ∧ responseSpin d k= -1 := by
  have ho : (0:ℝ)<O := by exact_mod_cast (show 0<O by omega)
  have hv1 : (r:ℝ)/O≤1 := by rw [div_le_one ho]; exact_mod_cast hr
  have hs1 : -8/9≤coord B O r k := by unfold coord; linarith [hk.2]
  have hs2 : coord B O r k≤ -1/9 := by unfold coord; linarith [hk.1]
  have hshape := negative_shape _ hs1 hs2
  have herr := (abs_le.mp (actual_shape_error_small d hO hBO hr hW k)).1
  have hnorm : 0<actualField d k/((B:ℝ)*O) := by linarith
  have hB : 0<B := k.pos
  have hOp : 0<O := by omega
  have hg : 0<actualField d k := by
    have h := (lt_div_iff₀ (by positivity : (0:ℝ)<(B:ℝ)*O)).mp hnorm
    simpa only [zero_mul] using h
  have hc : response d k=false := by simp [response,not_lt.mpr (le_of_lt hg)]
  exact ⟨hg,hc,by simp [responseSpin,hc]⟩


theorem responseSpin_bounds {B O r : ℕ} (d : Geometry B O r) (k : Fin B) :
    -1≤responseSpin d k ∧ responseSpin d k≤1 := by
  unfold responseSpin
  split <;> norm_num

theorem middle_index_coordinates (B n : ℕ) (hB : B=8*n) (k : Fin B)
    (hk : n≤k.val ∧ k.val<7*n) : 1/8≤u B k ∧ u B k≤7/8 := by
  have hb : (0:ℝ)<B := by exact_mod_cast k.pos
  have he : (B:ℝ)=8*(n:ℝ) := by exact_mod_cast hB
  have hk1 : (n:ℝ)≤k.val := by exact_mod_cast hk.1
  have hk2 : (k.val:ℝ)+1≤7*n := by exact_mod_cast hk.2
  unfold u
  constructor
  · rw [le_div_iff₀ hb]
    linarith
  · rw [div_le_iff₀ hb]
    linarith

theorem half_weights_of_middle (B n : ℕ) (hB : B=8*n) (f : Fin B → ℝ)
    (hf : ∀k, -1≤f k ∧ f k≤1) (hmid : ∀k, n≤k.val → k.val<7*n → f k=1) :
    (B:ℝ)/4≤(∑k : Fin B, if k.val<B/2 then f k else 0) ∧
    (B:ℝ)/4≤(∑k : Fin B, if B/2≤k.val then f k else 0) ∧
    (B:ℝ)/2≤∑k : Fin B, f k := by
  have hhalf : B/2=4*n := by omega
  have hn : n≤B := by omega
  have h4n : 4*n≤B := by omega
  have h7n : 7*n≤B := by omega
  have he : (B:ℝ)=8*(n:ℝ) := by exact_mod_cast hB
  have hleft (k : Fin B) :
      (if k.val<4*n then (1:ℝ) else 0)-2*(if k.val<n then 1 else 0) ≤
      (if k.val<4*n then f k else 0) := by
    by_cases hk : k.val<4*n
    · by_cases hkn : k.val<n
      · simp only [hk,hkn,ite_true]
        linarith [(hf k).1]
      · have hkm := hmid k (by omega) (by omega)
        simp [hk,hkn,hkm]
    · have hkn : ¬k.val<n := by omega
      simp [hk,hkn]
  have hright (k : Fin B) :
      (if k.val<4*n then (0:ℝ) else 1)-2*(if k.val<7*n then 0 else 1) ≤
      (if 4*n≤k.val then f k else 0) := by
    by_cases hk : k.val<4*n
    · have hkn : k.val<7*n := by omega
      simp [hk,hkn,show ¬4*n≤k.val by omega]
    · by_cases hkn : k.val<7*n
      · have hkm := hmid k (by omega) hkn
        simp [hk,hkn,hkm,show 4*n≤k.val by omega]
      · simp only [hk,hkn,ite_false,show 4*n≤k.val by omega,ite_true]
        linarith [(hf k).1]
  have hl := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hleft k)
  have hr := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hright k)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,prefix_constant B (4*n) h4n,
    prefix_constant B n hn] at hl
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,suffix_constant B (4*n) h4n,
    suffix_constant B (7*n) h7n] at hr
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,mul_one] at hl hr
  have hl' : (B:ℝ)/4≤∑k : Fin B, if k.val<B/2 then f k else 0 := by
    rw [hhalf]
    linarith
  have hr' : (B:ℝ)/4≤∑k : Fin B, if B/2≤k.val then f k else 0 := by
    rw [hhalf]
    linarith
  have hsum : (∑k : Fin B, if k.val<B/2 then f k else 0)+
      (∑k : Fin B, if B/2≤k.val then f k else 0) = ∑k : Fin B, f k := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.val<B/2
    · simp [hk,not_le.mpr hk]
    · simp [hk,not_lt.mp hk]
  exact ⟨hl',hr',by linarith⟩

theorem early_half_weights {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (h8 : 8∣B)
    (hW : (d.parent.card:ℝ)/O≤1/514) (hearly : (r:ℝ)/O≤1/514) :
    (B:ℝ)/4≤(∑k : Fin B, if k.val<B/2 then responseSpin d k else 0) ∧
    (B:ℝ)/4≤(∑k : Fin B, if B/2≤k.val then responseSpin d k else 0) ∧
    (B:ℝ)/2≤∑k : Fin B, responseSpin d k := by
  obtain ⟨n,hn⟩ := h8
  apply half_weights_of_middle B n hn (responseSpin d) (responseSpin_bounds d)
  intro k hk1 hk2
  exact (early_middle_response d hO hBO hr hW hearly k
    (middle_index_coordinates B n hn k ⟨hk1,hk2⟩)).2.2

theorem late_half_weights {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (h8 : 8∣B)
    (hW : (d.parent.card:ℝ)/O≤1/514) (hlate : 1-1/514≤(r:ℝ)/O) :
    (∑k : Fin B, if k.val<B/2 then responseSpin d k else 0)≤ -(B:ℝ)/4 ∧
    (∑k : Fin B, if B/2≤k.val then responseSpin d k else 0)≤ -(B:ℝ)/4 ∧
    (∑k : Fin B, responseSpin d k)≤ -(B:ℝ)/2 := by
  obtain ⟨n,hn⟩ := h8
  have h := half_weights_of_middle B n hn (fun k => -responseSpin d k) (by
    intro k
    have hh := responseSpin_bounds d k
    constructor <;> linarith) (by
    intro k hk1 hk2
    have hh := (late_middle_response d hO hBO hr hW hlate k
      (middle_index_coordinates B n hn k ⟨hk1,hk2⟩)).2.2
    rw [hh]
    norm_num)
  have hl : (∑k : Fin B, if k.val<B/2 then -responseSpin d k else 0)=
      -(∑k : Fin B, if k.val<B/2 then responseSpin d k else 0) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split <;> simp
  have hr' : (∑k : Fin B, if B/2≤k.val then -responseSpin d k else 0)=
      -(∑k : Fin B, if B/2≤k.val then responseSpin d k else 0) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split <;> simp
  rw [hl,hr',Finset.sum_neg_distrib] at h
  rcases h with ⟨h1,h2,h3⟩
  constructor
  · linarith
  constructor <;> linarith

end Q4.Candidate.OrdinaryResponse
#print axioms Q4.Candidate.OrdinaryResponse.actual_shape_estimate
#print axioms Q4.Candidate.OrdinaryResponse.response_minimizes
#print axioms Q4.Candidate.OrdinaryResponse.early_middle_response
#print axioms Q4.Candidate.OrdinaryResponse.late_middle_response

#print axioms Q4.Candidate.OrdinaryResponse.early_half_weights
#print axioms Q4.Candidate.OrdinaryResponse.late_half_weights
