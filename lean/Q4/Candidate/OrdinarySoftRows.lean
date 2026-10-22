import Q4.Candidate.OrdinaryResponse

/-! Soft-row count for actual ordinary fans, with the central switch excluded
by the early/late geometric rank rather than by an assumed increment bound. -/
open scoped BigOperators
namespace Q4.Candidate.OrdinaryResponse
open Q4.Candidate.GridCounts Q4.Candidate.VirtualColumnField
open Q4.Candidate.VirtualColumnMidpoint Q4.Candidate.VirtualColumnShape
open Q4.Candidate.VirtualColumnSoftRows

noncomputable def ordinaryBand {B O r : ℕ} (d : Geometry B O r) (z L U : ℝ) : Finset (Fin B) :=
  Finset.univ.filter (fun k => |actualField d k|≤z*((B:ℝ)*O) ∧ L≤coord B O r k ∧ coord B O r k≤U)

noncomputable def ordinarySoftRows {B O r : ℕ} (d : Geometry B O r) (z : ℝ) : Finset (Fin B) :=
  Finset.univ.filter (fun k => |actualField d k|≤z*((B:ℝ)*O))

theorem ordinary_increment_small {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
    (k l : Fin B) (hl : l.val=k.val+1) (hcut : l.val≠B/2) :
    |(actualField d l-actualField d k)-(O:ℝ)*(1-2*|coord B O r k|)|≤(O:ℝ)/4 := by
  have ho : (0:ℝ)<O := by exact_mod_cast (show 0<O by omega)
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have hbig : (1000:ℝ)≤O := by exact_mod_cast hO
  have hOb : (O:ℝ)/B≤1 := by rw [div_le_one hb]; exact_mod_cast hBO
  have hW' := (div_le_iff₀ ho).mp hW
  have hactual := actual_increment_comparison d k l hl hcut
  have hvirtual := virtualField_increment_estimate B O r (by omega) hr k l hl
  rw [Int.cast_sub] at hvirtual
  change |(field B O r l-field B O r k)-(O:ℝ)*(1-2*|coord B O r k|)|≤_ at hvirtual
  have htri := abs_sub_le (actualField d l-actualField d k)
    (field B O r l-field B O r k) ((O:ℝ)*(1-2*|coord B O r k|))
  have he : 2*(O:ℝ)/B=2*((O:ℝ)/B) := by ring
  rw [he] at hvirtual
  linarith

theorem band_avoids_switch {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O)
    (hside : (r:ℝ)/O≤1/514 ∨ 1-1/514≤(r:ℝ)/O)
    (L U : ℝ) (hband : (L= -1/8 ∧ U=1/8) ∨ (L= -1 ∧ U= -7/8) ∨ (L=7/8 ∧ U=1))
    (k l : Fin B) (hl : l.val=k.val+1) (hc : L≤coord B O r k ∧ coord B O r k≤U) :
    l.val≠B/2 := by
  intro hcut
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have ho : (0:ℝ)<O := by exact_mod_cast (show 0<O by omega)
  have hbig : (1000:ℝ)≤B := by exact_mod_cast (hO.trans hBO)
  have hdiv : 2*(B/2)=B := by rcases d.even with ⟨n,hn⟩; omega
  have hk : 2*(k.val+1)=B := by omega
  have hk' : 2*((k.val:ℝ)+1)=B := by exact_mod_cast hk
  have hu : 3/8≤u B k ∧ u B k≤5/8 := by
    unfold u
    constructor
    · rw [le_div_iff₀ hb]
      linarith
    · rw [div_le_iff₀ hb]
      linarith
  have hv0 : 0≤(r:ℝ)/O := by positivity
  have hv1 : (r:ℝ)/O≤1 := by rw [div_le_one ho]; exact_mod_cast hr
  unfold coord at hc
  rcases hside with hearly | hlate <;>
    rcases hband with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> linarith [hc.1,hc.2,hu.1,hu.2]

theorem ordinary_band_card {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
    (hside : (r:ℝ)/O≤1/514 ∨ 1-1/514≤(r:ℝ)/O)
    (z L U : ℝ) (hz : 0≤z)
    (hband : (L= -1/8 ∧ U=1/8) ∨ (L= -1 ∧ U= -7/8) ∨ (L=7/8 ∧ U=1)) :
    ((ordinaryBand d z L U).card:ℝ)≤4*(B:ℝ)*z+1 := by
  have hB : 0<B := by omega
  have ho : (0:ℝ)<O := by exact_mod_cast (show 0<O by omega)
  let S := ordinaryBand d z L U
  have hsoft : ∀i∈S, |actualField d i|≤z*((B:ℝ)*O) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.1
  have hconvex (a b k : Fin B) (ha : a∈S) (hb : b∈S) (hak : a≤k) (hkb : k≤b) :
      L≤coord B O r k ∧ coord B O r k≤U := by
    have haa := (Finset.mem_filter.mp ha).2.2
    have hbb := (Finset.mem_filter.mp hb).2.2
    have h1 := coord_antitone B O r hB hak
    have h2 := coord_antitone B O r hB hkb
    constructor <;> linarith
  have hbound (f : Fin B → ℝ) (hs : ∀i∈S, |f i|≤z*((B:ℝ)*O))
      (hp : ∀a∈S, ∀b∈S, a≤b → (O:ℝ)/2*((b.val:ℝ)-a.val)≤f b-f a) :
      (S.card:ℝ)≤4*(B:ℝ)*z+1 := by
    have hh := soft_card_from_separation f S (z*((B:ℝ)*O)) ((O:ℝ)/2)
      (by positivity) (by positivity) hs hp
    have he : 2*(z*((B:ℝ)*O))/((O:ℝ)/2)=4*(B:ℝ)*z := by field_simp; ring
    simpa only [he] using hh
  have hcut (k l : Fin B) (hl : l.val=k.val+1) (hc : L≤coord B O r k ∧ coord B O r k≤U) :
      l.val≠B/2 := band_avoids_switch d hO hBO hr hside L U hband k l hl hc
  rcases hband with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · apply hbound (actualField d) hsoft
    intro a ha b hb hab
    apply step_telescope _ _ a b hab
    intro k l hl hak hlb
    have hkl : k≤l := by change k.val≤l.val; omega
    have hc := hconvex a b k ha hb hak (hkl.trans hlb)
    have habs : |coord B O r k|≤1/8 := abs_le.mpr (by constructor <;> linarith [hc.1,hc.2])
    have he := (abs_le.mp (ordinary_increment_small d hO hBO hr hW k l hl (hcut k l hl hc))).1
    nlinarith
  · apply hbound (fun k => -actualField d k) (by intro i hi; simpa using hsoft i hi)
    intro a ha b hb hab
    apply step_telescope _ _ a b hab
    intro k l hl hak hlb
    have hkl : k≤l := by change k.val≤l.val; omega
    have hc := hconvex a b k ha hb hak (hkl.trans hlb)
    have habs : 7/8≤ |coord B O r k| := by rw [abs_of_nonpos (by linarith)]; linarith
    have he := (abs_le.mp (ordinary_increment_small d hO hBO hr hW k l hl (hcut k l hl hc))).2
    nlinarith
  · apply hbound (fun k => -actualField d k) (by intro i hi; simpa using hsoft i hi)
    intro a ha b hb hab
    apply step_telescope _ _ a b hab
    intro k l hl hak hlb
    have hkl : k≤l := by change k.val≤l.val; omega
    have hc := hconvex a b k ha hb hak (hkl.trans hlb)
    have habs : 7/8≤ |coord B O r k| := by rw [abs_of_nonneg (by linarith)]; linarith
    have he := (abs_le.mp (ordinary_increment_small d hO hBO hr hW k l hl (hcut k l hl hc))).2
    nlinarith

theorem ordinary_soft_supported {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
    (z : ℝ) (hz : z≤1/100) :
    ordinarySoftRows d z ⊆ ordinaryBand d z (-1/8) (1/8) ∪
      (ordinaryBand d z (-1) (-7/8) ∪ ordinaryBand d z (7/8) 1) := by
  intro k hk
  have hsoft := (Finset.mem_filter.mp hk).2
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have ho : (0:ℝ)<O := by exact_mod_cast (show 0<O by omega)
  have hv0 : 0≤(r:ℝ)/O := by positivity
  have hv1 : (r:ℝ)/O≤1 := by rw [div_le_one ho]; exact_mod_cast hr
  have hs : |coord B O r k|≤1 := by
    unfold coord
    rw [abs_le]
    constructor <;> linarith [u_pos B (by omega) k,u_lt_one B (by omega) k]
  have hsigned := actual_shape_error_small d hO hBO hr hW k
  have hfield : |actualField d k/((B:ℝ)*O)|≤z := by
    rw [abs_div,abs_of_pos (mul_pos hb ho),div_le_iff₀ (mul_pos hb ho)]
    exact hsoft
  have htri := abs_sub_le (actualField d k/((B:ℝ)*O)+shape (coord B O r k)) 0
    (actualField d k/((B:ℝ)*O))
  simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left] at htri
  have hsmall : |shape (coord B O r k)|<7/64 := by linarith
  rcases small_shape_support (coord B O r k) hs hsmall with hc | hl | hh
  · apply Finset.mem_union.mpr
    left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsoft,hc⟩
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsoft,hl⟩
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsoft,hh⟩

/-- Actual ordinary-fan instance of manuscript (4.14). Geometry contains
rational-coordinate hypotheses only; both field estimates and all finite
soft-set cardinality bounds are proved, including the central-switch issue. -/
theorem ordinary_soft_card {B O r : ℕ} (d : Geometry B O r)
    (hO : 1000≤O) (hBO : O≤B) (hr : r≤O) (hW : (d.parent.card:ℝ)/O≤1/514)
    (hside : (r:ℝ)/O≤1/514 ∨ 1-1/514≤(r:ℝ)/O)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((ordinarySoftRows d z).card:ℝ)≤12*(B:ℝ)*z+3 := by
  have hc := ordinary_band_card d hO hBO hr hW hside z (-1/8) (1/8) hz (Or.inl ⟨rfl,rfl⟩)
  have hl := ordinary_band_card d hO hBO hr hW hside z (-1) (-7/8) hz (Or.inr (Or.inl ⟨rfl,rfl⟩))
  have hh := ordinary_band_card d hO hBO hr hW hside z (7/8) 1 hz (Or.inr (Or.inr ⟨rfl,rfl⟩))
  have hsub := Finset.card_le_card (ordinary_soft_supported d hO hBO hr hW z hz1)
  have hu1 := Finset.card_union_le (ordinaryBand d z (-1/8) (1/8))
    (ordinaryBand d z (-1) (-7/8) ∪ ordinaryBand d z (7/8) 1)
  have hu2 := Finset.card_union_le (ordinaryBand d z (-1) (-7/8)) (ordinaryBand d z (7/8) 1)
  have htotal : (ordinarySoftRows d z).card≤(ordinaryBand d z (-1/8) (1/8)).card+
      (ordinaryBand d z (-1) (-7/8)).card+(ordinaryBand d z (7/8) 1).card := by omega
  have htotal' : ((ordinarySoftRows d z).card:ℝ)≤((ordinaryBand d z (-1/8) (1/8)).card:ℝ)+
      ((ordinaryBand d z (-1) (-7/8)).card:ℝ)+((ordinaryBand d z (7/8) 1).card:ℝ) := by exact_mod_cast htotal
  linarith

end Q4.Candidate.OrdinaryResponse
#print axioms Q4.Candidate.OrdinaryResponse.ordinary_increment_small
#print axioms Q4.Candidate.OrdinaryResponse.band_avoids_switch
#print axioms Q4.Candidate.OrdinaryResponse.ordinary_soft_card
