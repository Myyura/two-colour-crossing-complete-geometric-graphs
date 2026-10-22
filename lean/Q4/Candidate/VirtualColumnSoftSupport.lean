import Q4.Candidate.VirtualColumnSoftRows

namespace Q4.Candidate.VirtualColumnSoftRows
open Q4.Candidate.GridCounts Q4.Candidate.VirtualColumnField
open Q4.Candidate.VirtualColumnMidpoint Q4.Candidate.VirtualColumnShape

theorem rho_small (B O : ℕ) (hO : 1000≤O) (hBO : O≤B) : rho B O≤1/500 := by
  have ho : (1000:ℝ)≤O := by exact_mod_cast hO
  have hb : (1000:ℝ)≤B := by exact_mod_cast (hO.trans hBO)
  have h1 := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1000) ho
  have h2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1000) hb
  unfold rho
  linarith

theorem small_shape_support (s : ℝ) (hs : |s|≤1) (hshape : |shape s|<7/64) :
    (-1/8≤s ∧ s≤1/8) ∨ (-1≤s ∧ s≤ -7/8) ∨ (7/8≤s ∧ s≤1) := by
  have hprod : |shape s|=|s| * (1-|s|) := by
    unfold shape
    rw [abs_mul,abs_of_nonneg (show 0≤1-|s| by linarith)]
  rw [hprod] at hshape
  by_cases hc : |s|≤1/8
  · left
    have hh := abs_le.mp hc
    constructor <;> linarith
  · have hc' : 1/8< |s| := lt_of_not_ge hc
    have hout : 7/8≤ |s| := by
      by_contra hn
      have hh : |s|<7/8 := lt_of_not_ge hn
      have hp := mul_nonneg (le_of_lt (sub_pos.mpr hc')) (le_of_lt (sub_pos.mpr hh))
      nlinarith
    have hb := abs_le.mp hs
    rcases le_abs.mp hout with hp | hn
    · exact Or.inr (Or.inr ⟨hp,hb.2⟩)
    · exact Or.inr (Or.inl ⟨by linarith,by linarith⟩)

theorem soft_supported (B O r : ℕ) (hO : 1000≤O) (hBO : O≤B) (hr : r≤O)
    (z : ℝ) (hz : z≤1/100) :
    softRows B O r z ⊆ softBand B O r z (-1/8) (1/8) ∪
      (softBand B O r z (-1) (-7/8) ∪ softBand B O r z (7/8) 1) := by
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
  have hsigned := virtualField_shape_estimate B O r (by omega) hr k
  change |field B O r k/((B:ℝ)*O)+shape (coord B O r k)|≤6*rho B O at hsigned
  have hfield : |field B O r k/((B:ℝ)*O)|≤z := by
    rw [abs_div,abs_of_pos (mul_pos hb ho),div_le_iff₀ (mul_pos hb ho)]
    exact hsoft
  have htri := abs_sub_le (field B O r k/((B:ℝ)*O)+shape (coord B O r k)) 0
    (field B O r k/((B:ℝ)*O))
  simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left] at htri
  have hsmall : |shape (coord B O r k)|<7/64 := by
    linarith [rho_small B O hO hBO]
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

/-- The virtual-column instance of manuscript (4.14), for every virtual rank,
with no assumed support or increment formula. -/
theorem virtual_soft_card (B O r : ℕ) (hO : 1000≤O) (hBO : O≤B) (hr : r≤O)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1/100) :
    ((softRows B O r z).card:ℝ)≤12*(B:ℝ)*z+3 := by
  have hc := band_soft_card B O r hO hBO hr z (-1/8) (1/8) hz (Or.inl ⟨rfl,rfl⟩)
  have hl := band_soft_card B O r hO hBO hr z (-1) (-7/8) hz (Or.inr (Or.inl ⟨rfl,rfl⟩))
  have hh := band_soft_card B O r hO hBO hr z (7/8) 1 hz (Or.inr (Or.inr ⟨rfl,rfl⟩))
  have hsub := Finset.card_le_card (soft_supported B O r hO hBO hr z hz1)
  have hu1 := Finset.card_union_le (softBand B O r z (-1/8) (1/8))
    (softBand B O r z (-1) (-7/8) ∪ softBand B O r z (7/8) 1)
  have hu2 := Finset.card_union_le (softBand B O r z (-1) (-7/8)) (softBand B O r z (7/8) 1)
  have htotal : (softRows B O r z).card≤(softBand B O r z (-1/8) (1/8)).card+
      (softBand B O r z (-1) (-7/8)).card+(softBand B O r z (7/8) 1).card := by omega
  have htotal' : ((softRows B O r z).card:ℝ)≤((softBand B O r z (-1/8) (1/8)).card:ℝ)+
      ((softBand B O r z (-1) (-7/8)).card:ℝ)+((softBand B O r z (7/8) 1).card:ℝ) := by
    exact_mod_cast htotal
  linarith

end Q4.Candidate.VirtualColumnSoftRows
#print axioms Q4.Candidate.VirtualColumnSoftRows.soft_supported
#print axioms Q4.Candidate.VirtualColumnSoftRows.virtual_soft_card
