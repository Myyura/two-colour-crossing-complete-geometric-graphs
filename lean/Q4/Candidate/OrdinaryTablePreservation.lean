import Q4.Candidate.RankTablePreservation

namespace Q4.Candidate.OrdinaryTablePreservation
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.OrdinaryFan Q4.Candidate.OrientationPreservation
open Q4.Candidate.RankTablePreservation Q4.Candidate.UniformInsertion

theorem ordinary_clone_ray_nonzero (N : ℕ) (hN : Even N) (i : Fin N)
    (a c mu : ℚ) (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*((N:ℚ)+1)*|c-a| ≤ mu) :
    orient (ordinary a mu) (original c) (frame (frameParameter N i)) ≠ 0 := by
  have ht : frameParameter N i ≠ 0 := by
    intro he
    have hh := frameParameter_gap N hN i
    rw [he,abs_zero,mul_zero] at hh
    norm_num at hh
  have hs := ordinary_clone_sign a c mu (frameParameter N i) ha hc hm hm1
    (frameParameter_unit N i).le ht (indexed_clone_margin N hN i a c mu hclone)
  rcases lt_or_gt_of_ne ht with h|h
  · exact ne_of_lt (hs.2.mpr h)
  · exact ne_of_gt (hs.1.mpr h)

theorem ordinary_nonparent_ray_nonzero (a z mu t : ℚ)
    (ha : |a| ≤ 1) (hz : |z| ≤ 1) (ht : |t| ≤ 1) (hm : 0 < mu)
    (hsep : 5*mu ≤ |z-a|) : orient (ordinary a mu) (original z) (frame t) ≠ 0 := by
  exact nonparent_ray_nonzero _ a z t mu hm (by linarith)
    (ordinary_nonparent_sign a z mu t ha hz ht hm hsep)

/-- Full ordinary parent-clone prefix/suffix table after the common placement. -/
theorem placed_ordinary_clone_fan (M N : ℕ) (B R : Finset Point) (hN : Even N)
    (i k : Fin N) (a c mu : ℚ) (p : Point)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*((N:ℚ)+1)*|c-a| ≤ mu)
    (hfi : frame (frameParameter N i) ∈ B) (hfk : frame (frameParameter N k) ∈ B)
    (hcMem : original c ∈ B) (hr : ordinary a mu ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (ordinary a mu) p) :
    ProperCross p (frame (frameParameter N k)) (original c) (frame (frameParameter N i)) ↔
      (i < k ∧ k.val < N/2) ∨ (k < i ∧ N/2 ≤ k.val) := by
  have hvalid := ordinary_valid a mu (abs_le.mp ha).1 (abs_le.mp ha).2 hm hm1
  have hn (j : Fin N) := ordinary_clone_ray_nonzero N hN j a c mu ha hc hm hm1 hclone
  exact (fan_preserved_of_rays M B R (ordinary a mu) p c _ _ hvalid
    (frameParameter_unit N i).le (frameParameter_unit N k).le (hn i) (hn k)
    hfi hfk hcMem hr hproto hp).trans
    (ordinary_clone_indexed N hN i k a c mu ha hc hm hm1 hclone)

/-- Full ordinary nonparent virtual-macro-column table after placement. -/
theorem placed_ordinary_nonparent_fan (M N : ℕ) (B R : Finset Point)
    (i k : Fin N) (a z mu : ℚ) (p : Point)
    (ha : |a| ≤ 1) (hz : |z| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hsep : 5*mu ≤ |z-a|)
    (hfi : frame (frameParameter N i) ∈ B) (hfk : frame (frameParameter N k) ∈ B)
    (hzMem : original z ∈ B) (hr : ordinary a mu ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (ordinary a mu) p) :
    ProperCross p (frame (frameParameter N k)) (original z) (frame (frameParameter N i)) ↔
      (i < k ∧ z < a) ∨ (k < i ∧ a < z) := by
  have hvalid := ordinary_valid a mu (abs_le.mp ha).1 (abs_le.mp ha).2 hm hm1
  have hn (j : Fin N) := ordinary_nonparent_ray_nonzero a z mu (frameParameter N j)
    ha hz (frameParameter_unit N j).le hm hsep
  exact (fan_preserved_of_rays M B R (ordinary a mu) p z _ _ hvalid
    (frameParameter_unit N i).le (frameParameter_unit N k).le (hn i) (hn k)
    hfi hfk hzMem hr hproto hp).trans
    (ordinary_nonparent_indexed N i k a z mu ha hz hm hm1 hsep)

/-- Actual parent-clone/nonparent core determinants, including zero-crossing rows. -/
theorem ordinary_clone_core_determinants (N : ℕ) (hN : Even N) (k : Fin N)
    (a c z mu : ℚ) (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hz : |z| ≤ 1)
    (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*((N:ℚ)+1)*|c-a| ≤ mu) (hsep : 5*mu ≤ |z-a|) :
    orient (frame (frameParameter N k)) (original c) (ordinary a mu) ≠ 0 ∧
    orient (frame (frameParameter N k)) (original z) (ordinary a mu) ≠ 0 ∧
    orient (original c) (original z) (ordinary a mu) ≠ 0 := by
  have hcRay := ordinary_clone_ray_nonzero N hN k a c mu ha hc hm hm1 hclone
  have hzRay := ordinary_nonparent_ray_nonzero a z mu (frameParameter N k)
    ha hz (frameParameter_unit N k).le hm hsep
  have hsmall : 3*|c-a| ≤ mu := by
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0:ℚ) ≤ N) (abs_nonneg (c-a))]
  have hmargin := ordinary_clone_core_margin a c z mu ha hz hm hm1 hsmall
  have hne : z-c ≠ 0 := by
    intro he
    rw [sub_eq_zero.mp he] at hsep
    linarith
  refine ⟨?_,?_,?_⟩
  · rw [orient_cycle,orient_cycle,orient_reverse_last]
    exact neg_ne_zero.mpr hcRay
  · rw [orient_cycle,orient_cycle,orient_reverse_last]
    exact neg_ne_zero.mpr hzRay
  · rw [original_chord_orientation]
    exact mul_ne_zero (neg_ne_zero.mpr hne) (ne_of_lt hmargin)

theorem placed_ordinary_clone_core (M N : ℕ) (B R : Finset Point) (hN : Even N)
    (k : Fin N) (a c z mu : ℚ) (p : Point)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hz : |z| ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hclone : 3*((N:ℚ)+1)*|c-a| ≤ mu) (hsep : 5*mu ≤ |z-a|)
    (hframe : frame (frameParameter N k) ∈ B) (hcMem : original c ∈ B)
    (hzMem : original z ∈ B) (hr : ordinary a mu ∈ R)
    (hproto : ∀ q ∈ R, phi q < 0 ∧ |q.2| < 2)
    (hp : Placed M (constructionRadius B R) (ordinary a mu) p) :
    ProperCross p (frame (frameParameter N k)) (original c) (original z) ↔
      (k.val < N/2 ∧ a < z) ∨ (N/2 ≤ k.val ∧ z < a) := by
  have hdelta := constructionRadius_positive B R hproto
  have hbox := placed_in_box M _ hdelta _ p hp
  have hnz := ordinary_clone_core_determinants N hN k a c z mu ha hc hz hm hm1 hclone hsep
  have he := one_program_crossing_preserved B R _ _ _ _ p hframe hcMem hzMem hr
    (Or.inl hnz.1) (Or.inl hnz.2.1) (Or.inl hnz.2.2) _ hdelta
    (constructionRadius_bounds B R).2.2.2 (by linarith [hbox.1]) (by linarith [hbox.2])
  exact he.trans (ordinary_clone_core_indexed N hN k a c z mu ha hc hz hm hm1 hclone hsep)

end Q4.Candidate.OrdinaryTablePreservation

#print axioms Q4.Candidate.OrdinaryTablePreservation.ordinary_clone_ray_nonzero
#print axioms Q4.Candidate.OrdinaryTablePreservation.placed_ordinary_clone_fan
#print axioms Q4.Candidate.OrdinaryTablePreservation.placed_ordinary_nonparent_fan
#print axioms Q4.Candidate.OrdinaryTablePreservation.ordinary_clone_core_determinants
#print axioms Q4.Candidate.OrdinaryTablePreservation.placed_ordinary_clone_core
