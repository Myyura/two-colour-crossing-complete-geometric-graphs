import Q4.Candidate.CompleteBackground
import Q4.Candidate.CoreFixedPalette
import Mathlib.Data.Finset.Prod

/-! Palette forcing in the actual complete C-core objective. Every other
core edge remains freely colored in the local improvement argument. -/
namespace Q4.Candidate.CorePaletteForcing
open Q4.Candidate.CompleteDrawing Q4.Candidate.CompleteClassEnergy
open Q4.Candidate.CompleteBackground Q4.Candidate.ConvexSeparation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def setBit {O : ℕ} (κ : Inner O → Bool) (v : Inner O) (b : Bool) : Inner O → Bool :=
  fun c => if c=v then b else κ c

noncomputable def fanField {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (v : Inner O) : ℤ :=
  ∑t, if Cross ys ts rs (C v) (T t) then Q4.JointProbe.spin (τ t) else 0

noncomputable def unary {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (v : Inner O) (b : Bool) : ℝ :=
  ∑t, atom ys ts rs (C v) (T t) b (τ t)

theorem unary_difference {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (v : Inner O) :
    unary ys ts rs τ v true-unary ys ts rs τ v false=(fanField ys ts rs τ v:ℝ) := by
  unfold unary fanField
  rw [←Finset.sum_sub_distrib]
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : Cross ys ts rs (C v) (T t) <;> cases τ t <;> simp [atom,hc,Q4.JointProbe.spin]

theorem pair_atom_change_le {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (κ : Inner O → Bool) (v : Inner O) (b : Bool) (c d : Inner O) :
    atom ys ts rs (C c) (C d) (setBit κ v b c) (setBit κ v b d)-
      atom ys ts rs (C c) (C d) (κ c) (κ d)≤
      (if c=v then (1:ℝ) else 0)+(if d=v then 1 else 0) := by
  have hlo : (0:ℝ)≤atom ys ts rs (C c) (C d) (κ c) (κ d) := by unfold atom; split <;> norm_num
  have hhi : atom ys ts rs (C c) (C d) (setBit κ v b c) (setBit κ v b d)≤(1:ℝ) := by
    unfold atom; split <;> norm_num
  by_cases hc : c=v <;> by_cases hd : d=v
  · simp only [hc,hd,ite_true] at *; linarith
  · simp only [hc,hd,ite_true,ite_false,add_zero] at *; linarith
  · simp only [hc,hd,ite_true,ite_false,zero_add] at *; linarith
  · simp [setBit,hc,hd]

/-- Changing one core color can increase the complete CC pair cost by at
most the total number of core edges, independently of every other color. -/
theorem pair_change_le {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (κ : Inner O → Bool) (v : Inner O) (b : Bool) :
    halfSum (fun c d => atom ys ts rs (C c) (C d) (setBit κ v b c) (setBit κ v b d))-
      halfSum (fun c d => atom ys ts rs (C c) (C d) (κ c) (κ d))≤Fintype.card (Inner O) := by
  have hsum := Finset.sum_le_sum (fun (c : Inner O) (_ : c∈Finset.univ) =>
    Finset.sum_le_sum (fun (d : Inner O) (_ : d∈Finset.univ) => pair_atom_change_le ys ts rs κ v b c d))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hsum
  simp only [←Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one] at hsum
  unfold halfSum
  linarith

theorem unary_change {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (κ : Inner O → Bool) (v : Inner O) (b : Bool) :
    (∑c, unary ys ts rs τ c (setBit κ v b c))-(∑c, unary ys ts rs τ c (κ c))=
      unary ys ts rs τ v b-unary ys ts rs τ v (κ v) := by
  rw [←Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single v]
  · simp [setBit]
  · intro c _ hcv
    simp [setBit,hcv]
  · simp

/-- This strictly improves the actual complete CC+CT objective whenever one
palette edge is wrong. No colors of any other C edges are fixed. -/
theorem wrong_bit_improves {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (κ : Inner O → Bool) (v : Inner O) (b : Bool)
    (hdom : (Fintype.card (Inner O):ℝ)< (if b then -(fanField ys ts rs τ v:ℝ) else (fanField ys ts rs τ v:ℝ)))
    (hwrong : κ v≠b) :
    coreValue ys ts rs τ (setBit κ v b)<coreValue ys ts rs τ κ := by
  have hp := pair_change_le ys ts rs κ v b
  have hu := unary_change ys ts rs τ κ v b
  have hf := unary_difference ys ts rs τ v
  unfold coreValue cutSum
  change _+(∑c,unary ys ts rs τ c (setBit κ v b c))<_+(∑c,unary ys ts rs τ c (κ c))
  cases b <;> cases he : κ v <;> simp_all <;> linarith

/-- Every actual C-core minimizer obeys all designated palette bits
simultaneously; no palette agreement is assumed in the objective. -/
theorem every_minimizer_palette {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (τ : Fin B × Fin P → Bool) (palette : Finset (Inner O)) (bit : Inner O → Bool)
    (hdom : ∀v∈palette, (Fintype.card (Inner O):ℝ)<
      if bit v then -(fanField ys ts rs τ v:ℝ) else (fanField ys ts rs τ v:ℝ))
    (κ : Inner O → Bool) (hmin : ∀ψ, coreValue ys ts rs τ κ≤coreValue ys ts rs τ ψ) :
    ∀v∈palette, κ v=bit v := by
  intro v hv
  by_contra hwrong
  have hh := wrong_bit_improves ys ts rs τ κ v (bit v) (hdom v hv) hwrong
  exact (not_lt_of_ge (hmin _)) hh


/-- The actual core variables are all unordered original-original edges. -/
theorem core_card (O : ℕ) : Fintype.card (Inner O)=O.choose 2 := by
  rw [Fintype.card_subtype]
  simpa only [Finset.univ_product_univ,Finset.card_univ,Fintype.card_fin] using
    (Finset.card_product_filter_lt (s:=(Finset.univ : Finset (Fin O))))

theorem core_card_bound (O : ℕ) : (Fintype.card (Inner O):ℝ)≤(O:ℝ)^2/2 := by
  rw [core_card,Nat.choose_two_right]
  have hd := Nat.div_mul_le_self (O*(O-1)) 2
  have hm := Nat.mul_le_mul_left O (Nat.sub_le O 1)
  have hn : 2*(O*(O-1)/2)≤O*O := by omega
  have hr : (2:ℝ)*(O*(O-1)/2:ℕ)≤(O:ℝ)*O := by exact_mod_cast hn
  nlinarith

/-- A bound against O²/2 forces the actual global core minimizer, with all
CC edges and all CT costs still present and every other color unrestricted. -/
theorem every_minimizer_palette_of_square {O B P : ℕ} (ys : Fin O → ℚ) (ts : Fin B → ℚ)
    (rs : Fin P → Point) (τ : Fin B × Fin P → Bool) (palette : Finset (Inner O))
    (bit : Inner O → Bool)
    (hdom : ∀v∈palette, (O:ℝ)^2/2<
      if bit v then -(fanField ys ts rs τ v:ℝ) else (fanField ys ts rs τ v:ℝ))
    (κ : Inner O → Bool) (hmin : ∀ψ, coreValue ys ts rs τ κ≤coreValue ys ts rs τ ψ) :
    ∀v∈palette, κ v=bit v := by
  apply every_minimizer_palette ys ts rs τ palette bit ?_ κ hmin
  intro v hv
  exact lt_of_le_of_lt (core_card_bound O) (hdom v hv)

end Q4.Candidate.CorePaletteForcing
#print axioms Q4.Candidate.CorePaletteForcing.unary_difference
#print axioms Q4.Candidate.CorePaletteForcing.pair_change_le
#print axioms Q4.Candidate.CorePaletteForcing.wrong_bit_improves
#print axioms Q4.Candidate.CorePaletteForcing.every_minimizer_palette

#print axioms Q4.Candidate.CorePaletteForcing.core_card_bound
#print axioms Q4.Candidate.CorePaletteForcing.every_minimizer_palette_of_square
