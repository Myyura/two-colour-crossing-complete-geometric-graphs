import Q4.Candidate.VirtualColumnShape
import Mathlib.Algebra.BigOperators.Intervals

/-! Actual finite soft-row counts, with all fields instantiated by canonical
virtual-column sums. Generic finite sequence lemmas are proved here as helpers. -/
open scoped BigOperators
namespace Q4.Candidate.VirtualColumnSoftRows
open Q4.Candidate.GridCounts Q4.Candidate.VirtualColumnField
open Q4.Candidate.VirtualColumnMidpoint Q4.Candidate.VirtualColumnShape

theorem step_telescope {B : ℕ} (f : Fin B → ℝ) (d : ℝ) (a b : Fin B) (hab : a≤b)
    (hstep : ∀ k l : Fin B, l.val=k.val+1 → a≤k → l≤b → d≤f l-f k) :
    d*((b.val:ℝ)-a.val)≤f b-f a := by
  let g : ℕ → ℝ := fun i => if hi : i<B then f ⟨i,hi⟩ else 0
  have hv : a.val≤b.val := hab
  have ht : (∑ i ∈ Finset.Ico a.val b.val, (g (i+1)-g i))=f b-f a := by
    rw [Finset.sum_Ico_eq_sub _ hv,Finset.sum_range_sub,Finset.sum_range_sub]
    simp [g,a.isLt,b.isLt]
  have he := Finset.sum_le_sum (s:=Finset.Ico a.val b.val) (f:=fun _ => d)
    (g:=fun i => g (i+1)-g i) (by
      intro i hi
      have hh := Finset.mem_Ico.mp hi
      have hil : i+1<B := by omega
      have hik : i<B := by omega
      have hk := hstep ⟨i,hik⟩ ⟨i+1,hil⟩ rfl hh.1 (by exact hh.2)
      simpa [g,hik,hil] using hk)
  rw [ht] at he
  simpa only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul,Nat.cast_sub hv,mul_comm] using he

theorem soft_card_from_separation {B : ℕ} (f : Fin B → ℝ) (S : Finset (Fin B))
    (Z d : ℝ) (hZ : 0≤Z) (hd : 0<d) (hsoft : ∀i∈S, |f i|≤Z)
    (hsep : ∀a∈S, ∀b∈S, a≤b → d*((b.val:ℝ)-a.val)≤f b-f a) :
    (S.card:ℝ)≤2*Z/d+1 := by
  classical
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ha : a∈S := Finset.min'_mem S hS
    have hb : b∈S := Finset.max'_mem S hS
    have hab : a≤b := Finset.min'_le S b hb
    have hab' : (a.val:ℝ)≤b.val := by exact_mod_cast hab
    have hc := fin_card_le_span S a.val b.val hab' (by
      intro i hi
      constructor
      · exact_mod_cast (Finset.min'_le S i hi : a≤i)
      · exact_mod_cast (Finset.le_max' S i hi : i≤b))
    have hs := hsep a ha b hb hab
    have hsa := (abs_le.mp (hsoft a ha)).1
    have hsb := (abs_le.mp (hsoft b hb)).2
    have hspan : (b.val:ℝ)-a.val≤2*Z/d := by
      rw [le_div_iff₀ hd]
      nlinarith
    linarith
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

noncomputable def coord (B O r : ℕ) (k : Fin B) : ℝ := 1-u B k-(r:ℝ)/O

noncomputable def field (B O r : ℕ) (k : Fin B) : ℝ :=
  (virtualField (spin : Fin B × Fin O → ℤ) r k.val:ℝ)

noncomputable def softBand (B O r : ℕ) (z L U : ℝ) : Finset (Fin B) :=
  Finset.univ.filter (fun k => |field B O r k|≤z*((B:ℝ)*O) ∧ L≤coord B O r k ∧ coord B O r k≤U)

noncomputable def softRows (B O r : ℕ) (z : ℝ) : Finset (Fin B) :=
  Finset.univ.filter (fun k => |field B O r k|≤z*((B:ℝ)*O))

theorem coord_antitone (B O r : ℕ) (hB : 0<B) : Antitone (coord B O r) := by
  intro i j hij
  have h := u_mono B hB i j hij
  unfold coord
  linarith

theorem increment_error_small (B O r : ℕ) (hO : 1000≤O) (hBO : O≤B) (hr : r≤O)
    (k l : Fin B) (hl : l.val=k.val+1) :
    |(field B O r l-field B O r k)-(O:ℝ)*(1-2*|coord B O r k|)|≤(O:ℝ)/4 := by
  have ho : 0<O := by omega
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have hOb : (O:ℝ)/B≤1 := by rw [div_le_one hb]; exact_mod_cast hBO
  have hbig : (1000:ℝ)≤O := by exact_mod_cast hO
  have h := virtualField_increment_estimate B O r ho hr k l hl
  rw [Int.cast_sub] at h
  change |(field B O r l-field B O r k)-(O:ℝ)*(1-2*|coord B O r k|)|≤_ at h
  have he : 2*(O:ℝ)/B=2*((O:ℝ)/B) := by ring
  rw [he] at h
  linarith

theorem band_soft_card (B O r : ℕ) (hO : 1000≤O) (hBO : O≤B) (hr : r≤O)
    (z L U : ℝ) (hz : 0≤z)
    (hband : (L= -1/8 ∧ U=1/8) ∨ (L= -1 ∧ U= -7/8) ∨ (L=7/8 ∧ U=1)) :
    ((softBand B O r z L U).card:ℝ)≤4*(B:ℝ)*z+1 := by
  have hB : 0<B := by omega
  have ho : (0:ℝ)<O := by exact_mod_cast (show 0<O by omega)
  let S := softBand B O r z L U
  have hsoft : ∀i∈S, |field B O r i|≤z*((B:ℝ)*O) := by
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
  rcases hband with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · apply hbound (field B O r) hsoft
    intro a ha b hb hab
    apply step_telescope _ _ a b hab
    intro k l hl hak hlb
    have hkl : k≤l := by change k.val≤l.val; omega
    have hc := hconvex a b k ha hb hak (hkl.trans hlb)
    have habs : |coord B O r k|≤1/8 := abs_le.mpr (by constructor <;> linarith [hc.1,hc.2])
    have he := (abs_le.mp (increment_error_small B O r hO hBO hr k l hl)).1
    nlinarith
  · apply hbound (fun k => -field B O r k) (by intro i hi; simpa using hsoft i hi)
    intro a ha b hb hab
    apply step_telescope _ _ a b hab
    intro k l hl hak hlb
    have hkl : k≤l := by change k.val≤l.val; omega
    have hc := hconvex a b k ha hb hak (hkl.trans hlb)
    have habs : 7/8≤|coord B O r k| := by rw [abs_of_nonpos (by linarith)]; linarith
    have he := (abs_le.mp (increment_error_small B O r hO hBO hr k l hl)).2
    nlinarith
  · apply hbound (fun k => -field B O r k) (by intro i hi; simpa using hsoft i hi)
    intro a ha b hb hab
    apply step_telescope _ _ a b hab
    intro k l hl hak hlb
    have hkl : k≤l := by change k.val≤l.val; omega
    have hc := hconvex a b k ha hb hak (hkl.trans hlb)
    have habs : 7/8≤|coord B O r k| := by rw [abs_of_nonneg (by linarith)]; linarith
    have he := (abs_le.mp (increment_error_small B O r hO hBO hr k l hl)).2
    nlinarith

end Q4.Candidate.VirtualColumnSoftRows
#print axioms Q4.Candidate.VirtualColumnSoftRows.band_soft_card
