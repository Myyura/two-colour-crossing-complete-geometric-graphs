import Q4.Candidate.GeometryEncoding

/-! A concrete finite macro set: the two actual source meshes and a central
rational dummy mesh. All scales use this same set. -/
namespace Q4.Candidate.MacroLayout
open Q4.Candidate.ConvexSeparation Q4.Candidate.OrdinaryNonincident
open Q4.Candidate.GlobalGeometryScales Q4.Candidate.SourceChordGeometry
open Q4.Candidate.GeometryEncoding Q4.Candidate.RationalEncoding

def dummyParameter (D : ℕ) (i : Fin D) : ℚ := -1/4+((i.val:ℚ)+1)/(2*((D:ℚ)+1))

noncomputable def macros (n q D : ℕ) : Finset ℚ :=
  ((Finset.univ : Finset (Fin (n*q))).image (fun i => macroParameter n q (-3/4) i.val)) ∪
  ((Finset.univ : Finset (Fin (n*q))).image (fun i => macroParameter n q (5/8) i.val)) ∪
  ((Finset.univ : Finset (Fin D)).image (dummyParameter D))

theorem source_mesh_bounds (n q : ℕ) (base : ℚ) (i : Fin (n*q)) :
    base < macroParameter n q base i.val ∧ macroParameter n q base i.val < base+1/8 := by
  have hden : (0:ℚ) < 8*((n*q:ℕ)+1) := by positivity
  have hi : (i.val:ℚ)+1 ≤ (n*q:ℕ) := by exact_mod_cast (show i.val+1 ≤ n*q by omega)
  have hp : (0:ℚ) < (i.val:ℚ)+1 := by positivity
  have hlo := div_pos hp hden
  have hhi : ((i.val:ℚ)+1)/(8*((n*q:ℕ)+1)) < 1/8 :=
    (div_lt_iff₀ hden).2 (by linarith)
  unfold macroParameter
  exact ⟨by linarith,by linarith⟩

theorem dummy_bounds (D : ℕ) (i : Fin D) : -1/4 < dummyParameter D i ∧ dummyParameter D i < 1/4 := by
  have hd : (0:ℚ) < 2*((D:ℚ)+1) := by positivity
  have hi : (i.val:ℚ)+1 ≤ D := by exact_mod_cast (show i.val+1 ≤ D by omega)
  have hp : (0:ℚ) < (i.val:ℚ)+1 := by positivity
  have hh : ((i.val:ℚ)+1)/(2*((D:ℚ)+1)) < 1/2 := (div_lt_iff₀ hd).2 (by linarith)
  unfold dummyParameter
  exact ⟨by linarith [div_pos hp hd],by linarith⟩

theorem dummy_strictMono (D : ℕ) : StrictMono (dummyParameter D) := by
  intro i j hij
  unfold dummyParameter
  rw [add_lt_add_iff_left]
  apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℚ) < 2*((D:ℚ)+1))).2
  exact_mod_cast (show i.val+1 < j.val+1 by omega)

theorem mem_early (n q D : ℕ) (i : Fin (n*q)) : macroParameter n q (-3/4) i.val ∈ macros n q D := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem mem_late (n q D : ℕ) (i : Fin (n*q)) : macroParameter n q (5/8) i.val ∈ macros n q D := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem mem_dummy (n q D : ℕ) (i : Fin D) : dummyParameter D i ∈ macros n q D := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem source_macros_mem {n q : ℕ} (D : ℕ) (v : Fin n) (j : Fin q) :
    macroParameter n q (-3/4) (blockIndex v j) ∈ macros n q D ∧
    macroParameter n q (5/8) (blockIndex v j) ∈ macros n q D :=
  ⟨mem_early n q D ⟨_,blockIndex_bound v j⟩,mem_late n q D ⟨_,blockIndex_bound v j⟩⟩

theorem macro_box (n q D : ℕ) (a : ℚ) (ha : a ∈ macros n q D) : |a| ≤ 3/4 := by
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      have hi := source_mesh_bounds n q (-3/4) i
      apply abs_le.mpr; constructor <;> linarith
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      have hi := source_mesh_bounds n q (5/8) i
      apply abs_le.mpr; constructor <;> linarith
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    have hi := dummy_bounds D i
    apply abs_le.mpr; constructor <;> linarith

theorem dummy_encoding (D H : ℕ) (i : Fin D) (hH : 4*(D+1) ≤ H) :
    Bounded (dummyParameter D i) H := by
  have hi : (i.val:ℤ)+1 ≤ D := by exact_mod_cast (show i.val+1 ≤ D by omega)
  have hH' : (4:ℤ)*((D:ℤ)+1) ≤ H := by exact_mod_cast hH
  have hpos : (0:ℤ) < 4*((D:ℤ)+1) := by positivity
  refine ⟨2*((i.val:ℤ)+1)-((D:ℤ)+1),4*((D:ℤ)+1),?_,?_,by omega,?_⟩
  · apply abs_le.mpr; constructor <;> omega
  · rw [abs_of_pos hpos]; exact hH'
  · unfold dummyParameter
    push_cast
    field_simp
    ring

theorem macros_encoding (n q D H : ℕ) (hs : 8*(n*q+1) ≤ H) (hd : 4*(D+1) ≤ H) :
    ∀a∈macros n q D, Bounded a H := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact (source_macro_encoding n q i.val H (by omega) hs).1
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact (source_macro_encoding n q i.val H (by omega) hs).2
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact dummy_encoding D H i hd

theorem macros_card_le (n q D : ℕ) : (macros n q D).card ≤ 2*n*q+D := by
  have h1 := Finset.card_union_le
    ((Finset.univ : Finset (Fin (n*q))).image (fun i => macroParameter n q (-3/4) i.val))
    ((Finset.univ : Finset (Fin (n*q))).image (fun i => macroParameter n q (5/8) i.val))
  have h2 := Finset.card_union_le
    (((Finset.univ : Finset (Fin (n*q))).image (fun i => macroParameter n q (-3/4) i.val)) ∪
    ((Finset.univ : Finset (Fin (n*q))).image (fun i => macroParameter n q (5/8) i.val)))
    ((Finset.univ : Finset (Fin D)).image (dummyParameter D))
  have he := Finset.card_image_le (s := (Finset.univ : Finset (Fin (n*q))))
    (f := fun i => macroParameter n q (-3/4) i.val)
  have hl := Finset.card_image_le (s := (Finset.univ : Finset (Fin (n*q))))
    (f := fun i => macroParameter n q (5/8) i.val)
  have hd := Finset.card_image_le (s := (Finset.univ : Finset (Fin D))) (f := dummyParameter D)
  simp only [Finset.card_univ,Fintype.card_fin] at he hl hd
  unfold macros
  nlinarith

/-- The globally chosen width also meets the source realization's explicit
mesh-width requirement, including the small or empty source cases. -/
theorem common_source_width (n q D W B : ℕ) :
    0 < cloneScale (macros n q D) W B ∧
    cloneScale (macros n q D) W B < 1/(8*((n*q:ℕ)+1)) := by
  have hs := common_scale_bounds (macros n q D) W B
  have ht0 := hs.2.2.2.1
  have ht := hs.2.2.2.2.1
  have he0 := macroSpacing_positive (macros n q D)
  have he1 := macroSpacing_le_one (macros n q D)
  refine ⟨ht0,?_⟩
  by_cases hn : 2 ≤ n*q
  · let i : Fin (n*q) := ⟨0,by omega⟩
    let j : Fin (n*q) := ⟨1,by omega⟩
    have hgap : macroParameter n q (-3/4) j.val-macroParameter n q (-3/4) i.val =
        1/(8*((n*q:ℕ)+1)) := by
      dsimp [i,j,macroParameter]
      ring
    have hp : 0 < macroParameter n q (-3/4) j.val-macroParameter n q (-3/4) i.val := by
      rw [hgap]; positivity
    have he := macroSpacing_le (macros n q D) _ _ (mem_early n q D i) (mem_early n q D j)
      (sub_ne_zero.mp (ne_of_gt hp))
    rw [abs_of_pos hp,hgap] at he
    have hlt : cloneScale (macros n q D) W B < macroSpacing (macros n q D) := by linarith
    exact hlt.trans_le he
  · have hn' : ((n*q:ℕ):ℚ) ≤ 1 := by exact_mod_cast (show n*q ≤ 1 by omega)
    apply (lt_div_iff₀ (by positivity : (0:ℚ) < 8*((n*q:ℕ)+1))).2
    nlinarith [mul_le_mul_of_nonneg_left hn' ht0.le]

theorem source_clone_regions {n q : ℕ} (D W B : ℕ) (hW : 2 ≤ W)
    (v : Fin n) (j : Fin q) (r : Fin W) :
    (-1 < cloneParameter (-3/4) (cloneScale (macros n q D) W B) v j r ∧
      cloneParameter (-3/4) (cloneScale (macros n q D) W B) v j r < -1/2) ∧
    (1/2 < cloneParameter (5/8) (cloneScale (macros n q D) W B) v j r ∧
      cloneParameter (5/8) (cloneScale (macros n q D) W B) v j r < 1) := by
  have hs := common_scale_bounds (macros n q D) W B
  have ht0 := hs.2.2.2.1
  have ht := hs.2.2.2.2.1
  have he1 := macroSpacing_le_one (macros n q D)
  have hleft := cloneParameter_bounds (-3/4) (cloneScale (macros n q D) W B) v j r ht0.le hW
  have hright := cloneParameter_bounds (5/8) (cloneScale (macros n q D) W B) v j r ht0.le hW
  have hml := macro_bounds (-3/4) v j
  have hmr := macro_bounds (5/8) v j
  constructor <;> constructor <;> linarith

#print axioms dummy_strictMono
#print axioms source_macros_mem
#print axioms macro_box
#print axioms dummy_encoding
#print axioms macros_encoding
#print axioms macros_card_le
#print axioms common_source_width
#print axioms source_clone_regions

end Q4.Candidate.MacroLayout

