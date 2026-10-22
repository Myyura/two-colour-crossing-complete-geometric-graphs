import Q4.Candidate.ActualProgramGeometry
import Q4.Candidate.SideCatalog

/-! Actual same-side and side-dummy geometry for all remaining palette
families. The parent sets and every curvature inequality are constructed. -/
namespace Q4.Candidate.ActualSideGeometry
open Q4.Candidate.ConvexSeparation Q4.Candidate.OriginalVertexLayout
open Q4.Candidate.ProgramGeometry Q4.Candidate.ActualProgramGeometry
open Q4.Candidate.ProgramCatalog Q4.Candidate.GlobalGeometryScales
open Q4.Candidate.MacroLayout Q4.Candidate.SideCatalog
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 600000

noncomputable def sideBlock (n q D W B : ℕ) (hW : 2 ≤ W) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) : Block n q D W B :=
  if late then lateBlock n q D W B hW (latePhysical pi j) else earlyBlock n q D W B hW j

noncomputable def sideIndex (n q D W : ℕ) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) (s : Fin W) : Fin (O n q D W) :=
  if late then lateIndex n q D W (latePhysical pi j) s else earlyIndex n q D W j s

theorem side_mem (n q D W B : ℕ) (hW : 2 ≤ W) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) (s : Fin W) :
    sideIndex n q D W pi late j s∈(sideBlock n q D W B hW pi late j).parent := by
  cases late
  · exact early_mem n q D W B hW j s
  · exact late_mem n q D W B hW _ s

theorem side_other (n q D W B : ℕ) (hW : 2 ≤ W) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j k : Fin (n*q)) (s : Fin W) (hne : j≠k) :
    sideIndex n q D W pi late j s∉(sideBlock n q D W B hW pi late k).parent := by
  cases late
  · exact early_other n q D W B hW j k s hne
  · exact late_other n q D W B hW _ _ s (by intro h; exact hne ((latePhysical pi).injective h))

theorem side_opposite (n q D W B : ℕ) (hW : 2 ≤ W) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j k : Fin (n*q)) (s : Fin W) :
    sideIndex n q D W pi late j s∉(sideBlock n q D W B hW pi (!late) k).parent := by
  cases late
  · exact early_outside_late n q D W B hW j _ s
  · exact late_outside_early n q D W B hW _ k s

theorem middle_outside_side (n q D W B : ℕ) (hW : 2 ≤ W) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) (i : Fin (O n q D W))
    (hi : n*q*W ≤ i.val ∧ i.val < n*q*W+D) :
    i∉(sideBlock n q D W B hW pi late j).parent := by
  cases late
  · exact (middle_outside n q D W B hW j i hi).1
  · exact (middle_outside n q D W B hW _ i hi).2

theorem side_clone (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) (i : Fin (O n q D W))
    (hi : i∈(sideBlock n q D W B hW pi late j).parent) :
    3*((B:ℚ)+1)*|parameter n q D W B i-(ordinaryGeo (geometries n q D W B hW hEven pi) late j).2.a| ≤
      (ordinaryGeo (geometries n q D W B hW hEven pi) late j).2.mu := by
  cases late
  · exact ((geometries n q D W B hW hEven pi).ordinaryLeft j).2.clone i hi
  · exact ((geometries n q D W B hW hEven pi).ordinaryRight j).2.clone i hi

theorem side_sep (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) (i : Fin (O n q D W))
    (hi : i∉(sideBlock n q D W B hW pi late j).parent) :
    5*(ordinaryGeo (geometries n q D W B hW hEven pi) late j).2.mu ≤
      |parameter n q D W B i-(ordinaryGeo (geometries n q D W B hW hEven pi) late j).2.a| := by
  cases late
  · exact ((geometries n q D W B hW hEven pi).ordinaryLeft j).2.sep i hi
  · exact ((geometries n q D W B hW hEven pi).ordinaryRight j).2.sep i hi

theorem side_margins (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) (i k : Fin (O n q D W))
    (hi : i∉(sideBlock n q D W B hW pi late j).parent)
    (hk : k∉(sideBlock n q D W B hW pi late j).parent) :
    ordinaryMargin (geometries n q D W B hW hEven pi) late j
      (parameter n q D W B i) (parameter n q D W B k) ∧
    rankMargin (geometries n q D W B hW hEven pi) late j
      (parameter n q D W B i) (parameter n q D W B k) := by
  have hs : (lateBlock n q D W B hW (latePhysical pi j)).a-(earlyBlock n q D W B hW j).a ≤ 2 := by
    linarith [(abs_le.mp (lateBlock n q D W B hW (latePhysical pi j)).unit_a).2,
      (abs_le.mp (earlyBlock n q D W B hW j).unit_a).1]
  have hh := block_nonincident (sideBlock n q D W B hW pi late j) hW i k hi hk _ hs
  cases late
  · exact ⟨hh.1,fun _ => hh.2⟩
  · exact ⟨hh.1,fun _ => hh.2⟩

/-- Two distinct actual macro parents on either side. Both endpoint orders
are handled: the second parent's clone is the second endpoint. -/
theorem side_pair_support (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (late : Bool) (j k : Fin (n*q)) (s t : Fin W) (hne : j≠k) :
    Support (geometries n q D W B hW hEven pi) late {j,k}
      (parameter n q D W B (sideIndex n q D W pi late j s))
      (parameter n q D W B (sideIndex n q D W pi late k t)) := by
  have hOut (l : Fin (n*q)) (hl : l∉({j,k} : Finset (Fin (n*q)))) :=
    side_margins n q D W B hW hEven pi late l _ _
      (side_other n q D W B hW pi late j l s (by intro h; subst l; simp at hl))
      (side_other n q D W B hW pi late k l t (by intro h; subst l; simp at hl))
  have hOpp (l : Fin (n*q)) := side_margins n q D W B hW hEven pi (!late) l _ _
    (side_opposite n q D W B hW pi late j l s) (side_opposite n q D W B hW pi late k l t)
  refine {
    unit_c := parameter_abs n q D W B hW _
    unit_b := parameter_abs n q D W B hW _
    incident := ?_
    ordinary_outside := fun l hl => (hOut l hl).1
    rank_outside := fun l hl => (hOut l hl).2
    opposite_ordinary := fun l => (hOpp l).1
    opposite_rank := fun l => (hOpp l).2 }
  intro l hl
  rcases Finset.mem_insert.mp hl with he|hl
  · subst l
    exact Or.inl ⟨side_clone n q D W B hW hEven pi late j _ (side_mem n q D W B hW pi late j s),
      side_sep n q D W B hW hEven pi late j _ (side_other n q D W B hW pi late k j t hne.symm)⟩
  · have he := Finset.mem_singleton.mp hl
    subst l
    exact Or.inr ⟨side_clone n q D W B hW hEven pi late k _ (side_mem n q D W B hW pi late k t),
      side_sep n q D W B hW hEven pi late k _ (side_other n q D W B hW pi late j k s hne)⟩

/-- One actual side parent and one actual middle dummy endpoint. -/
theorem side_dummy_support (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (late : Bool) (j : Fin (n*q)) (s : Fin W)
    (i : Fin (O n q D W)) (hi : n*q*W ≤ i.val ∧ i.val < n*q*W+D) :
    Support (geometries n q D W B hW hEven pi) late {j}
      (parameter n q D W B (sideIndex n q D W pi late j s)) (parameter n q D W B i) := by
  have hOut (l : Fin (n*q)) (hl : l∉({j} : Finset (Fin (n*q)))) :=
    side_margins n q D W B hW hEven pi late l _ i
      (side_other n q D W B hW pi late j l s (by intro h; subst l; simp at hl))
      (middle_outside_side n q D W B hW pi late l i hi)
  have hOpp (l : Fin (n*q)) := side_margins n q D W B hW hEven pi (!late) l _ i
    (side_opposite n q D W B hW pi late j l s)
    (middle_outside_side n q D W B hW pi (!late) l i hi)
  refine {
    unit_c := parameter_abs n q D W B hW _
    unit_b := parameter_abs n q D W B hW i
    incident := ?_
    ordinary_outside := fun l hl => (hOut l hl).1
    rank_outside := fun l hl => (hOut l hl).2
    opposite_ordinary := fun l => (hOpp l).1
    opposite_rank := fun l => (hOpp l).2 }
  intro l hl
  have he := Finset.mem_singleton.mp hl
  subst l
  exact Or.inl ⟨side_clone n q D W B hW hEven pi late j _ (side_mem n q D W B hW pi late j s),
    side_sep n q D W B hW hEven pi late j i (middle_outside_side n q D W B hW pi late j i hi)⟩

theorem support_reverse {S gaps B N : ℕ} (g : Geometries S gaps B N) (late : Bool)
    (J : Finset (Fin S)) (c b : ℚ) (h : Support g late J c b) : Support g late J b c := by
  have ordinary_reverse (side : Bool) (j : Fin S) (hh : ordinaryMargin g side j c b) :
      ordinaryMargin g side j b c := by
    unfold ordinaryMargin at hh ⊢
    simpa only [mul_comm] using hh
  have rank_reverse (side : Bool) (j : Fin S) (hh : rankMargin g side j c b) :
      rankMargin g side j b c := by
    cases side <;> simpa only [rankMargin,Bool.false_eq_true,ite_false,ite_true,mul_comm] using hh
  refine ⟨h.unit_b,h.unit_c,?_,fun j hj => ordinary_reverse _ _ (h.ordinary_outside j hj),
    fun j hj => rank_reverse _ _ (h.rank_outside j hj),
    fun j => ordinary_reverse _ _ (h.opposite_ordinary j),fun j => rank_reverse _ _ (h.opposite_rank j)⟩
  intro j hj
  rcases h.incident j hj with hh|hh
  · exact Or.inr hh
  · exact Or.inl hh

theorem dummy_side_support (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (late : Bool) (j : Fin (n*q)) (s : Fin W)
    (i : Fin (O n q D W)) (hi : n*q*W ≤ i.val ∧ i.val < n*q*W+D) :
    Support (geometries n q D W B hW hEven pi) late {j}
      (parameter n q D W B i) (parameter n q D W B (sideIndex n q D W pi late j s)) :=
  support_reverse _ _ _ _ _ (side_dummy_support n q D W B hW hEven pi late j s i hi)

theorem sideIndex_eq_palette (n q D W : ℕ) (pi : Equiv.Perm (Fin n))
    (late : Bool) (j : Fin (n*q)) (s : Fin W) :
    sideIndex n q D W pi late j s =
      if late then ProposedPalette.lateEndpoint (n*q) W D (sitePermutation pi) j s
      else ProposedPalette.earlyEndpoint (n*q) W D (sitePermutation pi) j s := by
  cases late
  · rfl
  · exact (palette_late_index n q D W pi j s).symm

end Q4.Candidate.ActualSideGeometry

#print axioms Q4.Candidate.ActualSideGeometry.side_margins
#print axioms Q4.Candidate.ActualSideGeometry.side_pair_support
#print axioms Q4.Candidate.ActualSideGeometry.side_dummy_support
#print axioms Q4.Candidate.ActualSideGeometry.support_reverse
#print axioms Q4.Candidate.ActualSideGeometry.dummy_side_support
