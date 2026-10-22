import Q4.Candidate.ConvexSeparation
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Finite rational grid insertion, corresponding to §6.3 of the candidate.
Every excluded affine line is specified by two distinct actual rational points.
The theorem bounds their grid incidences and separately counts old points.
It does not establish that all earlier structural margins have been computed,
nor does it prove a coordinate bit-complexity or whole reduction theorem.
-/

namespace Q4.Candidate.ConvexSeparation

def gridPoint {m : ℕ} (origin : Point) (step : ℚ) (ij : Fin m × Fin m) : Point :=
  (origin.1 + step * (ij.1.val : ℚ), origin.2 + step * (ij.2.val : ℚ))

theorem gridPoint_injective {m : ℕ} (origin : Point) (step : ℚ) (hs : step ≠ 0) :
    Function.Injective (gridPoint (m := m) origin step) := by
  intro ij kl he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [gridPoint] at hx hy
  have hx' : (ij.1.val : ℚ) = (kl.1.val : ℚ) := mul_left_cancel₀ hs (by linarith)
  have hy' : (ij.2.val : ℚ) = (kl.2.val : ℚ) := mul_left_cancel₀ hs (by linarith)
  apply Prod.ext
  · apply Fin.ext
    exact_mod_cast hx'
  · apply Fin.ext
    exact_mod_cast hy'

def lineIndices {m : ℕ} (origin : Point) (step : ℚ) (a b : Point) :
    Finset (Fin m × Fin m) := Finset.univ.filter (fun ij => orient a b (gridPoint origin step ij) = 0)

/-- Every nondegenerate straight line hits at most m points of an actual
affine m×m grid; vertical lines are covered separately rather than assumed away. -/
theorem lineIndices_card {m : ℕ} (origin : Point) (step : ℚ) (hs : step ≠ 0)
    (a b : Point) (hab : a ≠ b) : (lineIndices (m := m) origin step a b).card ≤ m := by
  by_cases hdy : b.2 - a.2 = 0
  · have hdx : b.1 - a.1 ≠ 0 := by
      intro hx
      apply hab
      apply Prod.ext <;> linarith
    have hcount := Finset.card_le_card_of_injOn (s := lineIndices (m := m) origin step a b)
      (t := Finset.univ) Prod.fst (by intro ij _; simp) (by
        intro ij hij kl hkl he
        have hi := (Finset.mem_filter.mp hij).2
        have hk := (Finset.mem_filter.mp hkl).2
        dsimp [orient, gridPoint] at hi hk
        rw [hdy] at hi hk
        have hy : (ij.2.val : ℚ) = (kl.2.val : ℚ) := by
          have hmul : (b.1 - a.1) * step *
              ((ij.2.val : ℚ) - (kl.2.val : ℚ)) = 0 := by nlinarith
          have hnonzero := mul_ne_zero hdx hs
          exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hnonzero)
        apply Prod.ext he
        apply Fin.ext
        exact_mod_cast hy)
    simpa using hcount
  · have hcount := Finset.card_le_card_of_injOn (s := lineIndices (m := m) origin step a b)
      (t := Finset.univ) Prod.snd (by intro ij _; simp) (by
        intro ij hij kl hkl he
        have hi := (Finset.mem_filter.mp hij).2
        have hk := (Finset.mem_filter.mp hkl).2
        have hey := congrArg (fun k : Fin m => (k.val : ℚ)) he
        dsimp [orient, gridPoint] at hi hk
        rw [hey] at hi
        have hx : (ij.1.val : ℚ) = (kl.1.val : ℚ) := by
          have hmul : (b.2 - a.2) * step *
              ((ij.1.val : ℚ) - (kl.1.val : ℚ)) = 0 := by nlinarith
          have hnonzero := mul_ne_zero hdy hs
          exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hnonzero)
        apply Prod.ext _ he
        apply Fin.ext
        exact_mod_cast hx)
    simpa using hcount

def oldPointIndices {m : ℕ} (origin : Point) (step : ℚ) (old : Finset Point) :
    Finset (Fin m × Fin m) := Finset.univ.filter (fun ij => gridPoint origin step ij ∈ old)

theorem oldPointIndices_card {m : ℕ} (origin : Point) (step : ℚ) (hs : step ≠ 0)
    (old : Finset Point) : (oldPointIndices (m := m) origin step old).card ≤ old.card := by
  apply Finset.card_le_card_of_injOn (gridPoint origin step)
  · intro ij hij
    exact (Finset.mem_filter.mp hij).2
  · intro ij _ kl _ he
    exact gridPoint_injective origin step hs he

/-- A concrete finite rational search always has a survivor once the displayed
incidence budget is below m². Lines and isolated forbidden points are both kept. -/
theorem exists_grid_point_avoiding {m : ℕ} (origin : Point) (step : ℚ) (hs : step ≠ 0)
    (lines : Finset (Point × Point)) (old : Finset Point)
    (hproper : ∀ ab ∈ lines, ab.1 ≠ ab.2)
    (hbudget : lines.card * m + old.card < m * m) :
    ∃ ij : Fin m × Fin m, gridPoint origin step ij ∉ old ∧
      ∀ ab ∈ lines, orient ab.1 ab.2 (gridPoint origin step ij) ≠ 0 := by
  let badLines := lines.biUnion (fun ab => lineIndices (m := m) origin step ab.1 ab.2)
  let badPoints := oldPointIndices (m := m) origin step old
  have hlines : badLines.card ≤ lines.card * m := by
    calc
      badLines.card ≤ ∑ ab ∈ lines, (lineIndices (m := m) origin step ab.1 ab.2).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _ab ∈ lines, m := Finset.sum_le_sum (fun ab hab =>
        lineIndices_card origin step hs ab.1 ab.2 (hproper ab hab))
      _ = lines.card * m := by simp
  have hpoints : badPoints.card ≤ old.card := oldPointIndices_card origin step hs old
  have hsmall : (badLines ∪ badPoints).card < (Finset.univ : Finset (Fin m × Fin m)).card := by
    have hc := Finset.card_union_le badLines badPoints
    simpa using (show (badLines ∪ badPoints).card < m * m by omega)
  obtain ⟨ij, _, hij⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  refine ⟨ij, ?_, ?_⟩
  · intro he
    apply hij
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  · intro ab hab he
    apply hij
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨ab, hab, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩)

/-- The candidate's m = number-of-lines-bound + number-of-old-points-bound + 2
is more than sufficient; no asymptotic or real-area argument is used. -/
theorem candidate_grid_budget (L M : ℕ) :
    L * (L + M + 2) + M < (L + M + 2) * (L + M + 2) := by
  nlinarith

def insertionOrigin (r : Point) (delta : ℚ) (m : ℕ) : Point :=
  (r.1 + delta * (1 / ((m : ℚ) + 1) - 1 / 2),
   r.2 + delta * (1 / ((m : ℚ) + 1) - 1 / 2))

def insertionPoint {m : ℕ} (r : Point) (delta : ℚ) (ij : Fin m × Fin m) : Point :=
  gridPoint (insertionOrigin r delta m) (delta / ((m : ℚ) + 1)) ij

theorem insertion_coordinate (r : Point) (delta : ℚ) {m : ℕ} (ij : Fin m × Fin m) :
    insertionPoint r delta ij =
      (r.1 + delta * (((ij.1.val : ℚ) + 1) / ((m : ℚ) + 1) - 1 / 2),
       r.2 + delta * (((ij.2.val : ℚ) + 1) / ((m : ℚ) + 1) - 1 / 2)) := by
  apply Prod.ext <;> dsimp [insertionPoint, gridPoint, insertionOrigin] <;> ring

theorem insertion_coordinate_bound (delta : ℚ) (hd : 0 < delta) {m : ℕ} (i : Fin m) :
    |delta * (((i.val : ℚ) + 1) / ((m : ℚ) + 1) - 1 / 2)| < delta / 2 := by
  have hm : 0 < (m : ℚ) + 1 := by positivity
  have hi0 : 0 ≤ (i.val : ℚ) := by positivity
  have him : (i.val : ℚ) < (m : ℚ) := by exact_mod_cast i.isLt
  have hratio0 : 0 < ((i.val : ℚ) + 1) / ((m : ℚ) + 1) := div_pos (by linarith) hm
  have hratio1 : ((i.val : ℚ) + 1) / ((m : ℚ) + 1) < 1 :=
    (div_lt_one hm).2 (by linarith)
  rw [abs_lt]
  constructor <;> nlinarith [mul_pos hd hratio0, mul_pos hd (sub_pos.mpr hratio1)]

/-- The explicit candidate grid is strictly inside the prescribed L∞ box. -/
theorem insertion_in_box (r : Point) (delta : ℚ) (hd : 0 < delta)
    {m : ℕ} (ij : Fin m × Fin m) :
    |(insertionPoint r delta ij).1 - r.1| < delta / 2 ∧
      |(insertionPoint r delta ij).2 - r.2| < delta / 2 := by
  rw [insertion_coordinate]
  simpa using And.intro (insertion_coordinate_bound delta hd ij.1)
    (insertion_coordinate_bound delta hd ij.2)

/-- Exact same-denominator rational grid, nonzero displacement, and a point
simultaneously avoiding every specified old point and every specified old line. -/
theorem exists_insertion_point (r : Point) (delta : ℚ) (hd : 0 < delta)
    (lines : Finset (Point × Point)) (old : Finset Point)
    (hproper : ∀ ab ∈ lines, ab.1 ≠ ab.2) :
    ∃ p : Point, |p.1 - r.1| < delta / 2 ∧ |p.2 - r.2| < delta / 2 ∧
      p ∉ old ∧ ∀ ab ∈ lines, orient ab.1 ab.2 p ≠ 0 := by
  let m := lines.card + old.card + 2
  have hstep : delta / ((m : ℚ) + 1) ≠ 0 :=
    div_ne_zero (ne_of_gt hd) (by positivity)
  obtain ⟨ij, hpoint, hlines⟩ := exists_grid_point_avoiding (m := m)
    (insertionOrigin r delta m) (delta / ((m : ℚ) + 1)) hstep lines old hproper
    (candidate_grid_budget lines.card old.card)
  have hbox := insertion_in_box r delta hd ij
  exact ⟨insertionPoint r delta ij, hbox.1, hbox.2, hpoint, hlines⟩

def GeneralPosition (points : Finset Point) : Prop :=
  ∀ a ∈ points, ∀ b ∈ points, ∀ c ∈ points,
    a ≠ b → a ≠ c → b ≠ c → orient a b c ≠ 0

theorem orient_cycle (a b c : Point) : orient a b c = orient b c a := by
  unfold orient
  ring

theorem orient_reverse_last (a b c : Point) : orient a b c = -orient a c b := by
  unfold orient
  ring

theorem generalPosition_insert (old : Finset Point) (p : Point)
    (hgp : GeneralPosition old)
    (havoid : ∀ a ∈ old, ∀ b ∈ old, a ≠ b → orient a b p ≠ 0) :
    GeneralPosition (insert p old) := by
  intro a ha b hb c hc hab hac hbc
  rcases Finset.mem_insert.mp ha with rfl | haOld
  · rcases Finset.mem_insert.mp hb with rfl | hbOld
    · exact (hab rfl).elim
    · rcases Finset.mem_insert.mp hc with rfl | hcOld
      · exact (hac rfl).elim
      · rw [orient_cycle]
        exact havoid b hbOld c hcOld hbc
  · rcases Finset.mem_insert.mp hb with rfl | hbOld
    · rcases Finset.mem_insert.mp hc with rfl | hcOld
      · exact (hbc rfl).elim
      · rw [orient_reverse_last]
        exact neg_ne_zero.mpr (havoid a haOld c hcOld hac)
    · rcases Finset.mem_insert.mp hc with rfl | hcOld
      · exact havoid a haOld b hbOld hab
      · exact hgp a haOld b hbOld c hcOld hab hac hbc

/-- A completely specified finite forbidden family gives a new rational point
inside any positive box while preserving general position. Using both ordered
versions of each old pair is harmless and needs at most |old|² forbidden lines;
the sharper unordered-pair count of the paper is not needed for this theorem. -/
theorem exists_general_position_extension (old : Finset Point) (hgp : GeneralPosition old)
    (r : Point) (delta : ℚ) (hd : 0 < delta) :
    ∃ p : Point, |p.1 - r.1| < delta / 2 ∧ |p.2 - r.2| < delta / 2 ∧
      p ∉ old ∧ GeneralPosition (insert p old) := by
  let lines := (old ×ˢ old).filter (fun ab : Point × Point => ab.1 ≠ ab.2)
  have hproper : ∀ ab ∈ lines, ab.1 ≠ ab.2 := by
    intro ab hab
    exact (Finset.mem_filter.mp hab).2
  obtain ⟨p, hx, hy, hp, hav⟩ := exists_insertion_point r delta hd lines old hproper
  refine ⟨p, hx, hy, hp, generalPosition_insert old p hgp ?_⟩
  intro a ha b hb hab
  exact hav (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩)

/-- The same finite insertion can preserve the original cap region as well as
general position. All geometric hypotheses here are numerical prototype/radius
conditions; no zero-crossing or constructed-point existence is assumed. -/
theorem exists_inward_general_position_extension (old : Finset Point)
    (hgp : GeneralPosition old) (r : Point) (eta delta : ℚ)
    (heta : 0 < eta) (hr : phi r ≤ -eta) (hry : |r.2| ≤ 2)
    (hd : 0 < delta) (hq : delta ≤ 1 / 4) (hm : delta ≤ eta / 8) :
    ∃ p : Point, |p.1 - r.1| < delta / 2 ∧ |p.2 - r.2| < delta / 2 ∧
      p ∉ old ∧ GeneralPosition (insert p old) ∧ phi p < 0 := by
  obtain ⟨p, hx, hy, hp, hgen⟩ := exists_general_position_extension old hgp r delta hd
  refine ⟨p, hx, hy, hp, hgen, ?_⟩
  have hpert := perturbation_inside r eta delta (p.1 - r.1) (p.2 - r.2)
    heta hr hry (le_of_lt hd) hq hm (by linarith) (by linarith)
  have he : perturb r (p.1 - r.1) (p.2 - r.2) = p := by
    apply Prod.ext <;> dsimp [perturb] <;> ring
  rwa [he] at hpert

/-- Adding the explicit height margin closes the interface to `Vertex.valid`
and hence to frame isolation. A prototype merely satisfying |ry|≤2 would not
suffice after perturbation; the margin below is therefore kept in the statement. -/
theorem exists_valid_program_extension (old : Finset Point)
    (hgp : GeneralPosition old) (r : Point) (eta delta : ℚ)
    (heta : 0 < eta) (hr : phi r ≤ -eta)
    (hd : 0 < delta) (hq : delta ≤ 1 / 4) (hm : delta ≤ eta / 8)
    (hheight : |r.2| + delta / 2 ≤ 2) :
    ∃ p : Point, |p.1 - r.1| < delta / 2 ∧ |p.2 - r.2| < delta / 2 ∧
      p ∉ old ∧ GeneralPosition (insert p old) ∧ (Vertex.program p).valid := by
  have hry : |r.2| ≤ 2 := by linarith
  obtain ⟨p, hx, hy, hp, hgen, hphi⟩ :=
    exists_inward_general_position_extension old hgp r eta delta heta hr hry hd hq hm
  have hyabs : |p.2| ≤ |p.2 - r.2| + |r.2| := by
    simpa using abs_add_le (p.2 - r.2) r.2
  have hy2 : |p.2| ≤ 2 := by linarith
  exact ⟨p, hx, hy, hp, hgen, hphi, abs_le.mp hy2⟩

end Q4.Candidate.ConvexSeparation

#print axioms Q4.Candidate.ConvexSeparation.gridPoint_injective
#print axioms Q4.Candidate.ConvexSeparation.lineIndices_card
#print axioms Q4.Candidate.ConvexSeparation.oldPointIndices_card
#print axioms Q4.Candidate.ConvexSeparation.exists_grid_point_avoiding
#print axioms Q4.Candidate.ConvexSeparation.candidate_grid_budget
#print axioms Q4.Candidate.ConvexSeparation.insertion_in_box
#print axioms Q4.Candidate.ConvexSeparation.exists_insertion_point
#print axioms Q4.Candidate.ConvexSeparation.generalPosition_insert
#print axioms Q4.Candidate.ConvexSeparation.exists_general_position_extension
#print axioms Q4.Candidate.ConvexSeparation.exists_inward_general_position_extension
#print axioms Q4.Candidate.ConvexSeparation.exists_valid_program_extension
