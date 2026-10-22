import Q4.Candidate.DoubleCapGrid

/-!
Fixed-grid, common-radius batch insertion of all program copies. Every copy
uses m=M²+M+2, where M is fixed before any insertion. The larger ordered-pair
line budget is a conservative variant of candidate §6.3; no recursive shrinking
of the common radius or grid denominator is required by this construction.

Prototype cap and height margins, and a common admissible radius, remain explicit
numerical inputs. This module does not yet preserve arbitrary structural
orientation tables or prove binary bit-length bounds.
-/

namespace Q4.Candidate.UniformInsertion

open Q4.Candidate.ConvexSeparation

def gridSide (M : ℕ) : ℕ := M * M + M + 2

/-- Every insertion from a fixed master grid has a legal survivor; its width
is chosen once from a bound on the final total number of points. -/
theorem fixed_grid_extension (M : ℕ) (old : Finset Point) (hsize : old.card ≤ M)
    (hgp : GeneralPosition old) (r : Point) (eta delta : ℚ)
    (heta : 0 < eta) (hr : phi r ≤ -eta) (hd : 0 < delta)
    (hq : delta ≤ 1 / 4) (hm : delta ≤ eta / 8)
    (hheight : |r.2| + delta / 2 ≤ 2) :
    ∃ ij : Fin (gridSide M) × Fin (gridSide M),
      let p := insertionPoint r delta ij
      p ∉ old ∧ GeneralPosition (insert p old) ∧ (Vertex.program p).valid := by
  let lines := (old ×ˢ old).filter (fun ab : Point × Point => ab.1 ≠ ab.2)
  have hproper : ∀ ab ∈ lines, ab.1 ≠ ab.2 := by
    intro ab hab
    exact (Finset.mem_filter.mp hab).2
  have hlineCard : lines.card ≤ M * M := by
    have hh := Finset.card_filter_le (old ×ˢ old) (fun ab : Point × Point => ab.1 ≠ ab.2)
    simp only [Finset.card_product] at hh
    dsimp [lines]
    nlinarith
  have hbudget : lines.card * gridSide M + old.card < gridSide M * gridSide M := by
    have h1 := Nat.mul_le_mul_right (gridSide M) hlineCard
    have h2 := candidate_grid_budget (M * M) M
    dsimp [gridSide] at *
    omega
  have hstep : delta / ((gridSide M : ℚ) + 1) ≠ 0 := div_ne_zero (ne_of_gt hd) (by positivity)
  obtain ⟨ij, hp, hav⟩ := exists_grid_point_avoiding (m := gridSide M)
    (insertionOrigin r delta (gridSide M)) (delta / ((gridSide M : ℚ) + 1))
    hstep lines old hproper hbudget
  let p := insertionPoint r delta ij
  have hgen : GeneralPosition (insert p old) := by
    apply generalPosition_insert old p hgp
    intro a ha b hb hab
    exact hav (a,b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab⟩)
  have hbox := insertion_in_box r delta hd ij
  have hry : |r.2| ≤ 2 := by linarith
  have hpert := perturbation_inside r eta delta (p.1-r.1) (p.2-r.2)
    heta hr hry (le_of_lt hd) hq hm (by dsimp [p]; linarith [hbox.1])
      (by dsimp [p]; linarith [hbox.2])
  have he : perturb r (p.1-r.1) (p.2-r.2) = p := by
    apply Prod.ext <;> dsimp [perturb] <;> ring
  rw [he] at hpert
  have hyabs : |p.2| ≤ |p.2-r.2| + |r.2| := by
    simpa using abs_add_le (p.2-r.2) r.2
  have hy2 : |p.2| ≤ 2 := by dsimp [p] at *; linarith [hbox.2]
  exact ⟨ij, hp, hgen, hpert, abs_le.mp hy2⟩

def Placed (M : ℕ) (delta : ℚ) (r p : Point) : Prop :=
  ∃ ij : Fin (gridSide M) × Fin (gridSide M),
    p = insertionPoint r delta ij ∧ (Vertex.program p).valid

theorem placed_in_box (M : ℕ) (delta : ℚ) (hd : 0 < delta) (r p : Point)
    (hp : Placed M delta r p) :
    |p.1-r.1| < delta / 2 ∧ |p.2-r.2| < delta / 2 := by
  obtain ⟨ij,rfl,_⟩ := hp
  exact insertion_in_box r delta hd ij

/-- Batch existence with one fixed total-size bound, one radius, and one grid
side length. Repeated prototypes are allowed; all chosen program copies are
nevertheless distinct, distinct from the bases, and jointly in general position. -/
theorem batch_program_insertion (M : ℕ) (old : Finset Point) (rs : List Point)
    (hsize : old.card + rs.length ≤ M) (hgp : GeneralPosition old)
    (eta delta : ℚ) (heta : 0 < eta) (hd : 0 < delta)
    (hq : delta ≤ 1 / 4) (hm : delta ≤ eta / 8)
    (hproto : ∀ r ∈ rs, phi r ≤ -eta ∧ |r.2| + delta / 2 ≤ 2) :
    ∃ ps : List Point, ps.length = rs.length ∧ ps.Nodup ∧
      (∀ p ∈ ps, p ∉ old) ∧ GeneralPosition (old ∪ ps.toFinset) ∧
      List.Forall₂ (Placed M delta) rs ps := by
  induction rs generalizing old with
  | nil =>
    exact ⟨[], rfl, List.nodup_nil, by simp, by simpa using hgp, List.Forall₂.nil⟩
  | cons r rs ih =>
    have hr := hproto r (by simp)
    obtain ⟨ij, hp, hgen, hvalid⟩ := fixed_grid_extension M old (by simpa using (show old.card ≤ M by omega))
      hgp r eta delta heta hr.1 hd hq hm hr.2
    let p := insertionPoint r delta ij
    have hsize' : (insert p old).card + rs.length ≤ M := by
      rw [Finset.card_insert_of_notMem hp]
      simp only [List.length_cons] at hsize
      omega
    obtain ⟨ps, hlen, hnd, hout, hgp', hplaced⟩ := ih (insert p old) hsize' hgen
      (fun q hq => hproto q (by simp [hq]))
    have hpnot : p ∉ ps := by
      intro hh
      exact hout p hh (by simp)
    refine ⟨p :: ps, by simp [hlen], List.nodup_cons.mpr ⟨hpnot,hnd⟩, ?_, ?_, ?_⟩
    · intro q hq hqold
      rcases List.mem_cons.mp hq with rfl | hqtail
      · exact hp hqold
      · exact hout q hqtail (Finset.mem_insert_of_mem hqold)
    · simpa [List.toFinset_cons, Finset.union_insert] using hgp'
    · exact List.Forall₂.cons ⟨ij,rfl,hvalid⟩ hplaced

end Q4.Candidate.UniformInsertion

#print axioms Q4.Candidate.UniformInsertion.fixed_grid_extension
#print axioms Q4.Candidate.UniformInsertion.placed_in_box
#print axioms Q4.Candidate.UniformInsertion.batch_program_insertion
