import Q4.Candidate.CorePaletteForcing
import Q4.Candidate.ProgramIndex

/-! Reuse the complete CT cost bridge to force actual full core minimizers
from the actual catalog field, with no extra enumeration convention. -/
namespace Q4.Candidate.IndexedPaletteForcing
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.ProgramCount Q4.Candidate.CompleteDrawing
open Q4.Candidate.CompleteBackground Q4.Candidate.CorePaletteForcing

theorem fan_field_eq_catalog {O B S gaps Ssite : ℕ} (d : Recipe S)
    (ys : Fin O → ℚ) (ps : Label d gaps → Point) (site : Fin O → ProposedPalette.Site Ssite)
    (v : Inner O) :
    fanField ys (frameParameter B) (ProgramIndex.points d ps)
      (frozenFans ys (frameParameter B) (ProgramIndex.points d ps) false) v=
      ProgramField.field (B:=B) d ys ps (original (ys v.val.1)) (original (ys v.val.2)) := by
  have ht := ProgramIndex.core_unary_eq_catalog (B:=B) d ys ps site v true
  have hf := ProgramIndex.core_unary_eq_catalog (B:=B) d ys ps site v false
  change unary ys (frameParameter B) (ProgramIndex.points d ps)
    (frozenFans ys (frameParameter B) (ProgramIndex.points d ps) false) v true=_ at ht
  change unary ys (frameParameter B) (ProgramIndex.points d ps)
    (frozenFans ys (frameParameter B) (ProgramIndex.points d ps) false) v false=_ at hf
  have hh := CorePaletteForcing.unary_difference ys (frameParameter B) (ProgramIndex.points d ps)
    (frozenFans ys (frameParameter B) (ProgramIndex.points d ps) false) v
  rw [ht,hf,←Int.cast_sub,ProgramField.cost_difference] at hh
  exact_mod_cast hh.symm

/-- This is the actual complete-graph C-core minimizer conclusion. Its only
field premise is on the same actual catalog sums produced by the geometric
support and dominance theorems. -/
theorem every_minimizer_palette {O B S gaps Ssite : ℕ} (d : Recipe S)
    (ys : Fin O → ℚ) (ps : Label d gaps → Point) (site : Fin O → ProposedPalette.Site Ssite)
    (hdom : ∀v∈ProposedPalette.palette site, (O:ℝ)^2/2<
      if ProposedPalette.paletteBit site v then
        -(ProgramField.field (B:=B) d ys ps (original (ys v.val.1)) (original (ys v.val.2)):ℝ)
      else (ProgramField.field (B:=B) d ys ps (original (ys v.val.1)) (original (ys v.val.2)):ℝ))
    (κ : Inner O → Bool)
    (hmin : ∀ψ, coreValue ys (frameParameter B) (ProgramIndex.points d ps)
      (frozenFans ys (frameParameter B) (ProgramIndex.points d ps) false) κ≤
      coreValue ys (frameParameter B) (ProgramIndex.points d ps)
        (frozenFans ys (frameParameter B) (ProgramIndex.points d ps) false) ψ) :
    ∀v∈ProposedPalette.palette site, κ v=ProposedPalette.paletteBit site v := by
  apply CorePaletteForcing.every_minimizer_palette_of_square ys (frameParameter B)
    (ProgramIndex.points d ps) _ _ _ ?_ κ hmin
  intro v hv
  rw [fan_field_eq_catalog d ys ps site]
  exact hdom v hv

end Q4.Candidate.IndexedPaletteForcing
#print axioms Q4.Candidate.IndexedPaletteForcing.fan_field_eq_catalog
#print axioms Q4.Candidate.IndexedPaletteForcing.every_minimizer_palette
