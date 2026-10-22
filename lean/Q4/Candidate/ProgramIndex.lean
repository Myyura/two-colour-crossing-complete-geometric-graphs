import Q4.Candidate.ActualRecipe
import Q4.Candidate.CoreValueBridge

/-! Reindex every actual program copy as a Fin P vertex and identify its
canonical response and complete-core unary with the catalog objective. -/
namespace Q4.Candidate.ProgramIndex
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.ProgramCount Q4.Candidate.ProgramCatalog
open Q4.Candidate.CompleteDrawing Q4.Candidate.CompleteClassEnergy
open Q4.Candidate.CompleteBackground Q4.Candidate.CoreValueBridge
attribute [local instance] Classical.propDecidable
open scoped BigOperators

noncomputable def points {S gaps : ℕ} (d : Recipe S) (ps : Label d gaps → Point) :
    Fin (Fintype.card (Label d gaps)) → Point := fun k => ps ((Fintype.equivFin _).symm k)

theorem frozen_eq_response {O B P : ℕ} (ys : Fin O → ℚ) (rs : Fin P → Point)
    (i : Fin B) (k : Fin P) :
    frozenFans ys (frameParameter B) rs false (i,k)=RankResponse.response ys (rs k) i := by
  unfold frozenFans CompleteProbeFreezing.frozenColor
  simp only [Bool.false_eq_true,ite_false,T,CompleteFanFields.full_field_eq_pointField]
  rfl

theorem core_cross {O B P : ℕ} (ys : Fin O → ℚ) (rs : Fin P → Point)
    (e : Inner O) (i : Fin B) (k : Fin P) :
    Cross ys (frameParameter B) rs (C e) (T (i,k)) ↔
      ProperCross (rs k) (frame (frameParameter B i)) (original (ys e.val.1)) (original (ys e.val.2)) := by
  change ProperCross (original (ys e.val.1)) (original (ys e.val.2))
    (frame (frameParameter B i)) (rs k) ↔ _
  exact (properCross_swap_edges _ _ _ _).trans (properCross_reverse_first _ _ _ _).symm

theorem core_unary_sum {O B P S : ℕ} (ys : Fin O → ℚ) (rs : Fin P → Point)
    (site : Fin O → ProposedPalette.Site S) (e : Inner O) (bit : Bool) :
    coreUnary ys (frameParameter B) rs
      (CoreValueBridge.reference site (frozenFans ys (frameParameter B) rs false)) e bit=
      (∑k : Fin P, RankResponse.coreCost (B:=B) ys (rs k)
        (original (ys e.val.1)) (original (ys e.val.2)) bit : ℤ) := by
  unfold coreUnary
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  unfold RankResponse.coreCost
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  change (if Cross ys (frameParameter B) rs (C e) (T (i,k)) ∧
    bit=frozenFans ys (frameParameter B) rs false (i,k) then (1:ℝ) else 0)=_
  simp only [core_cross,frozen_eq_response]
  split_ifs <;> simp_all

theorem core_unary_eq_catalog {O B S gaps Ssite : ℕ} (d : Recipe S)
    (ys : Fin O → ℚ) (ps : Label d gaps → Point)
    (site : Fin O → ProposedPalette.Site Ssite) (e : Inner O) (bit : Bool) :
    coreUnary ys (frameParameter B) (points d ps)
      (CoreValueBridge.reference site (frozenFans ys (frameParameter B) (points d ps) false)) e bit=
      (ProgramField.cost (B:=B) d ys ps (original (ys e.val.1)) (original (ys e.val.2)) bit : ℝ) := by
  rw [core_unary_sum]
  congr 1
  unfold ProgramField.cost points
  exact Equiv.sum_comp (Fintype.equivFin (Label d gaps)).symm
    (fun l => RankResponse.coreCost (B:=B) ys (ps l)
      (original (ys e.val.1)) (original (ys e.val.2)) bit)

theorem actual_unary_eq {S W D B : ℕ} (A T : ℤ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (g : Geometries S (W-1) B (S*W+D+S*W)) (p : Placement (ActualRecipe.recipe A T hW pi g) g)
    (e : Inner (S*W+D+S*W)) (bit : Bool) :
    CoreValueBridge.unary g.ys (frameParameter B) (points (ActualRecipe.recipe A T hW pi g) p.points)
      (ProposedPalette.indexedSite S W D hW pi)
      (frozenFans g.ys (frameParameter B) (points (ActualRecipe.recipe A T hW pi g) p.points) false) e bit=
      (ActualRecipe.unary A T hW pi g p e.val.1 e.val.2 bit : ℝ) := by
  unfold CoreValueBridge.unary CoreFixedPalette.freeUnary ActualRecipe.unary
  rw [core_unary_eq_catalog]
  push_cast
  rfl

end Q4.Candidate.ProgramIndex
#print axioms Q4.Candidate.ProgramIndex.frozen_eq_response
#print axioms Q4.Candidate.ProgramIndex.core_unary_eq_catalog
#print axioms Q4.Candidate.ProgramIndex.actual_unary_eq
