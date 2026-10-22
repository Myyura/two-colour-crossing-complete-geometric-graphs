import Q4.Candidate.ActualProgramGeometry
import Q4.Candidate.ProgramExclusion
import Q4.Candidate.DummyPaletteField

/-! Actual dummy chords have no program crossing cost; their remaining
palette unary cost is a directly enumerable constant for both colors. -/
namespace Q4.Candidate.ActualDummyUnary
open Q4.Candidate.ConvexSeparation Q4.Candidate.ProgramGeometry
open Q4.Candidate.ProgramCatalog Q4.Candidate.OriginalVertexLayout

 theorem program_cost_zero (n q D W B : ℕ) (hW : 2≤W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ)
    (p : Placement (ActualRecipe.recipe A T (by omega) (sitePermutation pi)
      (geometries n q D W B hW hEven pi)) (geometries n q D W B hW hEven pi))
    (u v : Fin (O n q D W))
    (hu : n*q*W≤u.val ∧ u.val<n*q*W+D) (hv : n*q*W≤v.val ∧ v.val<n*q*W+D) (bit : Bool) :
    ProgramField.cost (B:=B) (ActualRecipe.recipe A T (by omega) (sitePermutation pi)
      (geometries n q D W B hW hEven pi)) (parameter n q D W B) p.points
      (original (parameter n q D W B u)) (original (parameter n q D W B v)) bit=0 := by
  exact ProgramExclusion.cost_zero _ _ p _ _ (parameter_abs n q D W B hW u)
    (parameter_abs n q D W B hW v) (p.original_mem u) (p.original_mem v)
    (fun j => ActualProgramGeometry.dummy_nonincident n q D W B hW hEven pi j u v hu hv) bit

/-- This is the combined palette-plus-program unary used by the actual core
extension. It holds for each genuine dummy chord, not merely in aggregate. -/
theorem unary_constant (n q D W B : ℕ) (hW : 2≤W) (hEven : Even B) (hS : 0<n*q)
    (pi : Equiv.Perm (Fin n)) (A T : ℤ)
    (p : Placement (ActualRecipe.recipe A T (by omega) (sitePermutation pi)
      (geometries n q D W B hW hEven pi)) (geometries n q D W B hW hEven pi))
    (u v : Fin (O n q D W)) (huv : u<v)
    (hu : n*q*W≤u.val) (hv : v.val<n*q*W+D) (bit : Bool) :
    ActualRecipe.unary A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) p u v bit=
    ActualRecipe.unary A T (by omega) (sitePermutation pi) (geometries n q D W B hW hEven pi) p u v false := by
  have hlt : u.val<v.val := huv
  have hu' : n*q*W≤u.val ∧ u.val<n*q*W+D := ⟨hu,by omega⟩
  have hv' : n*q*W≤v.val ∧ v.val<n*q*W+D := ⟨by omega,hv⟩
  unfold ActualRecipe.unary
  rw [show (geometries n q D W B hW hEven pi).ys=parameter n q D W B from rfl]
  rw [program_cost_zero n q D W B hW hEven pi A T p u v hu' hv' bit,
    program_cost_zero n q D W B hW hEven pi A T p u v hu' hv' false]
  exact congrArg (fun z : ℤ => z+0) (DummyPaletteField.indexed_dummy_cost_constant (n*q) W D hS
    (by omega) (sitePermutation pi) _ (parameter_strictMono n q D W B hW) u v huv hu hv bit)

end Q4.Candidate.ActualDummyUnary
#print axioms Q4.Candidate.ActualDummyUnary.program_cost_zero
#print axioms Q4.Candidate.ActualDummyUnary.unary_constant
