import Q4.Candidate.ProgramGeometry
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup

/-! One finite batch supplies genuinely distinct rational copies of the
computed program catalog, jointly in general position with the actual bases. -/
namespace Q4.Candidate.ProgramPlacement
open Q4.Candidate.ConvexSeparation Q4.Candidate.UniformInsertion
open Q4.Candidate.OrientationPreservation
open Q4.Candidate.ProgramGeometry Q4.Candidate.OriginalVertexLayout
open Q4.Candidate.ProgramCatalog Q4.Candidate.ProgramCount Q4.Candidate.ProgramField
open Q4.Candidate.DoubleCapGrid
attribute [local instance] Classical.propDecidable

/-- Reindex the actual list construction by arbitrary finite copy labels.
Even repeated prototypes obtain different final points. -/
theorem finite_batch {α : Type*} [Fintype α] (base : Finset Point) (f : α → Point)
    (hgp : GeneralPosition base) (hf : ∀a, phi (f a) < 0 ∧ |(f a).2| < 2) :
    let R := Finset.univ.image f
    let M := base.card+Fintype.card α
    ∃points : α → Point, Function.Injective points ∧ (∀a, points a ∉ base) ∧
      GeneralPosition (base ∪ Finset.univ.image points) ∧
      (∀a, Placed M (constructionRadius base R) (f a) (points a)) := by
  classical
  dsimp only
  let e := Fintype.equivFin α
  let rs := List.ofFn (fun i => f (e.symm i))
  have hlen : rs.length=Fintype.card α := List.length_ofFn
  have hmem (r : Point) : r∈rs ↔ ∃a, f a=r := by
    simp only [rs,List.mem_ofFn]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨a,rfl⟩; exact ⟨e a,by simp⟩
  have hR : rs.toFinset=Finset.univ.image f := by
    ext r
    simp only [List.mem_toFinset,hmem,Finset.mem_image,Finset.mem_univ,true_and]
  obtain ⟨_,ps,hpslen,hnd,hout,hgp',hplaced,_⟩ :=
    batch_insertion_preserving_tables (base.card+Fintype.card α) base rs
      (by rw [hlen]) hgp (by intro r hr; obtain ⟨a,rfl⟩ := (hmem r).mp hr; exact hf a)
  have hps : ps.length=Fintype.card α := hpslen.trans hlen
  let points (a : α) : Point := ps.get ⟨(e a).val,by rw [hps]; exact (e a).isLt⟩
  have hinj : Function.Injective points := by
    intro a b hab
    have hh := List.nodup_iff_injective_get.mp hnd hab
    apply e.injective
    have hv : (e a).val=(e b).val := congrArg (fun i : Fin ps.length => i.val) hh
    exact Fin.ext hv
  have hpoints : Finset.univ.image points=ps.toFinset := by
    ext r
    constructor
    · intro hr
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hr
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · intro hr
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hr)
      refine Finset.mem_image.mpr ⟨e.symm ⟨i.val,by rw [←hps]; exact i.isLt⟩,Finset.mem_univ _,?_⟩
      dsimp only [points]
      rw [Equiv.apply_symm_apply]
      exact hi
  refine ⟨points,hinj,?_,?_,?_⟩
  · intro a
    exact hout _ (List.get_mem _ _)
  · rw [hpoints]
    exact hgp'
  · intro a
    have hh := hplaced.get (i:=(e a).val) (by rw [hlen]; exact (e a).isLt)
      (by rw [hps]; exact (e a).isLt)
    rw [hR] at hh
    simpa [rs,List.get_ofFn,points] using hh

noncomputable def prototypes (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q)) : Finset Point :=
  Finset.univ.image (prototype d (geometries n q D W B hW hEven pi).prototypes)

/-- A concrete finite catalog Placement exists with no assumed GP or small
radius. Its original coordinates, prototypes, grid size and common radius are
all the preceding explicit definitions. -/
theorem placement_exists (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q)) :
    ∃p : Placement d (geometries n q D W B hW hEven pi),
      p.base=fixedBase n q D W B ∧
      p.prototypes=prototypes n q D W B hW hEven pi d ∧
      p.M=(fixedBase n q D W B).card+Fintype.card (Label d (W-1)) ∧
      Function.Injective p.points ∧ (∀l, p.points l ∉ p.base) ∧
      GeneralPosition (p.base ∪ Finset.univ.image p.points) := by
  classical
  let g := geometries n q D W B hW hEven pi
  obtain ⟨points,hinj,hout,hgp,hplaced⟩ := finite_batch (fixedBase n q D W B)
    (prototype d g.prototypes) (fixedBase_general_position n q D W B hW)
    (prototype_below n q D W B hW hEven pi d)
  let p : Placement d g := {
    M := (fixedBase n q D W B).card+Fintype.card (Label d (W-1))
    base := fixedBase n q D W B
    prototypes := prototypes n q D W B hW hEven pi d
    points := points
    frame_mem := by
      intro k
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨frameParameter B k,
        Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,rfl⟩)
    original_mem := by
      intro j
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨parameter n q D W B j,
        Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,rfl⟩)
    prototype_mem := by
      intro l
      exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩
    proto_below := by
      intro r hr
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hr
      exact prototype_below n q D W B hW hEven pi d l
    placed := hplaced }
  exact ⟨p,rfl,rfl,rfl,hinj,hout,hgp⟩

open Q4.Candidate.GeometryEncoding Q4.Candidate.RationalEncoding
open Q4.Candidate.MacroLayout

theorem prototype_provenance (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q)) (l : Label d (W-1)) :
    ActualPrototype (macros n q D) W B
      (prototype d (geometries n q D W B hW hEven pi).prototypes l) := by
  rcases l with ⟨j,i⟩|⟨j,i⟩|⟨j,ell,i⟩|⟨j,ell,i⟩
  · exact Or.inl ⟨_,(earlyBlock n q D W B hW j).mem,rfl⟩
  · exact Or.inl ⟨_,(lateBlock n q D W B hW (latePhysical pi j)).mem,rfl⟩
  · exact Or.inr ⟨_,(earlyBlock n q D W B hW j).mem,
      _,(lateBlock n q D W B hW (latePhysical pi j)).mem,ell.val,by omega,Or.inl rfl⟩
  · exact Or.inr ⟨_,(earlyBlock n q D W B hW j).mem,
      _,(lateBlock n q D W B hW (latePhysical pi j)).mem,ell.val,by omega,Or.inr rfl⟩

/-- A deliberately loose explicit bit budget. In particular this is not the
manuscript parameter H. It includes the actual number of catalog labels. -/
def encodingBudget (n q D W B : ℕ) (d : Recipe (n*q)) : ℕ :=
  10000+8*(n*q+1)+4*(D+1)+W+B+(O n q D W+B+Fintype.card (Label d (W-1)))

def BinaryPoint (K : ℕ) (p : Point) : Prop :=
  ∃nx dx ny dy : ℤ,
    |nx| ≤ (2:ℤ)^K ∧ |dx| ≤ (2:ℤ)^K ∧ dx≠0 ∧ p.1=(nx:ℚ)/(dx:ℚ) ∧
    |ny| ≤ (2:ℤ)^K ∧ |dy| ≤ (2:ℤ)^K ∧ dy≠0 ∧ p.2=(ny:ℚ)/(dy:ℚ)

theorem pointBounded_binary (p : Point) (L k : ℕ) (hp : PointBounded p (2^L) k) :
    BinaryPoint (L*k) p := by
  obtain ⟨nx,dx,hx⟩ := binary_certificate L k hp.1
  obtain ⟨ny,dy,hy⟩ := binary_certificate L k hp.2
  exact ⟨nx,dx,ny,dy,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2,hy⟩

/-- Actual GP coordinates for every base and every program label have one
explicit binary certificate bound, with no determinant-size premise. -/
theorem placement_exists_encoded (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q)) :
    ∃p : Placement d (geometries n q D W B hW hEven pi),
      p.base=fixedBase n q D W B ∧
      p.prototypes=prototypes n q D W B hW hEven pi d ∧
      p.M=O n q D W+B+Fintype.card (Label d (W-1)) ∧
      Function.Injective p.points ∧ (∀l, p.points l ∉ p.base) ∧
      GeneralPosition (p.base ∪ Finset.univ.image p.points) ∧
      (∀z∈p.base ∪ Finset.univ.image p.points,
        BinaryPoint (encodingBudget n q D W B d*(602*(O n q D W+B)+2719)) z) := by
  obtain ⟨p,hbase,hproto,hM,hinj,hout,hgp⟩ := placement_exists n q D W B hW hEven pi d
  have hM' : p.M=O n q D W+B+Fintype.card (Label d (W-1)) := by
    rw [hM,fixedBase_card n q D W B hW]
  have hbcard : p.base.card=O n q D W+B := by
    rw [hbase,fixedBase_card n q D W B hW]
  let L := encodingBudget n q D W B d
  have hpow : L ≤ 2^L := (Nat.lt_two_pow_self).le
  have hlarge : 10000 ≤ 2^L := by dsimp [L,encodingBudget] at hpow ⊢; omega
  have hWH : W ≤ 2^L := by dsimp [L,encodingBudget] at hpow ⊢; omega
  have hBH : B ≤ 2^L := by dsimp [L,encodingBudget] at hpow ⊢; omega
  have hMH : p.M ≤ 2^L := by rw [hM']; dsimp [L,encodingBudget] at hpow ⊢; omega
  have hs : 8*(n*q+1) ≤ 2^L := by dsimp [L,encodingBudget] at hpow ⊢; omega
  have hd : 4*(D+1) ≤ 2^L := by dsimp [L,encodingBudget] at hpow ⊢; omega
  have hA := macros_encoding n q D (2^L) hs hd
  have hbp : ∀z∈p.base, ActualBase (macros n q D) W B z := by
    rw [hbase]
    exact fixedBase_provenance n q D W B hW
  have hrp : ∀z∈p.prototypes, ActualPrototype (macros n q D) W B z := by
    rw [hproto]
    intro z hz
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hz
    exact prototype_provenance n q D W B hW hEven pi d l
  refine ⟨p,hbase,hproto,hM',hinj,hout,hgp,?_⟩
  intro z hz
  apply pointBounded_binary z L _
  rcases Finset.mem_union.mp hz with hz|hz
  · have henc := actual_base_encoding (macros n q D) W B (2^L) hlarge hWH hBH hA z (hbp z hz)
    exact point_encoding_mono henc (by omega) (by omega)
  · obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hz
    have henc := actual_placed_encoding (macros n q D) W B p.M (2^L) hlarge hWH hBH hMH hA hW
      p.base p.prototypes hbp hrp _ _ (p.prototype_mem l) (p.placed l)
    rwa [hbcard] at henc

end Q4.Candidate.ProgramPlacement

#print axioms Q4.Candidate.ProgramPlacement.finite_batch
#print axioms Q4.Candidate.ProgramPlacement.placement_exists
#print axioms Q4.Candidate.ProgramPlacement.prototype_provenance
#print axioms Q4.Candidate.ProgramPlacement.pointBounded_binary
#print axioms Q4.Candidate.ProgramPlacement.placement_exists_encoded
