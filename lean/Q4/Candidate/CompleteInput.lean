import Q4.Candidate.ProgramPlacement
import Q4.Candidate.ProgramIndex

/-! The constructed point set is a legitimate labeled complete straight-line
input: all vertex labels are distinct, all triples are in general position,
and every coordinate has the uniform explicit binary certificate. -/
namespace Q4.Candidate.CompleteInput
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.OriginalVertexLayout Q4.Candidate.ProgramGeometry
open Q4.Candidate.ProgramPlacement Q4.Candidate.ProgramCount Q4.Candidate.ProgramCatalog
open Q4.Candidate.CompleteDrawing
attribute [local instance] Classical.propDecidable

theorem point_injective {N B P : ℕ} (ys : Fin N → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : Function.Injective ys) (ht : Function.Injective ts) (hr : Function.Injective rs)
    (hro : ∀k j, rs k≠original (ys j)) (hrf : ∀k i, rs k≠frame (ts i)) :
    Function.Injective (CompleteDrawing.point ys ts rs) := by
  intro v w h
  rcases v with j|(i|k) <;> rcases w with j'|(i'|k')
  · exact congrArg Sum.inl (hy (original_injective h))
  · exact (original_frame_distinct (ys j) (ts i') h).elim
  · exact (hro k' j h.symm).elim
  · exact (original_frame_distinct (ys j') (ts i) h.symm).elim
  · exact congrArg (fun z => Sum.inr (Sum.inl z)) (ht (frame_injective h))
  · exact (hrf k' i h.symm).elim
  · exact (hro k j' h).elim
  · exact (hrf k i' h).elim
  · exact congrArg (fun z => Sum.inr (Sum.inr z)) (hr h)

theorem point_image {N B P : ℕ} (ys : Fin N → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    Finset.univ.image (CompleteDrawing.point ys ts rs) =
      (Finset.univ.image (fun j => original (ys j)) ∪ Finset.univ.image (fun i => frame (ts i))) ∪
      Finset.univ.image rs := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
    rcases v with j|(i|k)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
  · intro hz
    rcases Finset.mem_union.mp hz with hz|hz
    · rcases Finset.mem_union.mp hz with hz|hz
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨Sum.inl j,Finset.mem_univ _,rfl⟩
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inl i),Finset.mem_univ _,rfl⟩
    · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inr k),Finset.mem_univ _,rfl⟩

theorem program_points_image {S gaps : ℕ} (d : Recipe S) (ps : Label d gaps → Point) :
    Finset.univ.image (ProgramIndex.points d ps)=Finset.univ.image ps := by
  ext z
  simp only [Finset.mem_image,Finset.mem_univ,true_and,ProgramIndex.points]
  constructor
  · rintro ⟨k,hk⟩; exact ⟨(Fintype.equivFin _).symm k,hk⟩
  · rintro ⟨l,hl⟩; exact ⟨Fintype.equivFin _ l,by simpa using hl⟩

theorem actual_point_image (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q))
    (p : Placement d (geometries n q D W B hW hEven pi)) (hbase : p.base=fixedBase n q D W B) :
    Finset.univ.image (CompleteDrawing.point (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points))=
      p.base ∪ Finset.univ.image p.points := by
  rw [point_image,program_points_image,hbase]
  simp only [fixedBase,basePoints,originalParameters,frameParameters,Finset.image_image,Function.comp_def]

theorem actual_point_injective (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q))
    (p : Placement d (geometries n q D W B hW hEven pi))
    (hinj : Function.Injective p.points) (hout : ∀l, p.points l∉p.base) :
    Function.Injective (CompleteDrawing.point (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points)) := by
  apply point_injective _ _ _ (parameter_strictMono n q D W B hW).injective (frameParameter_antitone B).injective
  · exact hinj.comp (Fintype.equivFin _).symm.injective
  · intro k j h
    exact hout _ (h.symm ▸ p.original_mem j)
  · intro k i h
    exact hout _ (h.symm ▸ p.frame_mem i)

/-- The existing finite edge type is the complete geometric graph on these
coordinates, with neither repeated labels nor zero-length represented edges. -/
theorem actual_edge_endpoints_distinct (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q))
    (p : Placement d (geometries n q D W B hW hEven pi))
    (hinj : Function.Injective p.points) (hout : ∀l, p.points l∉p.base)
    (e : Edge (O n q D W) B (Fintype.card (Label d (W-1)))) :
    CompleteDrawing.point (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points) (endpoints e).1 ≠
      CompleteDrawing.point (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points) (endpoints e).2 := by
  intro h
  exact endpoints_ne e (actual_point_injective n q D W B hW hEven pi d p hinj hout h)

/-- One actual placement satisfies all labeled-input requirements at once. -/
theorem complete_input_exists (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q)) :
    ∃p : Placement d (geometries n q D W B hW hEven pi),
      p.base=fixedBase n q D W B ∧
      p.prototypes=ProgramPlacement.prototypes n q D W B hW hEven pi d ∧
      p.M=O n q D W+B+Fintype.card (Label d (W-1)) ∧
      Function.Injective p.points ∧ (∀l, p.points l∉p.base) ∧
      Function.Injective (CompleteDrawing.point (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points)) ∧
      GeneralPosition (Finset.univ.image
        (CompleteDrawing.point (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points))) ∧
      (∀v : CompleteDrawing.Vertex (O n q D W) B (Fintype.card (Label d (W-1))),
        BinaryPoint (encodingBudget n q D W B d*(602*(O n q D W+B)+2719))
          (CompleteDrawing.point (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points) v)) := by
  obtain ⟨p,hbase,hproto,hM,hinj,hout,hgp,hbit⟩ := placement_exists_encoded n q D W B hW hEven pi d
  have he := actual_point_image n q D W B hW hEven pi d p hbase
  refine ⟨p,hbase,hproto,hM,hinj,hout,actual_point_injective n q D W B hW hEven pi d p hinj hout,?_,?_⟩
  · rw [he]
    exact hgp
  · intro v
    apply hbit
    rw [←he]
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩

/-- Natural contiguous indexing of the three actual vertex classes. -/
def vertexEquiv (N B P : ℕ) : CompleteDrawing.Vertex N B P ≃ Fin (N+B+P) :=
  ((Equiv.sumCongr (Equiv.refl (Fin N)) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (Nat.add_assoc N B P).symm)

theorem vertexEquiv_val {N B P : ℕ} (v : CompleteDrawing.Vertex N B P) :
    (vertexEquiv N B P v).val=vertexIndex v := by
  rcases v with j|(i|k)
  · rfl
  · rfl
  · change N+(B+k.val)=N+B+k.val
    omega

def edgeMap (N B P : ℕ) (e : Edge N B P) : Inner (N+B+P) :=
  ⟨(vertexEquiv N B P (endpoints e).1,vertexEquiv N B P (endpoints e).2),by
    change (vertexEquiv N B P (endpoints e).1).val < (vertexEquiv N B P (endpoints e).2).val
    rw [vertexEquiv_val,vertexEquiv_val]
    exact endpoints_increasing e⟩

theorem edgeMap_injective (N B P : ℕ) : Function.Injective (edgeMap N B P) := by
  intro e f h
  have h1 := congrArg (fun z : Inner (N+B+P) => z.val.1) h
  have h2 := congrArg (fun z : Inner (N+B+P) => z.val.2) h
  exact endpoints_injective (Prod.ext ((vertexEquiv N B P).injective h1) ((vertexEquiv N B P).injective h2))

theorem edgeMap_surjective (N B P : ℕ) : Function.Surjective (edgeMap N B P) := by
  intro f
  have hne : (vertexEquiv N B P).symm f.val.1 ≠ (vertexEquiv N B P).symm f.val.2 := by
    intro h
    exact (ne_of_lt f.property) ((vertexEquiv N B P).symm.injective h)
  obtain ⟨e,he|he⟩ := edges_exhaustive _ _ hne
  · refine ⟨e,?_⟩
    apply Subtype.ext
    simp only [edgeMap,he,Equiv.apply_symm_apply]
  · have hh := endpoints_increasing e
    rw [he] at hh
    have h1 := vertexEquiv_val ((vertexEquiv N B P).symm f.val.1)
    have h2 := vertexEquiv_val ((vertexEquiv N B P).symm f.val.2)
    simp only [Equiv.apply_symm_apply] at h1 h2
    dsimp only at hh
    have hf : f.val.1.val < f.val.2.val := f.property
    omega

noncomputable def edgeEquiv (N B P : ℕ) : Edge N B P ≃ Inner (N+B+P) :=
  Equiv.ofBijective (edgeMap N B P) ⟨edgeMap_injective N B P,edgeMap_surjective N B P⟩

theorem edgeEquiv_apply (N B P : ℕ) (e : Edge N B P) : edgeEquiv N B P e=edgeMap N B P e := rfl

def finCoordinates {N B P : ℕ} (ys : Fin N → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    Fin (N+B+P) → Point := fun i => CompleteDrawing.point ys ts rs ((vertexEquiv N B P).symm i)

def plainCross {N : ℕ} (coords : Fin N → Point) (e f : Inner N) : Prop :=
  ProperCross (coords e.val.1) (coords e.val.2) (coords f.val.1) (coords f.val.2)

theorem crossing_transport {N B P : ℕ} (ys : Fin N → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e f : Edge N B P) :
    plainCross (finCoordinates ys ts rs) (edgeEquiv N B P e) (edgeEquiv N B P f) ↔ Cross ys ts rs e f := by
  simp only [edgeEquiv_apply,plainCross,finCoordinates,edgeMap,Equiv.symm_apply_apply,Cross]

open scoped BigOperators
noncomputable def plainPairs {N : ℕ} (coords : Fin N → Point) : Finset (Inner N × Inner N) :=
  Finset.univ.filter (fun p => Fintype.equivFin _ p.1 < Fintype.equivFin _ p.2 ∧ plainCross coords p.1 p.2)
noncomputable def plainEnergy {N : ℕ} (coords : Fin N → Point) (chi : Inner N → Bool) : ℝ :=
  (Q4.monoCount (plainPairs coords).toList chi : ℝ)
noncomputable def plainWeight {N : ℕ} (coords : Fin N → Point) (chi : Inner N → Bool)
    (e f : Inner N) : ℝ := if plainCross coords e f ∧ chi e=chi f then 1 else 0

theorem plainEnergy_double_sum {N : ℕ} (coords : Fin N → Point) (chi : Inner N → Bool) :
    2*plainEnergy coords chi=∑e,∑f,plainWeight coords chi e f := by
  have hs (e f : Inner N) : plainWeight coords chi e f=plainWeight coords chi f e := by
    simp only [plainWeight,plainCross,properCross_swap_edges,eq_comm (a:=chi e)]
  have hz (e : Inner N) : plainWeight coords chi e e=0 := by
    simp [plainWeight,plainCross,ProperCross,orient]
  have hh := CoreFixedPalette.ordered_halfSum (plainWeight coords chi) hs hz
  have hc : plainEnergy coords chi=∑e,∑f,
      if Fintype.equivFin _ e < Fintype.equivFin _ f then plainWeight coords chi e f else 0 := by
    unfold plainEnergy plainPairs
    rw [GridStepBridge.monoCount_list_sum,Finset.sum_map_toList,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    unfold plainWeight
    split_ifs <;> simp_all
  unfold CompleteClassEnergy.halfSum at hh
  rw [hc]
  linarith

theorem energy_transport {N B P : ℕ} (ys : Fin N → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (chi : Edge N B P → Bool) :
    plainEnergy (finCoordinates ys ts rs) (fun e => chi ((edgeEquiv N B P).symm e))=
      CompleteGridEnergy.energy ys ts rs chi := by
  let e := edgeEquiv N B P
  let psi := fun z => chi (e.symm z)
  have hw (a b : Edge N B P) : plainWeight (finCoordinates ys ts rs) psi (e a) (e b)=
      CompleteGridEnergy.weight ys ts rs chi a b := by
    simp only [plainWeight,psi,e,crossing_transport,Equiv.symm_apply_apply,CompleteGridEnergy.weight]
  have hsum : (∑a,∑b,plainWeight (finCoordinates ys ts rs) psi a b)=
      ∑a,∑b,CompleteGridEnergy.weight ys ts rs chi a b := by
    rw [←Equiv.sum_comp e (fun a => ∑b,plainWeight (finCoordinates ys ts rs) psi a b)]
    apply Finset.sum_congr rfl
    intro a _
    rw [←Equiv.sum_comp e (fun b => plainWeight (finCoordinates ys ts rs) psi (e a) b)]
    simp_rw [hw]
  have hP := plainEnergy_double_sum (finCoordinates ys ts rs) psi
  have hC := CompleteGridEnergy.energy_double_sum ys ts rs chi
  rw [hsum] at hP
  linarith

/-- Both directions quantify over all freely chosen colors of every edge. -/
theorem decision_transport {N B P : ℕ} (ys : Fin N → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) (K : ℝ) :
    (∃chi : Edge N B P → Bool, CompleteGridEnergy.energy ys ts rs chi ≤ K) ↔
    (∃psi : Inner (N+B+P) → Bool, plainEnergy (finCoordinates ys ts rs) psi ≤ K) := by
  constructor
  · rintro ⟨chi,hchi⟩
    exact ⟨fun e => chi ((edgeEquiv N B P).symm e),by rwa [energy_transport]⟩
  · rintro ⟨psi,hpsi⟩
    let chi := fun e => psi (edgeEquiv N B P e)
    refine ⟨chi,?_⟩
    have hh := energy_transport ys ts rs chi
    have he : (fun e => chi ((edgeEquiv N B P).symm e))=psi := by funext e; simp [chi]
    rw [he] at hh
    rwa [←hh]

theorem finCoordinates_image {N B P : ℕ} (ys : Fin N → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    Finset.univ.image (finCoordinates ys ts rs)=Finset.univ.image (CompleteDrawing.point ys ts rs) := by
  ext z
  simp only [Finset.mem_image,Finset.mem_univ,true_and,finCoordinates]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨(vertexEquiv N B P).symm i,hi⟩
  · rintro ⟨v,hv⟩; exact ⟨vertexEquiv N B P v,by simpa using hv⟩

/-- An ordinary Fin-indexed rational input for the complete graph, preserving
all the actual placement data used by the cost construction. -/
theorem complete_fin_input_exists (n q D W B : ℕ) (hW : 2 ≤ W) (hEven : Even B)
    (pi : Equiv.Perm (Fin n)) (d : Recipe (n*q)) :
    ∃p : Placement d (geometries n q D W B hW hEven pi),
      p.base=fixedBase n q D W B ∧
      p.prototypes=ProgramPlacement.prototypes n q D W B hW hEven pi d ∧
      p.M=O n q D W+B+Fintype.card (Label d (W-1)) ∧
      Function.Injective p.points ∧ (∀l, p.points l∉p.base) ∧
      Function.Injective (finCoordinates (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points)) ∧
      GeneralPosition (Finset.univ.image
        (finCoordinates (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points))) ∧
      (∀v : Fin (O n q D W+B+Fintype.card (Label d (W-1))),
        BinaryPoint (encodingBudget n q D W B d*(602*(O n q D W+B)+2719))
          (finCoordinates (parameter n q D W B) (frameParameter B) (ProgramIndex.points d p.points) v)) := by
  obtain ⟨p,hbase,hproto,hM,hinj,hout,hpoint,hgp,hbit⟩ := complete_input_exists n q D W B hW hEven pi d
  refine ⟨p,hbase,hproto,hM,hinj,hout,hpoint.comp (vertexEquiv _ _ _).symm.injective,?_,?_⟩
  · rw [finCoordinates_image]
    exact hgp
  · intro v
    exact hbit ((vertexEquiv _ _ _).symm v)

end Q4.Candidate.CompleteInput

#print axioms Q4.Candidate.CompleteInput.actual_point_image
#print axioms Q4.Candidate.CompleteInput.actual_point_injective
#print axioms Q4.Candidate.CompleteInput.actual_edge_endpoints_distinct
#print axioms Q4.Candidate.CompleteInput.complete_input_exists
#print axioms Q4.Candidate.CompleteInput.edgeEquiv
#print axioms Q4.Candidate.CompleteInput.crossing_transport
#print axioms Q4.Candidate.CompleteInput.plainEnergy_double_sum
#print axioms Q4.Candidate.CompleteInput.energy_transport
#print axioms Q4.Candidate.CompleteInput.decision_transport
#print axioms Q4.Candidate.CompleteInput.complete_fin_input_exists
