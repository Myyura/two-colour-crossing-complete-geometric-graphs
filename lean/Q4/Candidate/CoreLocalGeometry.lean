import Q4.Candidate.ProposedPalette
import Q4.Candidate.CompleteProbeFreezing

/-! Actual free core-edge classification and localization of every crossing
involving a short edge. Local constraints are counted with a conservative bound;
no selected edge or complete-graph edge is removed from the output. -/
namespace Q4.Candidate.CoreLocalGeometry
open Q4.Candidate.ProposedPalette Q4.Candidate.PaletteCounting
open Q4.Candidate.OriginalCapAlternation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def belongs {S : ℕ} (j : Fin S) (s : Site S) : Prop := s = .early j ∨ s = .late j

def localEdge {O S : ℕ} (site : Fin O → Site S) (j : Fin S) (e : CoreEdge O) : Prop :=
  belongs j (site e.val.1) ∧ belongs j (site e.val.2)

def dummyEdge {O S : ℕ} (site : Fin O → Site S) (e : CoreEdge O) : Prop :=
  site e.val.1 = .dummy ∧ site e.val.2 = .dummy

def shortEdge {O S : ℕ} (site : Fin O → Site S) (j : Fin S) (e : CoreEdge O) : Prop :=
  (site e.val.1 = .early j ∧ site e.val.2 = .early j) ∨
  (site e.val.1 = .late j ∧ site e.val.2 = .late j)

theorem free_classification {O S : ℕ} (site : Fin O → Site S) (e : CoreEdge O) :
    e ∉ palette site ↔ dummyEdge site e ∨ ∃ j, localEdge site j e := by
  simp only [palette,Finset.mem_filter,Finset.mem_univ,true_and]
  unfold dummyEdge localEdge belongs
  cases site e.val.1 <;> cases site e.val.2 <;> simp [allowed,eq_comm]

theorem local_unique {O S : ℕ} (site : Fin O → Site S) (j k : Fin S) (e : CoreEdge O)
    (hj : localEdge site j e) (hk : localEdge site k e) : j = k := by
  rcases hj.1 with h|h <;> rcases hk.1 with h'|h' <;> rw [h] at h' <;> simp_all

theorem free_incident_early {S : ℕ} (j : Fin S) (s : Site S)
    (h : ¬allowed (.early j) s) : belongs j s := by
  cases s <;> simp_all [allowed,belongs,eq_comm]

theorem free_incident_late {S : ℕ} (j : Fin S) (s : Site S)
    (h : ¬allowed (.late j) s) : belongs j s := by
  cases s <;> simp_all [allowed,belongs,eq_comm]

theorem early_between {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j) (u v x : Fin O)
    (hu : site u = .early j) (hv : site v = .early j) (hux : u<x) (hxv : x<v) :
    site x = .early j := by
  apply (hf.early x).2
  have hu' := (hf.early u).1 hu
  have hv' := (hf.early v).1 hv
  have hx := show u.val<x.val from hux
  have hy := show x.val<v.val from hxv
  omega

theorem late_between {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j) (u v x : Fin O)
    (hu : site u = .late j) (hv : site v = .late j) (hux : u<x) (hxv : x<v) :
    site x = .late j := by
  apply (hf.late x).2
  have hu' := (hf.late u).1 hu
  have hv' := (hf.late v).1 hv
  have hx := show u.val<x.val from hux
  have hy := show x.val<v.val from hxv
  omega

/-- Every still-free actual neighbor of a short edge belongs to its own
selected bundle. No independence of omitted endpoints is assumed. -/
theorem short_cross_free_local {O S W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (site : Fin O → Site S) (j : Fin S) (hf : BlockFibers site W a b j)
    (e f : CoreEdge O) (he : shortEdge site j e) (hfree : f ∉ palette site)
    (hc : cross ys e.val.1 e.val.2 f.val.1 f.val.2) : localEdge site j f := by
  have hnot : ¬allowed (site f.val.1) (site f.val.2) := by simpa [palette] using hfree
  have hrev : ¬allowed (site f.val.2) (site f.val.1) := fun h => hnot ((allowed_symm _ _).2 h)
  rcases (cross_ordered ys hy _ _ _ _ e.property f.property).1 hc with hc|hc
  · rcases he with he|he
    · have hs := early_between site j hf _ _ _ he.1 he.2 hc.1 hc.2.1
      refine ⟨Or.inl hs,?_⟩
      rw [hs] at hnot
      exact free_incident_early j _ hnot
    · have hs := late_between site j hf _ _ _ he.1 he.2 hc.1 hc.2.1
      refine ⟨Or.inr hs,?_⟩
      rw [hs] at hnot
      exact free_incident_late j _ hnot
  · rcases he with he|he
    · have hs := early_between site j hf _ _ _ he.1 he.2 hc.2.1 hc.2.2
      refine ⟨?_,Or.inl hs⟩
      rw [hs] at hrev
      exact free_incident_early j _ hrev
    · have hs := late_between site j hf _ _ _ he.1 he.2 hc.2.1 hc.2.2
      refine ⟨?_,Or.inr hs⟩
      rw [hs] at hrev
      exact free_incident_late j _ hrev

theorem indexed_short_cross_free_local (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (j : Fin S)
    (e f : CoreEdge (S*W+D+S*W))
    (he : shortEdge (indexedSite S W D hW pi) j e)
    (hfree : f ∉ palette (indexedSite S W D hW pi))
    (hc : cross ys e.val.1 e.val.2 f.val.1 f.val.2) :
    localEdge (indexedSite S W D hW pi) j f :=
  short_cross_free_local ys hy _ j (indexed_fibers S W D hW pi j) e f he hfree hc


noncomputable def vertices {O S : ℕ} (site : Fin O → Site S) (j : Fin S) : Finset (Fin O) :=
  Finset.univ.filter (fun y => belongs j (site y))

theorem vertices_card {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j) (ha : a+W≤O) (hb : b+W≤O) :
    (vertices site j).card ≤ 2*W := by
  have hs : vertices site j ⊆
      (Finset.univ.image (endpoint a ha)) ∪ (Finset.univ.image (endpoint b hb)) := by
    intro y hy
    rcases (Finset.mem_filter.mp hy).2 with he|hl
    · obtain ⟨r,rfl⟩ := endpoint_exists ha y ((hf.early y).1 he)
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩)
    · obtain ⟨r,rfl⟩ := endpoint_exists hb y ((hf.late y).1 hl)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩)
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have he := Finset.card_image_le (s := (Finset.univ : Finset (Fin W))) (f := endpoint a ha)
  have hl := Finset.card_image_le (s := (Finset.univ : Finset (Fin W))) (f := endpoint b hb)
  simp only [Finset.card_univ,Fintype.card_fin] at he hl
  omega

/-- An asymmetric ordered pair relation has at most half the square of the
vertex count. Both orientations inject into the full Cartesian square. -/
theorem asymmetric_pair_card {α : Type*} [Fintype α] (r : α → α → Prop)
    [DecidableRel r] (hasym : ∀a b, r a b → ¬r b a) :
    2*Fintype.card {p : α×α // r p.1 p.2} ≤ (Fintype.card α)^2 := by
  let f : Bool × {p : α×α // r p.1 p.2} → α×α :=
    fun p => if p.1 then p.2.val.swap else p.2.val
  have hf : Function.Injective f := by
    rintro ⟨b,p⟩ ⟨c,q⟩ he
    cases b <;> cases c
    · simp only [f,Bool.false_eq_true,ite_false,Prod.mk.injEq,true_and] at he ⊢
      exact Subtype.ext he
    · simp only [f,Bool.false_eq_true,ite_false,ite_true] at he
      have hp := p.property
      rw [he] at hp
      exact (hasym _ _ q.property hp).elim
    · simp only [f,Bool.false_eq_true,ite_false,ite_true] at he
      have hq := q.property
      rw [←he] at hq
      exact (hasym _ _ p.property hq).elim
    · simp only [f,ite_true,Prod.mk.injEq,true_and] at he ⊢
      exact Subtype.ext (Prod.swap_injective he)
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod,pow_two] using hc

/-- Every local edge is an actual edge on the two parent W-blocks. -/
def localToPair {O S : ℕ} (site : Fin O → Site S) (j : Fin S)
    (e : {e : CoreEdge O // localEdge site j e}) :
    {p : {y : Fin O // y ∈ vertices site j} × {y : Fin O // y ∈ vertices site j} // p.1.val < p.2.val} :=
  ⟨(⟨e.val.val.1,by simpa [vertices] using e.property.1⟩,
     ⟨e.val.val.2,by simpa [vertices] using e.property.2⟩), e.val.property⟩

theorem localToPair_injective {O S : ℕ} (site : Fin O → Site S) (j : Fin S) :
    Function.Injective (localToPair site j) := by
  intro e f he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun p => (p.val.1.val,p.val.2.val)) he

theorem local_edges_card {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j) (ha : a+W≤O) (hb : b+W≤O) :
    Fintype.card {e : CoreEdge O // localEdge site j e} ≤ 2*W^2 := by
  have hc := Fintype.card_le_of_injective _ (localToPair_injective site j)
  have hp := asymmetric_pair_card
    (fun x y : {y : Fin O // y ∈ vertices site j} => x.val < y.val)
    (fun _ _ h => lt_asymm h)
  simp only [Fintype.card_coe] at hp
  have hv := vertices_card site j hf ha hb
  nlinarith [sq_nonneg ((vertices site j).card : ℤ)]


noncomputable def edgeRank (O : ℕ) (e : CoreEdge O) : ℕ := (Fintype.equivFin _ e).val

noncomputable def localPairs {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S)
    (j : Fin S) : Finset (CoreEdge O × CoreEdge O) :=
  Finset.univ.filter (fun p => localEdge site j p.1 ∧ localEdge site j p.2 ∧
    edgeRank O p.1 < edgeRank O p.2 ∧ cross ys p.1.val.1 p.1.val.2 p.2.val.1 p.2.val.2)

theorem local_pairs_card {O S W a b : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S)
    (j : Fin S) (hf : BlockFibers site W a b j) (ha : a+W≤O) (hb : b+W≤O) :
    (localPairs ys site j).card ≤ 2*W^4 := by
  let E := {e : CoreEdge O // localEdge site j e}
  let r : E → E → Prop := fun e f => edgeRank O e.val < edgeRank O f.val
  let f : {p // p ∈ localPairs ys site j} → {p : E×E // r p.1 p.2} := fun p =>
    ⟨(⟨p.val.1,(Finset.mem_filter.mp p.property).2.1⟩,
       ⟨p.val.2,(Finset.mem_filter.mp p.property).2.2.1⟩),
      (Finset.mem_filter.mp p.property).2.2.2.1⟩
  have hf' : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    exact congrArg (fun p => (p.val.1.val,p.val.2.val)) h
  have hc := Fintype.card_le_of_injective f hf'
  have hp := asymmetric_pair_card r (fun _ _ h => lt_asymm h)
  have he := local_edges_card site j hf ha hb
  simp only [Fintype.card_coe] at hc
  change Fintype.card E ≤ 2*W^2 at he
  have he2 := Nat.mul_le_mul he he
  nlinarith [show W^2*W^2=W^4 by ring]

noncomputable def allLocalPairs {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S) :
    Finset (CoreEdge O × CoreEdge O) := Finset.univ.biUnion (localPairs ys site)

theorem indexed_allLocalPairs_card (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) :
    (allLocalPairs ys (indexedSite S W D hW pi)).card ≤ 2*S*W^4 := by
  have hh := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin S)))
    (t := localPairs ys (indexedSite S W D hW pi))
  have hb (j : Fin S) : (localPairs ys (indexedSite S W D hW pi) j).card ≤ 2*W^4 :=
    local_pairs_card ys _ j (indexed_fibers S W D hW pi j)
      (indexed_bounds S W D pi j).1 (indexed_bounds S W D pi j).2.1
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin S))) => hb j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  unfold allLocalPairs
  nlinarith


def selectedEdge {O S : ℕ} (site : Fin O → Site S) (j : Fin S) (e : CoreEdge O) : Prop :=
  (site e.val.1 = .early j ∧ site e.val.2 = .late j) ∨
  (site e.val.1 = .late j ∧ site e.val.2 = .early j)

theorem local_split {O S : ℕ} (site : Fin O → Site S) (j : Fin S) (e : CoreEdge O) :
    localEdge site j e ↔ shortEdge site j e ∨ selectedEdge site j e := by
  unfold localEdge belongs shortEdge selectedEdge
  tauto

theorem short_is_local {O S : ℕ} (site : Fin O → Site S) (j : Fin S) (e : CoreEdge O)
    (he : shortEdge site j e) : localEdge site j e := (local_split site j e).2 (Or.inl he)

/-- Deleting the actual local crossing set removes every free neighbor of
any short edge. Palette and program neighbors remain as their actual unaries. -/
theorem short_pair_in_local {O S W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (site : Fin O → Site S) (j : Fin S) (hf : BlockFibers site W a b j)
    (e f : CoreEdge O) (he : shortEdge site j e) (hfree : f ∉ palette site)
    (hr : edgeRank O e < edgeRank O f)
    (hc : cross ys e.val.1 e.val.2 f.val.1 f.val.2) : (e,f) ∈ allLocalPairs ys site := by
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_univ _,?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,short_is_local site j e he,
    short_cross_free_local ys hy site j hf e f he hfree hc,hr,hc⟩

/-- Uniform actual restoration bound for any common choice of every core
color. It never chooses a different auxiliary coloring for different pairs. -/
theorem actual_local_restoration (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (chi : CoreEdge (S*W+D+S*W) → Bool) :
    Q4.monoCount (allLocalPairs ys (indexedSite S W D hW pi)).toList chi ≤ 2*S*W^4 := by
  have hc := Q4.mono_add_cut (allLocalPairs ys (indexedSite S W D hW pi)).toList chi
  have hb := indexed_allLocalPairs_card S W D hW pi ys
  rw [Finset.length_toList] at hc
  omega

end Q4.Candidate.CoreLocalGeometry
#print axioms Q4.Candidate.CoreLocalGeometry.free_classification
#print axioms Q4.Candidate.CoreLocalGeometry.local_unique
#print axioms Q4.Candidate.CoreLocalGeometry.short_cross_free_local
#print axioms Q4.Candidate.CoreLocalGeometry.indexed_short_cross_free_local

#print axioms Q4.Candidate.CoreLocalGeometry.local_edges_card

#print axioms Q4.Candidate.CoreLocalGeometry.local_pairs_card
#print axioms Q4.Candidate.CoreLocalGeometry.indexed_allLocalPairs_card

#print axioms Q4.Candidate.CoreLocalGeometry.short_pair_in_local
#print axioms Q4.Candidate.CoreLocalGeometry.actual_local_restoration
