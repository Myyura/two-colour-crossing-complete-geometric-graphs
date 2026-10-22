import Q4.Candidate.OriginalVertexLayout
import Q4.Candidate.SourceSelectedEdges
import Q4.Candidate.CoreReducedPairs

/-! Exact identification of the actual complete-core main constraint set
with the source retained-selected objective. -/
namespace Q4.Candidate.MainSourceEncoding
open Q4.Candidate.OriginalVertexLayout Q4.Candidate.SourceSelectedEdges
open Q4.Candidate.CoreReducedPairs Q4.Candidate.CoreLocalGeometry
open Q4.Candidate.ProposedPalette Q4.Candidate.PaletteCounting
open Q4.Candidate.MacroLayout Q4.Candidate.GlobalGeometryScales
open Q4.Candidate.ConvexSeparation Q4.Candidate.OriginalCapAlternation
attribute [local instance] Classical.propDecidable

abbrev O (n q D W : ℕ) := n*q*W+D+n*q*W

def selectedCore {n q W : ℕ} (D : ℕ) (pi : Equiv.Perm (Fin n)) (e : Selected n q W) : CoreEdge (O n q D W) :=
  ⟨(earlyIndex n q D W (sourceBlock e.1 e.2.1) e.2.2.1,
      lateIndex n q D W (sourceBlock (pi e.1).rev e.2.1.rev) e.2.2.2),by
    have he := block_rank_lt n q W (sourceBlock e.1 e.2.1) e.2.2.1
    change (sourceBlock e.1 e.2.1).val*W+e.2.2.1.val <
      n*q*W+D+((sourceBlock (pi e.1).rev e.2.1.rev).val*W+e.2.2.2.val)
    omega⟩

theorem selectedCore_endpoints {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (e : Selected n q W) :
    (original (parameter n q D W B (selectedCore D pi e).val.1),
      original (parameter n q D W B (selectedCore D pi e).val.2)) =
    selectedEndpoints pi (cloneScale (macros n q D) W B) e :=
  source_endpoints_match D W B hW pi e.1 e.2.1 e.2.2.1 e.2.2.2

theorem selectedCore_injective {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) : Function.Injective (selectedCore (q:=q) (W:=W) D pi) := by
  intro e f he
  have ht := common_source_width n q D W B
  apply selected_endpoints_injective pi _ hW ht.1 ht.2
  rw [←selectedCore_endpoints D B hW pi e,←selectedCore_endpoints D B hW pi f,he]

theorem selectedCore_selected {n q W : ℕ} (D : ℕ) (hW : 0 < W)
    (pi : Equiv.Perm (Fin n)) (e : Selected n q W) :
    selectedEdge (indexedSite (n*q) W D hW (sitePermutation pi)) (sourceBlock e.1 e.2.1)
      (selectedCore D pi e) := by
  let site := indexedSite (n*q) W D hW (sitePermutation pi)
  let j := sourceBlock e.1 e.2.1
  have hf := indexed_fibers (n*q) W D hW (sitePermutation pi) j
  have hb := indexed_bounds (n*q) W D (sitePermutation pi) j
  have he := site_endpoint_early site j hf hb.1 e.2.2.1
  have hl := site_endpoint_late site j hf hb.2.1 e.2.2.2
  have hm := palette_endpoints_match D W pi e.1 e.2.1 e.2.2.1 e.2.2.2
  change site (earlyEndpoint (n*q) W D (sitePermutation pi) j e.2.2.1)=.early j at he
  change site (lateEndpoint (n*q) W D (sitePermutation pi) j e.2.2.2)=.late j at hl
  dsimp only [j] at he hl
  rw [hm.1] at he
  rw [hm.2] at hl
  exact Or.inl ⟨he,hl⟩

theorem selectedCore_exhaustive {n q W : ℕ} (D : ℕ) (hW : 0 < W)
    (pi : Equiv.Perm (Fin n)) (e : CoreEdge (O n q D W))
    (he : ∃j, selectedEdge (indexedSite (n*q) W D hW (sitePermutation pi)) j e) :
    ∃s : Selected n q W, selectedCore D pi s=e := by
  obtain ⟨j,hj⟩ := he
  let vj := finProdFinEquiv.symm j
  have hj' : sourceBlock vj.1 vj.2=j := by rw [sourceBlock_equiv]; exact finProdFinEquiv.apply_symm_apply j
  have hf := indexed_fibers (n*q) W D hW (sitePermutation pi) j
  have hb := indexed_bounds (n*q) W D (sitePermutation pi) j
  rcases hj with hj|hj
  · obtain ⟨r,hr⟩ := endpoint_exists hb.1 e.val.1 ((hf.early _).1 hj.1)
    obtain ⟨t,ht⟩ := endpoint_exists hb.2.1 e.val.2 ((hf.late _).1 hj.2)
    refine ⟨(vj.1,(vj.2,(r,t))),?_⟩
    have hm := palette_endpoints_match D W pi vj.1 vj.2 r t
    apply Subtype.ext
    apply Prod.ext
    · change earlyIndex n q D W (sourceBlock vj.1 vj.2) r=e.val.1
      rw [←hm.1,hj']
      exact hr
    · change lateIndex n q D W (sourceBlock (pi vj.1).rev vj.2.rev) t=e.val.2
      rw [←hm.2,hj']
      exact ht
  · have h1 := (hf.late _).1 hj.1
    have h2 := (hf.early _).1 hj.2
    have heord := e.property
    change e.val.1.val<e.val.2.val at heord
    omega

theorem selectedCore_crossing {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (e f : Selected n q W) :
    cross (parameter n q D W B) (selectedCore D pi e).val.1 (selectedCore D pi e).val.2
      (selectedCore D pi f).val.1 (selectedCore D pi f).val.2 ↔
    ProperCross (selectedEndpoints pi (cloneScale (macros n q D) W B) e).1
      (selectedEndpoints pi (cloneScale (macros n q D) W B) e).2
      (selectedEndpoints pi (cloneScale (macros n q D) W B) f).1
      (selectedEndpoints pi (cloneScale (macros n q D) W B) f).2 := by
  have he := selectedCore_endpoints D B hW pi e
  have hf := selectedCore_endpoints D B hW pi f
  unfold cross
  rw [←congrArg Prod.fst he,←congrArg Prod.snd he,←congrArg Prod.fst hf,←congrArg Prod.snd hf]

theorem sourceBlock_pair_eq {n q W : ℕ} (e f : Selected n q W) :
    sourceBlock e.1 e.2.1=sourceBlock f.1 f.2.1 ↔ (e.1,e.2.1)=(f.1,f.2.1) := by
  rw [sourceBlock_equiv,sourceBlock_equiv]
  exact finProdFinEquiv.injective.eq_iff

theorem main_selected_iff {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (e f : Selected n q W) :
    (selectedCore D pi e,selectedCore D pi f) ∈ mainPairs (parameter n q D W B)
      (indexedSite (n*q) W D (by omega) (sitePermutation pi)) ↔
    edgeRank (O n q D W) (selectedCore D pi e) < edgeRank (O n q D W) (selectedCore D pi f) ∧
    ((e,f) ∈ retainedPairs pi (cloneScale (macros n q D) W B) ∨
      (f,e) ∈ retainedPairs pi (cloneScale (macros n q D) W B)) := by
  have ht := common_source_width n q D W B
  let site := indexedSite (n*q) W D (show 0<W by omega) (sitePermutation pi)
  have he := selectedCore_selected D (by omega) pi e
  have hf := selectedCore_selected D (by omega) pi f
  have hel := (local_split site (sourceBlock e.1 e.2.1) _).2 (Or.inr he)
  have hfl := (local_split site (sourceBlock f.1 f.2.1) _).2 (Or.inr hf)
  constructor
  · intro h
    obtain ⟨j,k,hjk,hj,hk⟩ := (Finset.mem_filter.mp h).2
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
    have hje := local_unique site j (sourceBlock e.1 e.2.1) _
      ((local_split site j _).2 (Or.inr hj)) hel
    have hkf := local_unique site k (sourceBlock f.1 f.2.1) _
      ((local_split site k _).2 (Or.inr hk)) hfl
    have hne : (e.1,e.2.1)≠(f.1,f.2.1) := by
      intro hsame
      exact hjk (hje.trans (((sourceBlock_pair_eq e f).2 hsame).trans hkf.symm))
    refine ⟨hp.2.2.1,?_⟩
    apply (retained_exhaustive pi _ hW ht.1.le ht.2 e f).1
    exact ⟨hne,(selectedCore_crossing D B hW pi e f).1 hp.2.2.2⟩
  · rintro ⟨hr,hp⟩
    have hh := (retained_exhaustive pi _ hW ht.1.le ht.2 e f).2 hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,local_not_palette site _ _ hel,
      local_not_palette site _ _ hfl,hr,(selectedCore_crossing D B hW pi e f).2 hh.2⟩,
      sourceBlock e.1 e.2.1,sourceBlock f.1 f.2.1,?_,he,hf⟩
    exact fun h => hh.1 ((sourceBlock_pair_eq e f).1 h)

theorem edgeRank_injective (O : ℕ) : Function.Injective (edgeRank O) := by
  intro e f h
  apply (Fintype.equivFin (CoreEdge O)).injective
  exact Fin.ext h

noncomputable def encodePair {n q W : ℕ} (D : ℕ) (pi : Equiv.Perm (Fin n))
    (p : Selected n q W × Selected n q W) : CoreEdge (O n q D W) × CoreEdge (O n q D W) :=
  if edgeRank _ (selectedCore D pi p.1) < edgeRank _ (selectedCore D pi p.2)
  then (selectedCore D pi p.1,selectedCore D pi p.2)
  else (selectedCore D pi p.2,selectedCore D pi p.1)

theorem encodePair_mem {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (p : Selected n q W × Selected n q W)
    (hp : p∈retainedPairs pi (cloneScale (macros n q D) W B)) :
    encodePair D pi p ∈ mainPairs (parameter n q D W B)
      (indexedSite (n*q) W D (by omega) (sitePermutation pi)) := by
  have ht := common_source_width n q D W B
  have hs := (retained_predicate pi _ hW ht.1.le ht.2 p.1 p.2).1 hp
  have hne : edgeRank _ (selectedCore D pi p.1) ≠ edgeRank _ (selectedCore D pi p.2) := by
    intro h
    have he := selectedCore_injective D B hW pi (edgeRank_injective _ h)
    have hv := congrArg Prod.fst he
    exact (ne_of_lt hs.1) hv
  unfold encodePair
  split_ifs with hr
  · exact (main_selected_iff D B hW pi p.1 p.2).2 ⟨hr,Or.inl hp⟩
  · exact (main_selected_iff D B hW pi p.2 p.1).2
      ⟨lt_of_le_of_ne (le_of_not_gt hr) hne.symm,Or.inr hp⟩

theorem encodePair_injective_on {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (p z : Selected n q W × Selected n q W)
    (hp : p∈retainedPairs pi (cloneScale (macros n q D) W B))
    (hz : z∈retainedPairs pi (cloneScale (macros n q D) W B))
    (he : encodePair D pi p=encodePair D pi z) : p=z := by
  have ht := common_source_width n q D W B
  have hpv := (retained_predicate pi _ hW ht.1.le ht.2 p.1 p.2).1 hp
  have hzv := (retained_predicate pi _ hW ht.1.le ht.2 z.1 z.2).1 hz
  have hinj := selectedCore_injective (q:=q) D B hW pi
  unfold encodePair at he
  split_ifs at he with hp' hz' hz'
  · exact Prod.ext (hinj (congrArg Prod.fst he)) (hinj (congrArg Prod.snd he))
  · have h1 := hinj (congrArg Prod.fst he)
    have h2 := hinj (congrArg Prod.snd he)
    rw [h1,h2] at hpv
    exact (lt_asymm hpv.1 hzv.1).elim
  · have h1 := hinj (congrArg Prod.fst he)
    have h2 := hinj (congrArg Prod.snd he)
    rw [h1,h2] at hpv
    exact (lt_asymm hpv.1 hzv.1).elim
  · exact Prod.ext (hinj (congrArg Prod.snd he)) (hinj (congrArg Prod.fst he))

theorem encodePair_surjective_on {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (p : CoreEdge (O n q D W) × CoreEdge (O n q D W))
    (hp : p∈mainPairs (parameter n q D W B)
      (indexedSite (n*q) W D (by omega) (sitePermutation pi))) :
    ∃z∈retainedPairs pi (cloneScale (macros n q D) W B), encodePair D pi z=p := by
  rcases p with ⟨a,b⟩
  obtain ⟨j,k,hjk,hj,hk⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨e,rfl⟩ := selectedCore_exhaustive D (by omega) pi a ⟨j,hj⟩
  obtain ⟨f,rfl⟩ := selectedCore_exhaustive D (by omega) pi b ⟨k,hk⟩
  have hh := (main_selected_iff D B hW pi e f).1 hp
  rcases hh.2 with he|hf
  · exact ⟨(e,f),he,by simp only [encodePair,hh.1,↓reduceIte]⟩
  · exact ⟨(f,e),hf,by simp only [encodePair,not_lt_of_gt hh.1,↓reduceIte]⟩

theorem monoCount_finset {α : Type*} (es : Finset (α×α)) (chi : α → Bool) :
    Q4.monoCount es.toList chi = ∑p∈es, if chi p.1=chi p.2 then 1 else 0 := by
  have hl (xs : List (α×α)) : Q4.monoCount xs chi =
      (xs.map (fun p => if chi p.1=chi p.2 then (1:ℕ) else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons p xs ih =>
      rcases p with ⟨a,b⟩
      by_cases hc : chi a=chi b <;> simp [Q4.monoCount,hc,ih]
  rw [hl,Finset.sum_map_toList]

/-- Exact energy equality on the actual complete-core edge set. The pair
ordering changes, but each physical crossing and its common coloring occurs once. -/
theorem main_energy_eq_retained {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (chi : CoreEdge (O n q D W) → Bool) :
    pairEnergy (mainPairs (parameter n q D W B)
      (indexedSite (n*q) W D (by omega) (sitePermutation pi))) chi =
    Q4.monoCount (retainedPairs pi (cloneScale (macros n q D) W B)).toList
      (fun e => chi (selectedCore D pi e)) := by
  rw [monoCount_finset]
  unfold pairEnergy
  symm
  apply Finset.sum_bij (fun p _ => encodePair D pi p)
  · intro p hp; exact encodePair_mem D B hW pi p hp
  · intro p hp z hz he; exact encodePair_injective_on D B hW pi p z hp hz he
  · intro p hp
    obtain ⟨z,hz,he⟩ := encodePair_surjective_on D B hW pi p hp
    exact ⟨z,hz,he⟩
  · intro p hp
    unfold encodePair
    split_ifs <;> simp_all

theorem selected_coloring_extension {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (psi : Selected n q W → Bool) :
    ∃chi : CoreEdge (O n q D W) → Bool, ∀e, chi (selectedCore D pi e)=psi e := by
  classical
  let chi : CoreEdge (O n q D W) → Bool := fun e =>
    if h : ∃s, selectedCore D pi s=e then psi (Classical.choose h) else false
  refine ⟨chi,?_⟩
  intro e
  have hex : ∃s, selectedCore D pi s=selectedCore D pi e := ⟨e,rfl⟩
  dsimp only [chi]
  simp only [hex,↓reduceDIte]
  have he := selectedCore_injective D B hW pi (Classical.choose_spec hex)
  rw [he]

/-- Both directions of the exact free optimum, now for the actual full
core's mainPairs and a coloring of every core edge, not a separate label graph. -/
theorem actual_main_minimum {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) :
    (∀chi : CoreEdge (O n q D W) → Bool,
      (q:ℤ)^2*(W:ℤ)^4*(Q4.Candidate.CoreEncoding.sourceOpt (sourcePairs pi).toList:ℤ) ≤
      (pairEnergy (mainPairs (parameter n q D W B)
        (indexedSite (n*q) W D (by omega) (sitePermutation pi))) chi:ℤ)) ∧
    (∃chi : CoreEdge (O n q D W) → Bool,
      (pairEnergy (mainPairs (parameter n q D W B)
        (indexedSite (n*q) W D (by omega) (sitePermutation pi))) chi:ℤ) =
      (q:ℤ)^2*(W:ℤ)^4*(Q4.Candidate.CoreEncoding.sourceOpt (sourcePairs pi).toList:ℤ)) := by
  have ht := common_source_width n q D W B
  have hopt := retained_minimum (q:=q) pi _ hW ht.1.le ht.2
  constructor
  · intro chi
    rw [main_energy_eq_retained D B hW pi chi]
    exact hopt.1 _
  · obtain ⟨psi,hpsi⟩ := hopt.2
    obtain ⟨chi,hchi⟩ := selected_coloring_extension D B hW pi psi
    refine ⟨chi,?_⟩
    rw [main_energy_eq_retained D B hW pi chi]
    have he : (fun e => chi (selectedCore D pi e))=psi := funext hchi
    rw [he]
    exact hpsi

/-- Every given source coloring, not only an optimal one, lifts to colors
of every actual core edge with the exact main-energy multiplier. -/
theorem source_coloring_lift {n q W : ℕ} (D B : ℕ) (hW : 2 ≤ W)
    (pi : Equiv.Perm (Fin n)) (z : Fin n → Bool) :
    ∃chi : CoreEdge (O n q D W) → Bool,
      (∀e : Selected n q W, chi (selectedCore D pi e)=z e.1) ∧
      (pairEnergy (mainPairs (parameter n q D W B)
        (indexedSite (n*q) W D (by omega) (sitePermutation pi))) chi:ℤ) =
      (q:ℤ)^2*(W:ℤ)^4*(Q4.monoCount (sourcePairs pi).toList z:ℤ) := by
  obtain ⟨chi,hchi⟩ := selected_coloring_extension D B hW pi (fun e => z e.1)
  refine ⟨chi,hchi,?_⟩
  rw [main_energy_eq_retained D B hW pi chi]
  have he : (fun e => chi (selectedCore D pi e))=(fun e : Selected n q W => z e.1) := funext hchi
  rw [he]
  have ht := common_source_width n q D W B
  rw [retained_energy pi _ hW ht.1.le ht.2]
  change Q4.Candidate.CoreEncoding.blowEnergy (Finset.univ : Finset (Copy q W)).toList
    (sourcePairs pi).toList (Q4.Candidate.CoreEncoding.liftColor z)=_
  rw [Q4.Candidate.CoreEncoding.lift_energy]
  simp only [Finset.length_toList,Finset.card_univ,Copy,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  ring

#print axioms selectedCore_injective
#print axioms selectedCore_exhaustive
#print axioms selectedCore_crossing
#print axioms main_selected_iff
#print axioms encodePair_mem
#print axioms encodePair_injective_on
#print axioms encodePair_surjective_on
#print axioms main_energy_eq_retained
#print axioms selected_coloring_extension
#print axioms actual_main_minimum
#print axioms source_coloring_lift

end Q4.Candidate.MainSourceEncoding

