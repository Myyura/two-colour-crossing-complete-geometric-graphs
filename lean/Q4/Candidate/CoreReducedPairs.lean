import Q4.Candidate.CoreLocalGeometry
import Q4.Candidate.DummyGeometry

/-! Exhaustive actual free-pair decomposition after deleting local crossing
constraints. It is proved for the entire indexed core, not a selected subgraph. -/
namespace Q4.Candidate.CoreReducedPairs
open Q4.Candidate.CoreLocalGeometry Q4.Candidate.ProposedPalette
open Q4.Candidate.PaletteCounting Q4.Candidate.OriginalCapAlternation
open Q4.Candidate.ConvexSeparation
attribute [local instance] Classical.propDecidable

variable {O S : ℕ}

theorem local_not_palette (site : Fin O → Site S) (j : Fin S) (e : CoreEdge O)
    (he : localEdge site j e) : e ∉ palette site :=
  (free_classification site e).2 (Or.inr ⟨j,he⟩)

theorem dummy_not_palette (site : Fin O → Site S) (e : CoreEdge O)
    (he : dummyEdge site e) : e ∉ palette site := (free_classification site e).2 (Or.inl he)

theorem dummy_not_local (site : Fin O → Site S) (e : CoreEdge O) (j : Fin S)
    (he : dummyEdge site e) : ¬localEdge site j e := by
  intro h
  rcases h.1 with h|h <;> rw [he.1] at h <;> cases h

theorem dummy_no_local_cross (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (j : Fin S)
    (e f : CoreEdge (S*W+D+S*W))
    (he : localEdge (indexedSite S W D hW pi) j e)
    (hf : dummyEdge (indexedSite S W D hW pi) f) :
    ¬cross ys e.val.1 e.val.2 f.val.1 f.val.2 := by
  let site := indexedSite S W D hW pi
  have hb := indexed_fibers S W D hW pi j
  have hf1 := indexed_dummy_middle S W D hW pi j f.val.1 hf.1
  have hf2 := indexed_dummy_middle S W D hW pi j f.val.2 hf.2
  rcases (local_split site j e).1 he with hs|hs
  · intro hc
    have hh := indexed_short_cross_free_local S W D hW pi ys hy j e f hs
      (dummy_not_palette site f hf) hc
    exact dummy_not_local site f j hf hh
  · rcases hs with hs|hs
    · have h1 := (hb.early e.val.1).1 hs.1
      have h2 := (hb.late e.val.2).1 hs.2
      have he1 : e.val.1 < f.val.1 := by change e.val.1.val < f.val.1.val; omega
      have he2 : f.val.2 < e.val.2 := by change f.val.2.val < e.val.2.val; omega
      rw [cross_ordered ys hy _ _ _ _ e.property f.property]
      rintro (h|h)
      · exact lt_asymm he2 h.2.2
      · exact lt_asymm he1 h.1
    · have h1 := (hb.late e.val.1).1 hs.1
      have h2 := (hb.early e.val.2).1 hs.2
      have heord := e.property
      have hh := (indexed_bounds S W D pi j).2.2
      change e.val.1.val < e.val.2.val at heord
      omega

noncomputable def freePairs (ys : Fin O → ℚ) (site : Fin O → Site S) :
    Finset (CoreEdge O × CoreEdge O) :=
  Finset.univ.filter (fun p => p.1 ∉ palette site ∧ p.2 ∉ palette site ∧
    edgeRank O p.1 < edgeRank O p.2 ∧ cross ys p.1.val.1 p.1.val.2 p.2.val.1 p.2.val.2)

noncomputable def mainPairs (ys : Fin O → ℚ) (site : Fin O → Site S) :
    Finset (CoreEdge O × CoreEdge O) :=
  (freePairs ys site).filter (fun p => ∃j k, j≠k ∧ selectedEdge site j p.1 ∧ selectedEdge site k p.2)

noncomputable def dummyPairs (ys : Fin O → ℚ) (site : Fin O → Site S) :
    Finset (CoreEdge O × CoreEdge O) :=
  (freePairs ys site).filter (fun p => dummyEdge site p.1 ∧ dummyEdge site p.2)


theorem cross_symm (ys : Fin O → ℚ) (e f : CoreEdge O) :
    cross ys e.val.1 e.val.2 f.val.1 f.val.2 ↔ cross ys f.val.1 f.val.2 e.val.1 e.val.2 :=
  properCross_swap_edges _ _ _ _

/-- All free crossing pairs are exactly local constraints, retained main
source constraints, and dummy internal constraints. The proof covers every
actual core edge in the indexed complete graph. -/
theorem free_pairs_decomposition (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) :
    let site := indexedSite S W D hW pi
    freePairs ys site = allLocalPairs ys site ∪ mainPairs ys site ∪ dummyPairs ys site := by
  dsimp only
  let site := indexedSite S W D hW pi
  ext p
  constructor
  · intro hp
    obtain ⟨hfe,hff,hr,hc⟩ := (Finset.mem_filter.mp hp).2
    have hcr := (cross_symm ys p.1 p.2).1 hc
    rcases (free_classification site p.1).1 hfe with hd|⟨j,hj⟩
    · rcases (free_classification site p.2).1 hff with hd'|⟨k,hk⟩
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hd,hd'⟩)
      · exact (dummy_no_local_cross S W D hW pi ys hy k p.2 p.1 hk hd hcr).elim
    · rcases (free_classification site p.2).1 hff with hd'|⟨k,hk⟩
      · exact (dummy_no_local_cross S W D hW pi ys hy j p.1 p.2 hj hd' hc).elim
      · by_cases hjk : j=k
        · subst k
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          apply Finset.mem_biUnion.mpr
          exact ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,hk,hr,hc⟩⟩
        · have hselj : selectedEdge site j p.1 := by
            rcases (local_split site j p.1).1 hj with hs|hs
            · have hh := indexed_short_cross_free_local S W D hW pi ys hy j p.1 p.2 hs hff hc
              exact (hjk (local_unique site j k p.2 hh hk)).elim
            · exact hs
          have hselk : selectedEdge site k p.2 := by
            rcases (local_split site k p.2).1 hk with hs|hs
            · have hh := indexed_short_cross_free_local S W D hW pi ys hy k p.2 p.1 hs hfe hcr
              exact (hjk (local_unique site j k p.1 hj hh)).elim
            · exact hs
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hp,j,k,hjk,hselj,hselk⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hp|hp
    · rcases Finset.mem_union.mp hp with hp|hp
      · obtain ⟨j,_,hp⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨he,hf,hr,hc⟩ := (Finset.mem_filter.mp hp).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,local_not_palette site j _ he,
          local_not_palette site j _ hf,hr,hc⟩
      · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1


theorem local_main_disjoint (ys : Fin O → ℚ) (site : Fin O → Site S) :
    Disjoint (allLocalPairs ys site) (mainPairs ys site) := by
  apply Finset.disjoint_left.mpr
  intro p hl hm
  obtain ⟨j,_,hl⟩ := Finset.mem_biUnion.mp hl
  have hl' := (Finset.mem_filter.mp hl).2
  obtain ⟨k,l,hkl,hk,hl⟩ := (Finset.mem_filter.mp hm).2
  have he := local_unique site j k p.1 hl'.1 ((local_split site k p.1).2 (Or.inr hk))
  have hf := local_unique site j l p.2 hl'.2.1 ((local_split site l p.2).2 (Or.inr hl))
  exact hkl (he.symm.trans hf)

theorem local_dummy_disjoint (ys : Fin O → ℚ) (site : Fin O → Site S) :
    Disjoint (allLocalPairs ys site) (dummyPairs ys site) := by
  apply Finset.disjoint_left.mpr
  intro p hl hd
  obtain ⟨j,_,hl⟩ := Finset.mem_biUnion.mp hl
  have hj := (Finset.mem_filter.mp hl).2.1
  exact dummy_not_local site p.1 j (Finset.mem_filter.mp hd).2.1 hj

theorem main_dummy_disjoint (ys : Fin O → ℚ) (site : Fin O → Site S) :
    Disjoint (mainPairs ys site) (dummyPairs ys site) := by
  apply Finset.disjoint_left.mpr
  intro p hm hd
  obtain ⟨j,k,_,hj,_⟩ := (Finset.mem_filter.mp hm).2
  exact dummy_not_local site p.1 j (Finset.mem_filter.mp hd).2.1
    ((local_split site j p.1).2 (Or.inr hj))

noncomputable def pairEnergy (pairs : Finset (CoreEdge O × CoreEdge O))
    (chi : CoreEdge O → Bool) : ℕ := ∑ p ∈ pairs, if chi p.1 = chi p.2 then 1 else 0

/-- An exact identity for every actual free-core coloring, using one and the
same coloring in all three terms; the dummy part has no source/short color. -/
theorem free_energy_decomposition (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys)
    (chi : CoreEdge (S*W+D+S*W) → Bool) :
    let site := indexedSite S W D hW pi
    pairEnergy (freePairs ys site) chi = pairEnergy (allLocalPairs ys site) chi +
      pairEnergy (mainPairs ys site) chi + pairEnergy (dummyPairs ys site) chi := by
  dsimp only
  let site := indexedSite S W D hW pi
  have hld := local_dummy_disjoint ys site
  have hmd := main_dummy_disjoint ys site
  have hu : Disjoint (allLocalPairs ys site ∪ mainPairs ys site) (dummyPairs ys site) :=
    Finset.disjoint_union_left.mpr ⟨hld,hmd⟩
  rw [free_pairs_decomposition S W D hW pi ys hy]
  unfold pairEnergy
  rw [Finset.sum_union hu,Finset.sum_union (local_main_disjoint ys site)]

end Q4.Candidate.CoreReducedPairs

#print axioms Q4.Candidate.CoreReducedPairs.dummy_no_local_cross
#print axioms Q4.Candidate.CoreReducedPairs.free_pairs_decomposition

#print axioms Q4.Candidate.CoreReducedPairs.local_main_disjoint
#print axioms Q4.Candidate.CoreReducedPairs.local_dummy_disjoint
#print axioms Q4.Candidate.CoreReducedPairs.main_dummy_disjoint
#print axioms Q4.Candidate.CoreReducedPairs.free_energy_decomposition
