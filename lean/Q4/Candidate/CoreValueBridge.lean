import Q4.Candidate.CoreExtension

/-! Connect the exhaustive original-core decomposition to the actual frozen
core objective used in the complete-graph background theorem. -/
namespace Q4.Candidate.CoreValueBridge
open Q4.Candidate.ProposedPalette Q4.Candidate.PaletteCounting
open Q4.Candidate.CoreLocalGeometry Q4.Candidate.CoreReducedPairs
open Q4.Candidate.CoreFixedPalette Q4.Candidate.CompleteDrawing
open Q4.Candidate.CompleteBackground Q4.Candidate.CoreExtension
open Q4.Candidate.ConvexSeparation
attribute [local instance] Classical.propDecidable
variable {O B P S : ℕ}

def reference (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) : Edge O B P → Bool :=
  assemble (fun _ => false) tau (paletteBit site) (fun _ => false) (fun _ => false)

noncomputable def baseline (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) : ℝ :=
  paletteBaseline ys ts rs site (reference site tau)

noncomputable def unary (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) (e : CoreEdge O) (bit : Bool) : ℝ :=
  freeUnary ys ts rs site (reference site tau) e bit

/-- Every fixed-palette actual C coloring has exactly the explicit restored
value. Thus later minimization refers to the original C/CT costs. -/
theorem actual_core_decomposition (S W D B P : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (tau : Fin B×Fin P → Bool) (chi : CoreEdge (S*W+D+S*W) → Bool)
    (hp : ∀e∈palette (indexedSite S W D hW pi), chi e=paletteBit (indexedSite S W D hW pi) e) :
    let site := indexedSite S W D hW pi
    coreValue ys ts rs tau chi = restoredValue ys site (baseline ys ts rs site tau)
      (unary ys ts rs site tau) chi := by
  dsimp only
  let site := indexedSite S W D hW pi
  let psi := assemble (fun _ => false) tau chi (fun _ => false) (fun _ => false)
  have hh := indexed_full_core_decomposition S W D B P hW pi ys hy ts rs psi hp
  have hb : paletteBaseline ys ts rs site psi=baseline ys ts rs site tau := by
    apply paletteBaseline_congr
    · exact hp
    · intro t; rfl
  have hu (e : CoreEdge (S*W+D+S*W)) (b : Bool) :
      freeUnary ys ts rs site psi e b=unary ys ts rs site tau e b := by
    apply freeUnary_congr_T
    intro t; rfl
  change coreValue ys ts rs tau chi=paletteBaseline ys ts rs site psi+
    (pairEnergy (allLocalPairs ys site) chi:ℝ)+(pairEnergy (mainPairs ys site) chi:ℝ)+
    (pairEnergy (dummyPairs ys site) chi:ℝ)+
    ∑e, if e∉palette site then freeUnary ys ts rs site psi e (chi e) else 0 at hh
  simp_rw [hb,hu] at hh
  exact hh

/-- The core baseline is the directly evaluated palette constant plus all
binary unary floors. Neither the main nor dummy optimization is hidden here. -/
noncomputable def baseFloor (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (tau : Fin B×Fin P → Bool) : ℝ :=
  baseline ys ts rs site tau+CoreExtension.unaryFloor site (unary ys ts rs site tau)

theorem actual_core_lower (S W D B P : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (tau : Fin B×Fin P → Bool) (m z : ℝ)
    (hm : ∀chi, m≤(pairEnergy (mainPairs ys (indexedSite S W D hW pi)) chi:ℝ))
    (hz : ∀chi, z≤(pairEnergy (dummyPairs ys (indexedSite S W D hW pi)) chi:ℝ))
    (chi : CoreEdge (S*W+D+S*W) → Bool)
    (hp : ∀e∈palette (indexedSite S W D hW pi), chi e=paletteBit (indexedSite S W D hW pi) e) :
    baseFloor ys ts rs (indexedSite S W D hW pi) tau+m+z≤coreValue ys ts rs tau chi := by
  rw [actual_core_decomposition S W D B P hW pi ys hy ts rs tau chi hp]
  exact restored_lower ys _ _ m z _ hm hz chi

theorem actual_core_upper (S W D B P : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (tau : Fin B×Fin P → Bool) (m z R : ℝ)
    (hm : ∃chi, (pairEnergy (mainPairs ys (indexedSite S W D hW pi)) chi:ℝ)=m)
    (hz : ∃chi, (pairEnergy (dummyPairs ys (indexedSite S W D hW pi)) chi:ℝ)=z)
    (hR0 : 0≤R)
    (hR : ∀e, selected (indexedSite S W D hW pi) e →
      |unary ys ts rs (indexedSite S W D hW pi) tau e true-
        unary ys ts rs (indexedSite S W D hW pi) tau e false|≤R)
    (hd : ∀e, dummyEdge (indexedSite S W D hW pi) e →
      unary ys ts rs (indexedSite S W D hW pi) tau e true=
        unary ys ts rs (indexedSite S W D hW pi) tau e false) :
    ∃chi, coreValue ys ts rs tau chi≤
      baseFloor ys ts rs (indexedSite S W D hW pi) tau+m+z+2*S*W^2*R+2*S*W^4 := by
  obtain ⟨chi,hp,hu⟩ := restored_upper S W D hW pi ys
    (baseline ys ts rs _ tau) m z R (unary ys ts rs _ tau) hm hz hR0 hR hd
  refine ⟨chi,?_⟩
  rw [actual_core_decomposition S W D B P hW pi ys hy ts rs tau chi hp]
  exact hu

/-- Once palette forcing and actual main/dummy minima are supplied, the
free minimum of the original full C objective lies in this explicit interval.
The minimum Mc occurs only as the quantity being bounded, never in baseFloor. -/
theorem actual_core_minimum_interval (S W D B P : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (tau : Fin B×Fin P → Bool) (m z R Mc : ℝ)
    (hm : MinimumWitness (fun chi => (pairEnergy (mainPairs ys (indexedSite S W D hW pi)) chi:ℝ)) m)
    (hz : MinimumWitness (fun chi => (pairEnergy (dummyPairs ys (indexedSite S W D hW pi)) chi:ℝ)) z)
    (hMc : MinimumWitness (coreValue ys ts rs tau) Mc)
    (hforce : ∀chi, (∀psi, coreValue ys ts rs tau chi≤coreValue ys ts rs tau psi) →
      ∀e∈palette (indexedSite S W D hW pi), chi e=paletteBit (indexedSite S W D hW pi) e)
    (hR0 : 0≤R)
    (hR : ∀e, selected (indexedSite S W D hW pi) e →
      |unary ys ts rs (indexedSite S W D hW pi) tau e true-
        unary ys ts rs (indexedSite S W D hW pi) tau e false|≤R)
    (hd : ∀e, dummyEdge (indexedSite S W D hW pi) e →
      unary ys ts rs (indexedSite S W D hW pi) tau e true=
        unary ys ts rs (indexedSite S W D hW pi) tau e false) :
    baseFloor ys ts rs (indexedSite S W D hW pi) tau+m+z≤Mc ∧
      Mc≤baseFloor ys ts rs (indexedSite S W D hW pi) tau+m+z+2*S*W^2*R+2*S*W^4 := by
  constructor
  · obtain ⟨chi,hchi⟩ := hMc.attained
    have hf := hforce chi (by intro psi; rw [hchi]; exact hMc.lower psi)
    have hl := actual_core_lower S W D B P hW pi ys hy ts rs tau m z hm.lower hz.lower chi hf
    rwa [hchi] at hl
  · obtain ⟨chi,hu⟩ := actual_core_upper S W D B P hW pi ys hy ts rs tau m z R
      hm.attained hz.attained hR0 hR hd
    exact (hMc.lower chi).trans hu

end Q4.Candidate.CoreValueBridge
#print axioms Q4.Candidate.CoreValueBridge.actual_core_decomposition
#print axioms Q4.Candidate.CoreValueBridge.actual_core_lower
#print axioms Q4.Candidate.CoreValueBridge.actual_core_upper
#print axioms Q4.Candidate.CoreValueBridge.actual_core_minimum_interval
