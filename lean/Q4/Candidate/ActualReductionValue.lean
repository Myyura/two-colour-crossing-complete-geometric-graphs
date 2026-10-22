import Q4.Candidate.ComputedCore
import Q4.Candidate.ConvexBackground
import Q4.Candidate.FreezingErrors
import Q4.Candidate.MainSourceEncoding

/-! Actual full-drawing/core interval composition, with a directly executable
rational baseline. Finite minima are proved to exist and are used only inside
the analysis, never as inputs to the baseline evaluator. -/
namespace Q4.Candidate.ActualReductionValue
open Q4.Candidate.CompleteDrawing Q4.Candidate.ConvexSeparation
open Q4.Candidate.CompleteBackground Q4.Candidate.DoubleCapGrid
open Q4.Candidate.ProposedPalette Q4.Candidate.CoreLocalGeometry Q4.Candidate.CoreReducedPairs
open Q4.Candidate.ConvexBackground Q4.Candidate.FreezingParameters Q4.Candidate.FreezingErrors

variable {O B P S : ℕ}

def baseline (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (D : ℕ) : ℚ :=
  ComputedBackground.background ys ts rs (knownZ B)+
    ComputedCore.baseFloor ys ts rs site (ComputedBackground.fans ys ts rs)+knownZ D

theorem baseline_cast (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (site : Fin O → Site S) (D : ℕ) :
    (baseline ys ts rs site D:ℝ)=CompleteBackground.background ys ts rs (knownZ B)+
      CoreValueBridge.baseFloor ys ts rs site (frozenFans ys ts rs false)+(knownZ D:ℝ) := by
  simp only [baseline,Rat.cast_add,ComputedBackground.background_cast,ComputedCore.baseFloor_cast,
    ComputedBackground.fans_eq]

attribute [local instance] Classical.propDecidable

theorem finite_minimum {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ m, MinimumWitness f m := by
  obtain ⟨x,_,hx⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  exact ⟨f x,⟨fun y => hx y (Finset.mem_univ _),⟨x,rfl⟩⟩⟩

/-- Actual all-edge interval after substituting the actual core interval.
There is no assumed full or core optimum value, and K contains no minimum.
The main minimum is the source-encoding interface; the two convex certificates
are the explicitly external known result. -/
theorem combined_interval (S W D B P : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (M : ℕ) (base prototypes : Finset Point) (rs : Fin P → Point)
    (hw : ∀ k, CompleteFanFields.ProgramWitness (B:=B) ys M base prototypes (rs k))
    (hf : ∀ i, frame (frameParameter B i)∈base) (hybase : ∀ j, original (ys j)∈base)
    (hproto : ∀ q∈prototypes, phi q<0 ∧ |q.2|<2)
    (hO : 1000≤S*W+D+S*W) (hBO : S*W+D+S*W≤B)
    (hys : StrictMono ys) (hybox : ∀ j, |ys j|≤1)
    (a m R : ℝ) (ha : (P:ℝ)/(S*W+D+S*W)+GridCounts.rho B (S*W+D+S*W)≤a)
    (hsmall : a≤1/(2:ℝ)^4096)
    (hz1 : 104*a+CompleteProbeFreezing.outsideBudget (S*W+D+S*W) B P≤1/100)
    (hframe : ConvexOptimum B (knownZ B)) (hdummy : ConvexOptimum D (knownZ D))
    (hmain : MinimumWitness (fun chi =>
      (pairEnergy (mainPairs ys (indexedSite S W D hW pi)) chi:ℝ)) m)
    (hforce : ∀chi, (∀psi, coreValue ys (frameParameter B) rs
        (frozenFans ys (frameParameter B) rs false) chi≤coreValue ys (frameParameter B) rs
        (frozenFans ys (frameParameter B) rs false) psi) →
      ∀e∈palette (indexedSite S W D hW pi), chi e=paletteBit (indexedSite S W D hW pi) e)
    (hR0 : 0≤R)
    (hR : ∀e, CoreExtension.selected (indexedSite S W D hW pi) e →
      |CoreValueBridge.unary ys (frameParameter B) rs (indexedSite S W D hW pi)
        (frozenFans ys (frameParameter B) rs false) e true-
      CoreValueBridge.unary ys (frameParameter B) rs (indexedSite S W D hW pi)
        (frozenFans ys (frameParameter B) rs false) e false|≤R)
    (hd : ∀e, dummyEdge (indexedSite S W D hW pi) e →
      CoreValueBridge.unary ys (frameParameter B) rs (indexedSite S W D hW pi)
        (frozenFans ys (frameParameter B) rs false) e true=
      CoreValueBridge.unary ys (frameParameter B) rs (indexedSite S W D hW pi)
        (frozenFans ys (frameParameter B) rs false) e false)
    (chi : Edge (S*W+D+S*W) B P → Bool)
    (hmin : ∀psi, CompleteGridEnergy.energy ys (frameParameter B) rs chi≤
      CompleteGridEnergy.energy ys (frameParameter B) rs psi) :
    let K : ℝ := baseline ys (frameParameter B) rs (indexedSite S W D hW pi) D
    let N : ℝ := (B:ℝ)*(S*W+D+S*W)
    let eg : ℝ := 2^32*a^3*N^2
    let ef : ℝ := 2*(12*P/(S*W+D+S*W))*(104*a+
      CompleteProbeFreezing.outsideBudget (S*W+D+S*W) B P+GridCounts.rho B (S*W+D+S*W))*
      (104*a+CompleteProbeFreezing.outsideBudget (S*W+D+S*W) B P)*N^2
    let ey : ℝ := (Fintype.card (YEdge (S*W+D+S*W) P):ℝ)*
      ((B:ℝ)*P+Fintype.card (Inner (S*W+D+S*W)))+(Fintype.card (YEdge (S*W+D+S*W) P):ℝ)^2/2
    K+m-eg-ef≤CompleteGridEnergy.energy ys (frameParameter B) rs chi ∧
      CompleteGridEnergy.energy ys (frameParameter B) rs chi≤K+m+eg+ey+2*S*W^2*R+2*S*W^4 := by
  dsimp only
  obtain ⟨Mc,hMc⟩ := finite_minimum (coreValue ys (frameParameter B) rs (frozenFans ys (frameParameter B) rs false))
  have hfmin := frame_minimum ys (frameParameter B) rs (frameParameter_antitone B) (knownZ B) hframe
  have hdmin := dummy_minimum S W D hW pi ys hys (knownZ D) hdummy
  have hc := CoreValueBridge.actual_core_minimum_interval S W D B P hW pi ys hys (frameParameter B) rs
    (frozenFans ys (frameParameter B) rs false) m (knownZ D) R Mc hmain hdmin hMc hforce hR0 hR hd
  have hh := complete_minimum_interval ys M base prototypes rs hw hf hybase hproto hO hBO hys hybox
    a (knownZ B) Mc (by simpa only [Nat.cast_add,Nat.cast_mul] using ha) hsmall hz1 hfmin hMc chi hmin
  push_cast at hh
  rw [baseline_cast]
  constructor <;> linarith

attribute [local irreducible] scale originals frames a
set_option exponentiation.threshold 512

theorem actual_reduction_threshold (n q S W D B P : ℕ) (g t : ℤ)
    (hn : 1≤n) (hq : q=2^20*(n+1)) (hSdef : S=n*q)
    (hWdef : W=(scale S)^4) (hDdef : D=512*S*W) (hBdef : B=frames S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3)
    (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (ys : Fin (S*W+D+S*W) → ℚ) (M : ℕ) (base prototypes : Finset Point) (rs : Fin P → Point)
    (hw : ∀ k, CompleteFanFields.ProgramWitness (B:=B) ys M base prototypes (rs k))
    (hf : ∀ i, frame (frameParameter B i)∈base) (hybase : ∀ j, original (ys j)∈base)
    (hproto : ∀ q∈prototypes, phi q<0 ∧ |q.2|<2)
    (hys : StrictMono ys) (hybox : ∀ j, |ys j|≤1)
    (hframe : ConvexOptimum B (knownZ B)) (hdummy : ConvexOptimum D (knownZ D))
    (hmain : MinimumWitness (fun chi =>
      (pairEnergy (mainPairs ys (indexedSite S W D hW pi)) chi:ℝ)) ((q:ℝ)^2*(scale S:ℝ)^16*(g:ℝ)))
    (hforce : ∀chi, (∀psi, coreValue ys (frameParameter B) rs
        (frozenFans ys (frameParameter B) rs false) chi≤coreValue ys (frameParameter B) rs
        (frozenFans ys (frameParameter B) rs false) psi) →
      ∀e∈palette (indexedSite S W D hW pi), chi e=paletteBit (indexedSite S W D hW pi) e)
    (hR : ∀e, CoreExtension.selected (indexedSite S W D hW pi) e →
      |CoreValueBridge.unary ys (frameParameter B) rs (indexedSite S W D hW pi)
        (frozenFans ys (frameParameter B) rs false) e true-
      CoreValueBridge.unary ys (frameParameter B) rs (indexedSite S W D hW pi)
        (frozenFans ys (frameParameter B) rs false) e false|≤4*B)
    (hd : ∀e, dummyEdge (indexedSite S W D hW pi) e →
      CoreValueBridge.unary ys (frameParameter B) rs (indexedSite S W D hW pi)
        (frozenFans ys (frameParameter B) rs false) e true=
      CoreValueBridge.unary ys (frameParameter B) rs (indexedSite S W D hW pi)
        (frozenFans ys (frameParameter B) rs false) e false)
 :
    (∃chi : Edge (S*W+D+S*W) B P → Bool,
      CompleteGridEnergy.energy ys (frameParameter B) rs chi≤
        ((baseline ys (frameParameter B) rs (indexedSite S W D hW pi) D+
          (q:ℚ)^2*(scale S:ℚ)^16*t+(q:ℚ)^2*(scale S:ℚ)^16/4:ℚ):ℝ)) ↔ g≤t := by
  have hq0 : 0<q := by rw [hq]; positivity
  have hS : 1≤S := by rw [hSdef]; have hh := Nat.mul_pos (by omega : 0<n) hq0; omega
  have hOeq : S*W+D+S*W=originals S := by
    rw [hDdef,hWdef]
    unfold originals
    ring
  have hOr : (S:ℝ)*W+D+S*W=(originals S:ℝ) := by exact_mod_cast hOeq
  have hb := actual_bounds S P hS hP
  have hO : 1000≤S*W+D+S*W := by rw [hOeq]; exact hb.1
  have hBO : S*W+D+S*W≤B := by rw [hOeq,hBdef]; exact hb.2.1
  have ha := hb.2.2.2.1
  rw [←hOeq,←hBdef] at ha
  push_cast at ha
  have hz1 := hb.2.2.2.2.2.2.2.2
  rw [←hOeq,←hBdef] at hz1
  let K : ℚ := baseline ys (frameParameter B) rs (indexedSite S W D hW pi) D
  let Δ : ℝ := (q:ℝ)^2*(scale S:ℝ)^16
  let em : ℝ := gridError S+freezingError S P
  let ep : ℝ := gridError S+yError S P+10*S*(scale S:ℝ)^13+2*S*(scale S:ℝ)^16
  obtain ⟨v,hv⟩ := finite_minimum (CompleteGridEnergy.energy ys (frameParameter B) rs)
  obtain ⟨chi,hchi⟩ := hv.attained
  have hmin : ∀psi, CompleteGridEnergy.energy ys (frameParameter B) rs chi≤
      CompleteGridEnergy.energy ys (frameParameter B) rs psi := by
    intro psi; rw [hchi]; exact hv.lower psi
  have hh := combined_interval S W D B P hW pi ys M base prototypes rs hw hf hybase hproto
    hO hBO hys hybox (a S) (Δ*(g:ℝ)) (4*B) ha hb.2.2.2.2.1 hz1 hframe hdummy hmain
    hforce (by positivity) hR hd chi hmin
  dsimp only at hh
  have heg : 2^32*(a S)^3*((B:ℝ)*(S*W+D+S*W))^2=gridError S := by
    rw [hOr,hBdef]
    unfold gridError
    ring
  have hef : 2*(12*P/((S:ℝ)*W+D+S*W))*(104*a S+
      CompleteProbeFreezing.outsideBudget (S*W+D+S*W) B P+GridCounts.rho B (S*W+D+S*W))*
      (104*a S+CompleteProbeFreezing.outsideBudget (S*W+D+S*W) B P)*
      ((B:ℝ)*(S*W+D+S*W))^2=freezingError S P := by
    rw [hOr,hOeq,hBdef]
    rfl
  have hey : (Fintype.card (YEdge (S*W+D+S*W) P):ℝ)*
      ((B:ℝ)*P+Fintype.card (Inner (S*W+D+S*W)))+
      (Fintype.card (YEdge (S*W+D+S*W) P):ℝ)^2/2=yError S P := by
    rw [hOeq,hBdef]
    rfl
  have hu : 2*(S:ℝ)*W^2*(4*B)≤10*S*(scale S:ℝ)^13 := by
    rw [hWdef,hBdef]
    simp only [frames,Nat.cast_pow]
    have he : 2*(S:ℝ)*((scale S:ℝ)^4)^2*(4*(scale S:ℝ)^5)=8*S*(scale S:ℝ)^13 := by ring
    rw [he]
    have hp : 0≤(S:ℝ)*(scale S:ℝ)^13 := mul_nonneg (Nat.cast_nonneg S) (pow_nonneg (Nat.cast_nonneg _) _)
    nlinarith
  have hl : 2*(S:ℝ)*W^4=2*S*(scale S:ℝ)^16 := by
    rw [hWdef]
    push_cast
    ring
  rw [heg,hef,hey,hl,hchi] at hh
  have hlo : (K:ℝ)+Δ*(g:ℝ)-em≤v := by dsimp only [K,em]; linarith [hh.1]
  have hhi : v≤(K:ℝ)+Δ*(g:ℝ)+ep := by dsimp only [K,ep]; linarith [hh.2]
  have hscale : (0:ℝ)<scale S := by exact_mod_cast scale_positive S
  have hDelta : 0<Δ := mul_pos (pow_pos (by exact_mod_cast hq0) _) (pow_pos hscale _)
  have ha0 : 0≤a S := by unfold a alpha; positivity
  have hbeta0 := CompleteProbeFreezing.outsideBudget_nonneg (O:=originals S) (B:=frames S) (P:=P)
  have hrho0 := GridCounts.rho_nonneg (frames S) (originals S)
  have heg0 : 0≤gridError S := by unfold gridError; positivity
  have hef0 : 0≤freezingError S P := by unfold freezingError; positivity
  have hey0 : 0≤yError S P := by unfold yError; positivity
  have hem : 0≤em := add_nonneg heg0 hef0
  have hep : 0≤ep := by dsimp only [ep]; positivity
  have hwnd := actual_conservative_signal_window n q P hn hq (by simpa only [←hSdef] using hP)
  have hwnd' : (2:ℝ)^18*(em+ep)<Δ := by
    dsimp only [em,ep,Δ]
    rw [←hSdef] at hwnd
    convert hwnd using 1; ring
  have hquarter := ConservativeGap.quarter_gap Δ (em+ep) hDelta hwnd'
  have hiff := ReductionGap.threshold_equivalence g t K Δ (Δ/4) v em ep hDelta
    (by ring) hem hep hquarter hlo hhi
  have hcast : ((K+(q:ℚ)^2*(scale S:ℚ)^16*t+(q:ℚ)^2*(scale S:ℚ)^16/4:ℚ):ℝ)=
      (K:ℝ)+Δ*(t:ℝ)+Δ/4 := by push_cast; rfl
  change (∃psi, CompleteGridEnergy.energy ys (frameParameter B) rs psi≤
    ((K+(q:ℚ)^2*(scale S:ℚ)^16*t+(q:ℚ)^2*(scale S:ℚ)^16/4:ℚ):ℝ)) ↔ _
  rw [hcast]
  constructor
  · rintro ⟨psi,hpsi⟩
    exact hiff.mp ((hv.lower psi).trans hpsi)
  · intro hgt
    exact ⟨chi,by rw [hchi]; exact hiff.mpr hgt⟩

#print axioms finite_minimum
#print axioms combined_interval
#print axioms actual_reduction_threshold


/-- The standard integer query threshold is just the rational floor. This
bridge also covers negative thresholds without truncation to natural zero. -/
theorem nat_floor_iff (k : ℕ) (r : ℚ) : (k:ℤ)≤⌊r⌋ ↔ (k:ℝ)≤(r:ℝ) := by
  rw [Int.le_floor]
  have hh : (((k:ℤ):ℚ):ℝ)≤(r:ℝ) ↔ ((k:ℤ):ℚ)≤r := Rat.cast_le
  simpa only [Int.cast_natCast,Rat.cast_natCast] using hh.symm

theorem integer_threshold_iff (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) (r : ℚ) :
    (∃chi : Edge O B P → Bool, (Q4.monoCount (CompleteGridEnergy.crossingPairs ys ts rs).toList chi:ℤ)≤⌊r⌋) ↔
    (∃chi : Edge O B P → Bool, CompleteGridEnergy.energy ys ts rs chi≤(r:ℝ)) := by
  simp only [nat_floor_iff,CompleteGridEnergy.energy]

/-- The main certificate is now obtained from the actual source endpoint
layout, with free colours on every selected copy and every remaining core edge. -/
theorem source_main_minimum (n q D W B : ℕ) (hW : 2≤W) (pi : Equiv.Perm (Fin n)) :
    MinimumWitness (fun chi => (pairEnergy
      (mainPairs (OriginalVertexLayout.parameter n q D W B)
        (indexedSite (n*q) W D (by omega) (OriginalVertexLayout.sitePermutation pi))) chi:ℝ))
      ((q:ℝ)^2*(W:ℝ)^4*(CoreEncoding.sourceOpt (SourceSelectedEdges.sourcePairs pi).toList:ℝ)) := by
  have hh := MainSourceEncoding.actual_main_minimum (q:=q) D B hW pi
  constructor
  · intro chi
    exact_mod_cast hh.1 chi
  · obtain ⟨chi,hchi⟩ := hh.2
    exact ⟨chi,by exact_mod_cast hchi⟩

theorem actual_source_threshold (n q W D B P : ℕ) (t : ℤ)
    (hn : 1≤n) (hq : q=2^20*(n+1))
    (hWdef : W=(scale (n*q))^4) (hDdef : D=512*(n*q)*W) (hBdef : B=frames (n*q))
    (hP : (P:ℝ)≤(2:ℝ)^80*(((n*q):ℝ)+1)^4*(scale (n*q):ℝ)^3)
    (hW2 : 2≤W) (pi : Equiv.Perm (Fin n))
    (M : ℕ) (base prototypes : Finset Point) (rs : Fin P → Point)
    (hw : ∀ k, CompleteFanFields.ProgramWitness (B:=B) (OriginalVertexLayout.parameter n q D W B) M base prototypes (rs k))
    (hf : ∀ i, frame (frameParameter B i)∈base) (hybase : ∀ j, original ((OriginalVertexLayout.parameter n q D W B) j)∈base)
    (hproto : ∀ q∈prototypes, phi q<0 ∧ |q.2|<2)
    (hframe : ConvexOptimum B (knownZ B)) (hdummy : ConvexOptimum D (knownZ D))
    (hforce : ∀chi, (∀psi, coreValue (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs
        (frozenFans (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs false) chi≤coreValue (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs
        (frozenFans (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs false) psi) →
      ∀e∈palette (indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi)), chi e=paletteBit (indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi)) e)
    (hR : ∀e, CoreExtension.selected (indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi)) e →
      |CoreValueBridge.unary (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs (indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi))
        (frozenFans (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs false) e true-
      CoreValueBridge.unary (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs (indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi))
        (frozenFans (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs false) e false|≤4*B)
    (hd : ∀e, dummyEdge (indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi)) e →
      CoreValueBridge.unary (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs (indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi))
        (frozenFans (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs false) e true=
      CoreValueBridge.unary (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs (indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi))
        (frozenFans (OriginalVertexLayout.parameter n q D W B) (frameParameter B) rs false) e false)
 :
    let ys := OriginalVertexLayout.parameter n q D W B
    let site := indexedSite (n*q) W D (show 0<W by omega) (OriginalVertexLayout.sitePermutation pi)
    let r : ℚ := baseline ys (frameParameter B) rs site D+
      (q:ℚ)^2*(scale (n*q):ℚ)^16*t+(q:ℚ)^2*(scale (n*q):ℚ)^16/4
    (∃chi : Edge (n*q*W+D+n*q*W) B P → Bool,
      (Q4.monoCount (CompleteGridEnergy.crossingPairs ys (frameParameter B) rs).toList chi:ℤ)≤⌊r⌋) ↔
      (CoreEncoding.sourceOpt (SourceSelectedEdges.sourcePairs pi).toList:ℤ)≤t := by
  dsimp only
  rw [integer_threshold_iff]
  have hm := source_main_minimum n q D W B hW2 pi
  have hpow : (W:ℝ)^4=(scale (n*q):ℝ)^16 := by rw [hWdef]; push_cast; ring
  rw [hpow] at hm
  exact actual_reduction_threshold n q (n*q) W D B P
    (CoreEncoding.sourceOpt (SourceSelectedEdges.sourcePairs pi).toList:ℤ) t
    hn hq rfl hWdef hDdef hBdef (by simpa only [Nat.cast_mul] using hP) (by omega) (OriginalVertexLayout.sitePermutation pi)
    (OriginalVertexLayout.parameter n q D W B) M base prototypes rs hw hf hybase hproto
    (OriginalVertexLayout.parameter_strictMono n q D W B hW2)
    (fun j => OriginalVertexLayout.parameter_abs n q D W B hW2 j)
    hframe hdummy (by simpa only [Int.cast_natCast] using hm) hforce hR hd

#print axioms integer_threshold_iff
#print axioms source_main_minimum
#print axioms actual_source_threshold

end Q4.Candidate.ActualReductionValue
