import Q4.Candidate.CompleteFanFields
import Q4.Candidate.ProgramCount
import Q4.Candidate.ReductionGap

/-! Explicit scale closure for the actual complete drawing. In particular the
outside-degree budget includes Y, not just the Y-deleted auxiliary graph. -/
namespace Q4.Candidate.FreezingParameters
set_option exponentiation.threshold 4200

noncomputable def alpha (d H : ℝ) : ℝ := (2:ℝ)^84*d^4/H

theorem actual_large (d : ℝ) (hd : 1≤d) :
    (2:ℝ)^4200*d^4 ≤ (2:ℝ)^20000*d^40 := by
  exact mul_le_mul
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 4200≤20000))
    (pow_le_pow_right₀ hd (by omega : 4≤40)) (by positivity) (by positivity)

theorem alpha_small (d H : ℝ) (hd : 1≤d)
    (hH : (2:ℝ)^4200*d^4≤H) :
    0<alpha d H ∧ 2*alpha d H≤1/(2:ℝ)^4096 := by
  have hd0 : 0<d := by linarith
  have hH0 : 0<H := lt_of_lt_of_le (by positivity) hH
  refine ⟨by unfold alpha; positivity,?_⟩
  unfold alpha
  rw [←mul_div_assoc]
  apply (div_le_iff₀ hH0).2
  have hp := mul_le_mul_of_nonneg_left hH (by positivity : (0:ℝ)≤1/(2:ℝ)^4096)
  have hc : 2*(2:ℝ)^84 ≤ (1/(2:ℝ)^4096)*(2:ℝ)^4200 := by norm_num
  have hc' := mul_le_mul_of_nonneg_right hc (pow_nonneg (le_of_lt hd0) 4)
  nlinarith only [hp,hc']

theorem program_scale_bound (S H P : ℝ) (hS : 1≤S) (hH : 1≤H)
    (hP : P≤16*S*((2:ℝ)^26*(S+1)*(514*S*H^4)^2)/H^5+
      8*S*(514*S*H^4)*H^4/H^5+10*S) :
    P≤(2:ℝ)^80*(S+1)^4*H^3 := by
  have hH0 : H≠0 := ne_of_gt (by linarith : 0<H)
  have hS0 : 0≤S := by linarith
  have hd : 1≤S+1 := by linarith
  have hS3 : S^3≤(S+1)^3 := pow_le_pow_left₀ hS0 (by linarith) 3
  have hS2 : S^2≤(S+1)^4 := le_trans
    (pow_le_pow_left₀ hS0 (by linarith : S≤S+1) 2)
    (pow_le_pow_right₀ hd (by omega : 2≤4))
  have hSd : S≤(S+1)^4 := le_trans (by linarith : S≤S+1)
    (by simpa using pow_le_pow_right₀ hd (by omega : 1≤4))
  have hH3 : 1≤H^3 := one_le_pow₀ hH
  have h1 := mul_le_mul_of_nonneg_right hS3 (by positivity : (0:ℝ)≤S+1)
  have h2 := mul_le_mul_of_nonneg_right hS2 (by positivity : (0:ℝ)≤H^3)
  have h3 := mul_le_mul_of_nonneg_left hH3 (pow_nonneg (by linarith : 0≤S+1) 4)
  have h1' : S^3*(S+1)*H^3≤(S+1)^4*H^3 := by
    convert mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ)≤H^3) using 1
    ring
  have he : 16*S*((2:ℝ)^26*(S+1)*(514*S*H^4)^2)/H^5+
      8*S*(514*S*H^4)*H^4/H^5+10*S =
      (16*2^26*514^2)*(S^3*(S+1)*H^3)+4112*(S^2*H^3)+10*S := by
    field_simp
    ring
  rw [he] at hP
  norm_num at hP ⊢
  nlinarith only [hP,h1',h2,h3,hSd]

theorem scalar_bounds (S H P : ℝ) (hS : 1≤S) (hP0 : 0≤P)
    (hH : (2:ℝ)^4200*(S+1)^4≤H)
    (hP : P≤(2:ℝ)^80*(S+1)^4*H^3) :
    let O := 514*S*H^4
    let B := H^5
    let a := 2*alpha (S+1) H
    let beta := (B*P+(O+P)^2/2)/(B*O)
    1000≤O ∧ O≤B ∧ P≤O ∧
    P/O+(1/B+1/O)≤a ∧ a≤1/(2:ℝ)^4096 ∧
    beta≤alpha (S+1) H ∧ 12*P/O≤alpha (S+1) H ∧
    1/B+1/O≤alpha (S+1) H ∧ 104*a+beta≤1/100 := by
  dsimp only
  have hS0 : 0<S := by linarith
  have hd : 1≤S+1 := by linarith
  have hd4 : 1≤(S+1)^4 := one_le_pow₀ hd
  have hSd : S≤(S+1)^4 := le_trans (by linarith : S≤S+1)
    (by simpa using pow_le_pow_right₀ hd (by omega : 1≤4))
  have hc : (2:ℝ)^4200 ≥ 1024 := by norm_num
  have hH2 : 2≤H := by nlinarith only [hH,hd4,hc]
  have hH1 : 1≤H := by linarith
  have hH0 : 0<H := by linarith
  have hHn : H≠0 := ne_of_gt hH0
  have hO0 : 0<514*S*H^4 := by positivity
  have hOn : 514*S*H^4≠0 := ne_of_gt hO0
  have hB0 : 0<H^5 := by positivity
  have hbase : 514*S≤H := by nlinarith only [hH,hSd,hc,hd4]
  have hOB : 514*S*H^4≤H^5 := by
    convert mul_le_mul_of_nonneg_right hbase (by positivity : (0:ℝ)≤H^4) using 1
    ring
  have hO1000 : 1000≤514*S*H^4 := by
    have hh : (2:ℝ)^4≤H^4 := pow_le_pow_left₀ (by norm_num) hH2 4
    nlinarith
  have hH4O : H^4≤514*S*H^4 := by nlinarith [pow_nonneg (le_of_lt hH0) 4]
  let m : ℝ := (2:ℝ)^80*(S+1)^4/H
  have hm0 : 0≤m := by dsimp [m]; positivity
  have ham : alpha (S+1) H=16*m := by dsimp [alpha,m]; norm_num; ring
  have hpfrac : P/(514*S*H^4)≤m := by
    calc
      _ ≤ P/H^4 := div_le_div_of_nonneg_left hP0 (by positivity) hH4O
      _ ≤ ((2:ℝ)^80*(S+1)^4*H^3)/H^4 := div_le_div_of_nonneg_right hP (by positivity)
      _ = m := by dsimp [m]; field_simp
  have hoB : (514*S*H^4)/H^5≤m := by
    have hh : 514*S≤(2:ℝ)^80*(S+1)^4 := by
      have hc80 : (514:ℝ)≤2^80 := by norm_num
      nlinarith only [hSd,hc80,hd4]
    calc
      _ = 514*S/H := by field_simp
      _ ≤ m := div_le_div_of_nonneg_right hh (le_of_lt hH0)
  have hasmall := alpha_small (S+1) H hd hH
  have halpha1 : alpha (S+1) H≤1 := by
    have hc4096 : (1:ℝ)/(2:ℝ)^4096≤1 := by norm_num
    linarith [hasmall.2]
  have hpO : P≤514*S*H^4 := by
    have hh : P/(514*S*H^4)≤1 := by rw [ham] at halpha1; linarith
    exact (div_le_one hO0).mp hh
  have hbeta : (H^5*P+(514*S*H^4+P)^2/2)/(H^5*(514*S*H^4))≤3*m := by
    calc
      _ ≤ (H^5*P+2*(514*S*H^4)^2)/(H^5*(514*S*H^4)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg (514*S*H^4-P)]
      _ = P/(514*S*H^4)+2*((514*S*H^4)/H^5) := by field_simp
      _ ≤ 3*m := by linarith
  have hmesh : 1/H^5+1/(514*S*H^4)≤m := by
    have hHH4 : H≤H^4 := by simpa using pow_le_pow_right₀ hH1 (by omega : 1≤4)
    have hHH5 : H≤H^5 := by simpa using pow_le_pow_right₀ hH1 (by omega : 1≤5)
    have h1 : 1/H^5≤1/H := one_div_le_one_div_of_le hH0 hHH5
    have h2 : 1/(514*S*H^4)≤1/H := one_div_le_one_div_of_le hH0 (hHH4.trans hH4O)
    have htwo : (2:ℝ)≤2^80*(S+1)^4 := by
      have hc80 : (2:ℝ)≤2^80 := by norm_num
      nlinarith only [hd4,hc80]
    have h3 : 2/H≤m := div_le_div_of_nonneg_right htwo (le_of_lt hH0)
    simp only [div_eq_mul_inv,one_mul] at h1 h2 h3 ⊢
    linarith
  refine ⟨hO1000,hOB,hpO,?_,hasmall.2,?_,?_,?_,?_⟩
  · rw [ham]; linarith
  · rw [ham]; linarith
  · rw [ham,mul_div_assoc]; linarith
  · rw [ham]; linarith
  · have htiny : (1:ℝ)/(2:ℝ)^4096≤1/100000 := by norm_num
    rw [ham] at hasmall
    rw [ham]
    nlinarith only [hasmall.2,htiny,hbeta]

def scale (S : ℕ) : ℕ := 2^20000*(S+1)^40
def originals (S : ℕ) : ℕ := 514*S*(scale S)^4
def frames (S : ℕ) : ℕ := (scale S)^5
noncomputable def a (S : ℕ) : ℝ := 2*alpha ((S:ℝ)+1) (scale S)

theorem actual_bounds (S P : ℕ) (hS : 1≤S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3) :
    1000≤originals S ∧ originals S≤frames S ∧ P≤originals S ∧
    (P:ℝ)/originals S+GridCounts.rho (frames S) (originals S)≤a S ∧
    a S≤1/(2:ℝ)^4096 ∧
    CompleteProbeFreezing.outsideBudget (originals S) (frames S) P≤alpha ((S:ℝ)+1) (scale S) ∧
    12*P/(originals S:ℝ)≤alpha ((S:ℝ)+1) (scale S) ∧
    GridCounts.rho (frames S) (originals S)≤alpha ((S:ℝ)+1) (scale S) ∧
    104*a S+CompleteProbeFreezing.outsideBudget (originals S) (frames S) P≤1/100 := by
  have hSr : (1:ℝ)≤S := by exact_mod_cast hS
  have hH : (2:ℝ)^4200*((S:ℝ)+1)^4≤(scale S:ℝ) := by
    simp only [scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    exact actual_large ((S:ℝ)+1) (by linarith)
  have h := scalar_bounds S (scale S) P hSr (Nat.cast_nonneg P) hH hP
  dsimp only at h
  rcases h with ⟨hO,hOB,hPO,ha,hs,hb,hQ,hr,hz⟩
  have hOeq : (originals S:ℝ)=514*S*(scale S:ℝ)^4 := by
    simp only [originals,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hBeq : (frames S:ℝ)=(scale S:ℝ)^5 := by simp only [frames,Nat.cast_pow]
  simp only [←hOeq,←hBeq] at hO hOB hPO ha hb hQ hr hz
  refine ⟨by exact_mod_cast hO,by exact_mod_cast hOB,by exact_mod_cast hPO,ha,hs,hb,hQ,hr,hz⟩

/-- The actual complete-graph freezing statement with all scale hypotheses
discharged by the manuscript's explicit integer H,O,B. Only the constructed
catalog size and actual ordinary/rank placement witnesses remain as inputs. -/
theorem actual_complete_freezing (S P : ℕ) (hS : 1≤S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3)
    (ys : Fin (originals S) → ℚ) (M : Nat)
    (base prototypes : Finset Q4.Candidate.ConvexSeparation.Point)
    (rs : Fin P → Q4.Candidate.ConvexSeparation.Point)
    (hw : ∀ k, CompleteFanFields.ProgramWitness (B:=frames S) ys M base prototypes (rs k))
    (hf : ∀ i, Q4.Candidate.ConvexSeparation.frame (Q4.Candidate.DoubleCapGrid.frameParameter (frames S) i) ∈ base)
    (hy : ∀ j, Q4.Candidate.ConvexSeparation.original (ys j) ∈ base)
    (hproto : ∀ q ∈ prototypes, Q4.Candidate.ConvexSeparation.phi q < 0 ∧ |q.2| < 2)
    (hys : StrictMono ys) (hybox : ∀ j, |ys j|≤1)
    (χ : CompleteDrawing.Edge (originals S) (frames S) P → Bool)
    (hmin : ∀ ζ, CompleteGridEnergy.energy ys (Q4.Candidate.DoubleCapGrid.frameParameter (frames S)) rs χ ≤
      CompleteGridEnergy.energy ys (Q4.Candidate.DoubleCapGrid.frameParameter (frames S)) rs ζ) :
    ∃ b : Bool, ∃ ψ : CompleteDrawing.Edge (originals S) (frames S) P → Bool,
      (∀ t : Fin (frames S) × Fin P, ψ (.inr (.inl t)) =
        CompleteProbeFreezing.frozenColor ys (Q4.Candidate.DoubleCapGrid.frameParameter (frames S)) rs b (.inr (.inl t))) ∧
      (∀ e, (∀ t : Fin (frames S) × Fin P, e ≠ .inr (.inl t)) → ψ e = χ e) ∧
      (∀ x : Fin (frames S) × Fin (originals S), ψ (.inl x) = χ (.inl x)) ∧
      0 ≤ CompleteGridEnergy.energy ys (Q4.Candidate.DoubleCapGrid.frameParameter (frames S)) rs ψ-
        CompleteGridEnergy.energy ys (Q4.Candidate.DoubleCapGrid.frameParameter (frames S)) rs χ ∧
      CompleteGridEnergy.energy ys (Q4.Candidate.DoubleCapGrid.frameParameter (frames S)) rs ψ-
        CompleteGridEnergy.energy ys (Q4.Candidate.DoubleCapGrid.frameParameter (frames S)) rs χ ≤
        2*(12*P/(originals S:ℝ))*(104*a S+CompleteProbeFreezing.outsideBudget (originals S) (frames S) P+
          GridCounts.rho (frames S) (originals S))*
          (104*a S+CompleteProbeFreezing.outsideBudget (originals S) (frames S) P)*
          ((frames S:ℝ)*originals S)^2 := by
  obtain ⟨hO,hOB,_,ha,hs,_,_,_,hz⟩ := actual_bounds S P hS hP
  exact CompleteFanFields.complete_freezing_from_program_geometry ys M base prototypes rs hw hf hy hproto
    hO hOB hys hybox (a S) ha hs hz χ hmin

/-- The second bound of (5.16) for the actual four-family catalog. No total
program count is an input. The recipe's target and response-weight bounds are
the geometric/core obligations; all ceil and greedy counts are derived. -/
theorem catalog_scale_bound {S : ℕ} (d : ProgramCount.Recipe S) (gaps : ℕ) (hS : 1≤S)
    (hA : d.A=(2:ℚ)^26*((S:ℚ)+1)*(originals S:ℚ)^2)
    (hg : gaps≤(scale S)^4)
    (htL : ∀ j, 0≤d.A+j.val*d.T-d.offset j ∧ d.A+j.val*d.T-d.offset j≤2*d.A)
    (htR : ∀ j : Fin S, 0≤d.A+j.val*d.T ∧ d.A+j.val*d.T≤2*d.A)
    (huL : ∀ j, (frames S:ℚ)/4≤d.ordinaryLeftWeight j)
    (huR : ∀ j, (frames S:ℚ)/4≤d.ordinaryRightWeight j)
    (hsL : ∀ j, d.leftSlope j≤originals S) (hsR : ∀ j, d.rightSlope j≤originals S)
    (hwL : ∀ j i, i<gaps → 0<d.leftWeight j i ∧ d.leftWeight j i≤frames S ∧ frames S≤4*d.leftWeight j i)
    (hwR : ∀ j i, i<gaps → 0<d.rightWeight j i ∧ d.rightWeight j i≤frames S ∧ frames S≤4*d.rightWeight j i) :
    (Fintype.card (ProgramCount.Label d gaps):ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3 := by
  have hB : 0<frames S := by unfold frames scale; positivity
  have hH1n : 1≤scale S := by
    have hh : 0<scale S := by unfold scale; positivity
    omega
  have hcount := ProgramCount.program_count_bound d gaps (originals S) ((scale S)^4) (frames S)
    hB hg htL htR huL huR hsL hsR hwL hwR
  rw [hA] at hcount
  have hcountR : (Fintype.card (ProgramCount.Label d gaps):ℝ) ≤
    16*S*((2:ℝ)^26*((S:ℝ)+1)*(originals S:ℝ)^2)/(frames S:ℝ)+
      8*S*(originals S:ℝ)*(scale S:ℝ)^4/(frames S:ℝ)+10*S := by
    have hh := (Rat.cast_le (K:=ℝ)).2 hcount
    push_cast at hh
    exact hh
  apply program_scale_bound S (scale S) _ (by exact_mod_cast hS) (by exact_mod_cast hH1n)
  simpa only [originals,frames,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hcountR

end Q4.Candidate.FreezingParameters
#print axioms Q4.Candidate.FreezingParameters.actual_large
#print axioms Q4.Candidate.FreezingParameters.alpha_small
#print axioms Q4.Candidate.FreezingParameters.program_scale_bound
#print axioms Q4.Candidate.FreezingParameters.scalar_bounds
#print axioms Q4.Candidate.FreezingParameters.actual_bounds
#print axioms Q4.Candidate.FreezingParameters.actual_complete_freezing
#print axioms Q4.Candidate.FreezingParameters.catalog_scale_bound
