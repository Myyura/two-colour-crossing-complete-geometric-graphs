import Q4.Candidate.FreezingParameters
import Q4.Candidate.CompleteClassEnergy
import Q4.Candidate.ConservativeGap

/-! Explicit costs for actual complete-drawing freezing, grid localization and
all Y constraints, using the same copy-count and integer scale parameters. -/
namespace Q4.Candidate.FreezingErrors
open Q4.Candidate.FreezingParameters Q4.Candidate.CompleteDrawing
open Q4.Candidate.CompleteProbeFreezing
set_option exponentiation.threshold 512
attribute [local irreducible] scale originals frames a

noncomputable def gridError (S : ℕ) : ℝ :=
  (2:ℝ)^32*((frames S:ℝ)*originals S)^2*(a S)^3
noncomputable def freezingError (S P : ℕ) : ℝ :=
  2*(12*P/(originals S:ℝ))*(104*a S+outsideBudget (originals S) (frames S) P+
    GridCounts.rho (frames S) (originals S))*(104*a S+outsideBudget (originals S) (frames S) P)*
    ((frames S:ℝ)*originals S)^2
noncomputable def yError (S P : ℕ) : ℝ :=
  (Fintype.card (YEdge (originals S) P):ℝ)*
    ((frames S:ℝ)*P+Fintype.card (Inner (originals S)))+
    (Fintype.card (YEdge (originals S) P):ℝ)^2/2

theorem scale_positive (S : ℕ) : 0<scale S := by unfold scale; positivity

theorem cubic_scale_bound (S H : ℝ) (hS : 0≤S) (hH : 0<H) :
    (H^5*(514*S*H^4))^2*(2*alpha (S+1) H)^3≤(2:ℝ)^275*(S+1)^14*H^15 := by
  have hHn : H≠0 := ne_of_gt hH
  have hd0 : 0≤S+1 := by linarith
  have hS2 : S^2≤(S+1)^2 := pow_le_pow_left₀ hS (by linarith) 2
  have he : (H^5*(514*S*H^4))^2*(2*alpha (S+1) H)^3 =
    (514^2*(2:ℝ)^255)*S^2*(S+1)^12*H^15 := by
    unfold alpha
    field_simp
  rw [he]
  calc
    _ ≤ (514^2*(2:ℝ)^255)*(S+1)^2*(S+1)^12*H^15 := by gcongr
    _ = (514^2*(2:ℝ)^255)*((S+1)^14*H^15) := by ring
    _ ≤ (2:ℝ)^275*((S+1)^14*H^15) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

theorem actual_cubic_scale_bound (S : ℕ) :
    ((frames S:ℝ)*originals S)^2*(a S)^3≤(2:ℝ)^275*((S:ℝ)+1)^14*(scale S:ℝ)^15 := by
  simpa only [frames,originals,a,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    cubic_scale_bound S (scale S) (Nat.cast_nonneg S) (by exact_mod_cast scale_positive S)

theorem grid_error_bound (S : ℕ) :
    gridError S≤(2:ℝ)^307*((S:ℝ)+1)^14*(scale S:ℝ)^15 := by
  have hh := mul_le_mul_of_nonneg_left (actual_cubic_scale_bound S) (by positivity : (0:ℝ)≤2^32)
  have hp : (2:ℝ)^32*2^275=2^307 := by norm_num
  unfold gridError
  calc
    _ = (2:ℝ)^32*(((frames S:ℝ)*originals S)^2*(a S)^3) := by ring
    _ ≤ (2:ℝ)^32*((2:ℝ)^275*((S:ℝ)+1)^14*(scale S:ℝ)^15) := hh
    _ = _ := by rw [←mul_assoc,←mul_assoc,hp]

theorem freezing_cubic_bound (Q a beta rho N : ℝ)
    (_hQ0 : 0≤Q) (ha : 0≤a) (hb0 : 0≤beta) (hr0 : 0≤rho)
    (hQ : Q≤a) (hb : beta≤a) (hr : rho≤a) :
    2*Q*(104*a+beta+rho)*(104*a+beta)*N^2≤(2:ℝ)^15*N^2*a^3 := by
  have hb' : 104*a+beta≤105*a := by linarith
  have hr' : 104*a+beta+rho≤106*a := by linarith
  calc
    _ ≤ 2*a*(106*a)*(105*a)*N^2 := by gcongr
    _ ≤ (2:ℝ)^15*N^2*a^3 := by
      have hp : 0≤N^2*a^3 := mul_nonneg (sq_nonneg N) (pow_nonneg ha 3)
      norm_num
      nlinarith only [hp]

theorem freezing_error_bound (S P : ℕ) (hS : 1≤S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3) :
    freezingError S P≤(2:ℝ)^290*((S:ℝ)+1)^14*(scale S:ℝ)^15 := by
  obtain ⟨_,_,_,_,_,hbeta,hQ,hrho,_⟩ := actual_bounds S P hS hP
  have halpha : 0≤alpha ((S:ℝ)+1) (scale S) := by
    exact div_nonneg (mul_nonneg (by positivity) (pow_nonneg (by positivity) 4)) (Nat.cast_nonneg _)
  have ha : 0≤a S := by unfold a; exact mul_nonneg (by norm_num) halpha
  have hcube := freezing_cubic_bound (12*P/(originals S:ℝ)) (a S)
    (outsideBudget (originals S) (frames S) P) (GridCounts.rho (frames S) (originals S))
    ((frames S:ℝ)*originals S)
    (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg P)) (Nat.cast_nonneg _))
    ha outsideBudget_nonneg (GridCounts.rho_nonneg _ _)
    (by unfold a; linarith) (by unfold a; linarith) (by unfold a; linarith)
  have hscale := mul_le_mul_of_nonneg_left (actual_cubic_scale_bound S) (by positivity : (0:ℝ)≤2^15)
  have hp : (2:ℝ)^15*2^275=2^290 := by norm_num
  unfold freezingError
  calc
    _ ≤ (2:ℝ)^15*(((frames S:ℝ)*originals S)^2*(a S)^3) := by
      convert hcube using 1
      ring
    _ ≤ (2:ℝ)^15*((2:ℝ)^275*((S:ℝ)+1)^14*(scale S:ℝ)^15) := hscale
    _ = _ := by rw [←mul_assoc,←mul_assoc,hp]

theorem y_card_bound (O P : ℕ) (hP : P≤O) :
    (Fintype.card (YEdge O P):ℝ)≤2*(O:ℝ)*P := by
  have hi := inner_card_bound P
  have hiR : 2*(Fintype.card (Inner P):ℝ)≤(P:ℝ)^2 := by
    simp only [pow_two]
    exact_mod_cast hi
  have hPr : (P:ℝ)≤O := by exact_mod_cast hP
  have hp := mul_nonneg (Nat.cast_nonneg P : (0:ℝ)≤P) (sub_nonneg.mpr hPr)
  unfold YEdge
  simp_rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  push_cast
  nlinarith only [hiR,hp]

theorem actual_class_counts (S P : ℕ) (hS : 1≤S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3) :
    ((frames S:ℝ)*originals S≤(2:ℝ)^10*((S:ℝ)+1)*(scale S:ℝ)^9) ∧
    ((frames S:ℝ)*P≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^8) ∧
    ((Fintype.card (Inner (originals S)):ℝ)≤(2:ℝ)^19*((S:ℝ)+1)^2*(scale S:ℝ)^8) ∧
    ((Fintype.card (YEdge (originals S) P):ℝ)≤(2:ℝ)^91*((S:ℝ)+1)^5*(scale S:ℝ)^7) := by
  have hH0 : (0:ℝ)≤scale S := Nat.cast_nonneg _
  have hd0 : (0:ℝ)≤(S:ℝ)+1 := by positivity
  have hO : (originals S:ℝ)≤(2:ℝ)^10*((S:ℝ)+1)*(scale S:ℝ)^4 := by
    unfold originals
    push_cast
    have hh : (514:ℝ)*S≤2^10*((S:ℝ)+1) := by norm_num; linarith [Nat.cast_nonneg S (α:=ℝ)]
    exact mul_le_mul_of_nonneg_right hh (pow_nonneg hH0 4)
  have hB : (frames S:ℝ)=(scale S:ℝ)^5 := by unfold frames; push_cast; rfl
  have hN := mul_le_mul_of_nonneg_left hO (Nat.cast_nonneg (frames S) : (0:ℝ)≤frames S)
  have hp := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg (frames S) : (0:ℝ)≤frames S)
  have hi := inner_card_bound (originals S)
  have hiR : 2*(Fintype.card (Inner (originals S)):ℝ)≤(originals S:ℝ)^2 := by
    simp only [pow_two]
    exact_mod_cast hi
  have hPO := (actual_bounds S P hS hP).2.2.1
  have hy := y_card_bound (originals S) P hPO
  refine ⟨?_,?_,?_,?_⟩
  · rw [hB] at hN ⊢
    convert hN using 1
    ring
  · rw [hB] at hp ⊢
    convert hp using 1
    ring
  · calc
      _ ≤ (originals S:ℝ)^2/2 := by linarith
      _ ≤ ((2:ℝ)^10*((S:ℝ)+1)*(scale S:ℝ)^4)^2/2 := by gcongr
      _ = _ := by norm_num; ring
  · calc
      _ ≤ 2*(originals S:ℝ)*P := hy
      _ ≤ 2*((2:ℝ)^10*((S:ℝ)+1)*(scale S:ℝ)^4)*
          ((2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3) := by
        gcongr
      _ = _ := by norm_num; ring

theorem y_scalar_bound (d H h p c : ℝ) (hd : 1≤d) (hH : 1≤H)
    (hh0 : 0≤h) (hp0 : 0≤p) (hc0 : 0≤c)
    (hh : h≤(2:ℝ)^91*d^5*H^7)
    (hp : p≤(2:ℝ)^80*d^4*H^8) (hc : c≤(2:ℝ)^19*d^2*H^8) :
    h*(p+c)+h^2/2≤(2:ℝ)^182*d^10*H^15 := by
  have hd0 : 0≤d := by linarith
  have hH0 : 0≤H := by linarith
  have hd24 : d^2≤d^4 := pow_le_pow_right₀ hd (by omega : 2≤4)
  have hc' : c≤(2:ℝ)^19*d^4*H^8 := hc.trans (by gcongr)
  have hpc : p+c≤(2:ℝ)^81*d^4*H^8 := by
    have hx : 0≤d^4*H^8 := by positivity
    norm_num at hp hc' ⊢
    nlinarith only [hp,hc',hx]
  have hprod : h*(p+c)≤(2:ℝ)^172*d^9*H^15 := by
    calc
      _ ≤ ((2:ℝ)^91*d^5*H^7)*((2:ℝ)^81*d^4*H^8) := by gcongr
      _ = _ := by norm_num; ring
  have hsq : h^2/2≤(2:ℝ)^181*d^10*H^14 := by
    calc
      _ ≤ ((2:ℝ)^91*d^5*H^7)^2/2 := by gcongr
      _ = _ := by norm_num; ring
  have hd910 : d^9≤d^10 := pow_le_pow_right₀ hd (by omega : 9≤10)
  have hH1415 : H^14≤H^15 := pow_le_pow_right₀ hH (by omega : 14≤15)
  have hprod' : h*(p+c)≤(2:ℝ)^172*d^10*H^15 := hprod.trans (by gcongr)
  have hsq' : h^2/2≤(2:ℝ)^181*d^10*H^15 := hsq.trans (by gcongr)
  have hx : 0≤d^10*H^15 := by positivity
  norm_num at hprod' hsq' ⊢
  nlinarith only [hprod',hsq',hx]

theorem y_error_bound (S P : ℕ) (hS : 1≤S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3) :
    yError S P≤(2:ℝ)^182*((S:ℝ)+1)^10*(scale S:ℝ)^15 := by
  obtain ⟨_,hp,hc,hh⟩ := actual_class_counts S P hS hP
  have hH1 : (1:ℝ)≤scale S := by exact_mod_cast scale_positive S
  exact y_scalar_bound ((S:ℝ)+1) (scale S) _ _ _ (by linarith [Nat.cast_nonneg S (α:=ℝ)]) hH1
    (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _) hh hp hc

/-- This bounds every actual TY, CY and YY monochromatic term, for every
coloring, while retaining the manuscript's original R_Y baseline convention. -/
theorem actual_y_remainder_bound (S P : ℕ) (hS : 1≤S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3)
    (ys : Fin (originals S) → ℚ) (ts : Fin (frames S) → ℚ)
    (rs : Fin P → Q4.Candidate.ConvexSeparation.Point)
    (χ : Edge (originals S) (frames S) P → Bool) :
    0≤CompleteClassEnergy.yRemainder ys ts rs χ ∧
    CompleteClassEnergy.yRemainder ys ts rs χ≤(2:ℝ)^182*((S:ℝ)+1)^10*(scale S:ℝ)^15 := by
  have hh := CompleteClassEnergy.yRemainder_bounds ys ts rs χ
  exact ⟨hh.1,hh.2.trans (y_error_bound S P hS hP)⟩

/-- The three actual algebraic error budgets fit inside (7.7). Positivity of
the explicit scale makes the coefficient comparison strict. -/
theorem total_error_bound (S P : ℕ) (hS : 1≤S)
    (hP : (P:ℝ)≤(2:ℝ)^80*((S:ℝ)+1)^4*(scale S:ℝ)^3) :
    freezingError S P+2*gridError S+yError S P<
      (2:ℝ)^310*((S:ℝ)+1)^14*(scale S:ℝ)^15 := by
  have hf := freezing_error_bound S P hS hP
  have hg := grid_error_bound S
  have hy := y_error_bound S P hS hP
  have hd1 : (1:ℝ)≤(S:ℝ)+1 := by linarith [Nat.cast_nonneg S (α:=ℝ)]
  have hd : ((S:ℝ)+1)^10≤((S:ℝ)+1)^14 := pow_le_pow_right₀ hd1 (by omega : 10≤14)
  have hH0 : (0:ℝ)≤scale S := Nat.cast_nonneg _
  have hy' : yError S P≤(2:ℝ)^182*((S:ℝ)+1)^14*(scale S:ℝ)^15 := hy.trans (by gcongr)
  have hp : 0<((S:ℝ)+1)^14*(scale S:ℝ)^15 := mul_pos
    (pow_pos (by linarith) 14) (pow_pos (by exact_mod_cast scale_positive S) 15)
  norm_num at hf hg hy' ⊢
  nlinarith only [hf,hg,hy',hp]

/-- All three actual complete-drawing error budgets, plus the source unary
and local-constraint budgets, fit the final strict signal window. -/
theorem actual_signal_window (n q P : ℕ) (hn : 1≤n) (hq : q=2^20*(n+1))
    (hP : (P:ℝ)≤(2:ℝ)^80*((n*q:ℕ)+1:ℝ)^4*(scale (n*q):ℝ)^3) :
    (2:ℝ)^19*(freezingError (n*q) P+2*gridError (n*q)+yError (n*q) P+
      10*(n*q:ℕ)*(scale (n*q):ℝ)^13+(2/3:ℝ)*(n*q:ℕ)*(scale (n*q):ℝ)^16)<
      (q:ℝ)^2*(scale (n*q):ℝ)^16 := by
  have hqpos : 0<q := by rw [hq]; positivity
  have hS : 1≤n*q := by have hh := Nat.mul_pos (by omega : 0<n) hqpos; omega
  have hAlg := (total_error_bound (n*q) P hS hP).le
  have hqr : (q:ℝ)=(2:ℝ)^20*((n:ℝ)+1) := by exact_mod_cast hq
  have hH : (scale (n*q):ℝ)=(2:ℝ)^20000*((n:ℝ)*q+1)^40 := by
    simp only [scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  have hh := ReductionGap.actual_error_window n (Nat.cast_nonneg n)
    (freezingError (n*q) P+2*gridError (n*q)+yError (n*q) P)
    (10*(n:ℝ)*q*(scale (n*q):ℝ)^13) ((2/3:ℝ)*((n:ℝ)*q)*(scale (n*q):ℝ)^16)
    q ((n:ℝ)*q+1) (scale (n*q)) hqr rfl hH
    (by simpa only [Nat.cast_mul] using hAlg) (by ring_nf; exact le_rfl) (by rfl)
  simpa only [Nat.cast_mul,mul_assoc] using hh

/-- Version using the proved conservative local-pair budget 2 S H^16. The
original 2/3 version above is retained separately, not used in this conclusion. -/
theorem actual_conservative_signal_window (n q P : ℕ) (hn : 1≤n) (hq : q=2^20*(n+1))
    (hP : (P:ℝ)≤(2:ℝ)^80*((n*q:ℕ)+1:ℝ)^4*(scale (n*q):ℝ)^3) :
    (2:ℝ)^18*(freezingError (n*q) P+2*gridError (n*q)+yError (n*q) P+
      10*(n*q:ℕ)*(scale (n*q):ℝ)^13+2*(n*q:ℕ)*(scale (n*q):ℝ)^16)<
      (q:ℝ)^2*(scale (n*q):ℝ)^16 := by
  have hqpos : 0<q := by rw [hq]; positivity
  have hS : 1≤n*q := by have hh := Nat.mul_pos (by omega : 0<n) hqpos; omega
  have hAlg := (total_error_bound (n*q) P hS hP).le
  have hqr : (q:ℝ)=(2:ℝ)^20*((n:ℝ)+1) := by exact_mod_cast hq
  have hH : (scale (n*q):ℝ)=(2:ℝ)^20000*((n:ℝ)*q+1)^40 := by
    simp only [scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  have hh := ConservativeGap.actual_error_window n (Nat.cast_nonneg n)
    (freezingError (n*q) P+2*gridError (n*q)+yError (n*q) P)
    (10*(n:ℝ)*q*(scale (n*q):ℝ)^13) (2*((n:ℝ)*q)*(scale (n*q):ℝ)^16)
    q ((n:ℝ)*q+1) (scale (n*q)) hqr rfl hH
    (by simpa only [Nat.cast_mul] using hAlg) (by ring_nf; exact le_rfl) (by rfl)
  simpa only [Nat.cast_mul,mul_assoc] using hh

end Q4.Candidate.FreezingErrors
#print axioms Q4.Candidate.FreezingErrors.cubic_scale_bound
#print axioms Q4.Candidate.FreezingErrors.grid_error_bound
#print axioms Q4.Candidate.FreezingErrors.freezing_error_bound
#print axioms Q4.Candidate.FreezingErrors.actual_class_counts
#print axioms Q4.Candidate.FreezingErrors.y_error_bound
#print axioms Q4.Candidate.FreezingErrors.actual_y_remainder_bound
#print axioms Q4.Candidate.FreezingErrors.total_error_bound
#print axioms Q4.Candidate.FreezingErrors.actual_signal_window
#print axioms Q4.Candidate.FreezingErrors.actual_conservative_signal_window
