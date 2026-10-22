import Q4.Candidate.ComparisonEnergy
import Q4.Candidate.AnalyticVariance
import Q4.Candidate.ThresholdApproximation

/-!
Actual integral identity for the two diagonal halves in candidate (2.8).
The two halves are genuine measurable Boolean functions; their coordinate
operators are the previously defined comparison-kernel integrals.
-/

open MeasureTheory Set

namespace Q4.Candidate.DiagonalHalves

open Q4.Candidate.UnitIntervalMeasure Q4.Candidate.AlternationKernel

theorem bounded_interval_integrable (h : ℝ → ℝ) (hh : Measurable h)
    (C : ℝ) (hb : ∀ x, ‖h x‖ ≤ C) (a b : ℝ) : IntervalIntegrable h volume a b := by
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound (by simp [uIcc,Real.volume_Icc]) hh.aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun x => hb x)

/-- Split the actual antisymmetric kernel at its threshold; endpoints have
zero measure, and both interval integrals have verified integrability. -/
theorem kernel_integral_split (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ x, ‖h x‖ ≤ 1) (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    (∫ s, AlternationKernel.cmp u s*h s ∂unit) = (∫ s in (0:ℝ)..1, h s)-2*(∫ s in (0:ℝ)..u, h s) := by
  have hk : Measurable (fun s => AlternationKernel.cmp u s*h s) :=
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const).mul hh
  have hkb (x : ℝ) : ‖AlternationKernel.cmp u x*h x‖ ≤ 1 := by
    rw [norm_mul,cmp_norm,one_mul]
    exact hb x
  have hi := bounded_interval_integrable h hh 1 hb
  have hki := bounded_interval_integrable _ hk 1 hkb
  have hpart := intervalIntegral.integral_add_adjacent_intervals (hki 0 u) (hki u 1)
  have hleft : (∫ s in (0:ℝ)..u, AlternationKernel.cmp u s*h s) = -(∫ s in (0:ℝ)..u, h s) := by
    calc
      _ = ∫ s in (0:ℝ)..u, -h s := by
        apply intervalIntegral.integral_congr_Ioo_of_le hu.1
        intro s hs
        simp [AlternationKernel.cmp,not_lt_of_ge hs.2.le]
      _ = _ := intervalIntegral.integral_neg
  have hright : (∫ s in u..1, AlternationKernel.cmp u s*h s) = ∫ s in u..1, h s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hu.2
    intro s hs
    simp [AlternationKernel.cmp,hs.1]
  have htotal := intervalIntegral.integral_add_adjacent_intervals (hi 0 u) (hi u 1)
  have hunit : (∫ s, AlternationKernel.cmp u s*h s ∂unit) = ∫ s in (0:ℝ)..1, AlternationKernel.cmp u s*h s := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rfl
  rw [hleft,hright] at hpart
  rw [hunit]
  linarith

noncomputable def primitive (h : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, h s

theorem shifted_kernel_primitive (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ x, ‖h x‖ ≤ 1) (u v : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    (∫ s, AlternationKernel.cmp u s*h (s+v) ∂unit) =
      primitive h (1+v)+primitive h v-2*primitive h (u+v) := by
  have hs := kernel_integral_split (fun s => h (s+v))
    (hh.comp (measurable_id.add_const v)) (fun s => hb (s+v)) u hu
  rw [intervalIntegral.integral_comp_add_right,intervalIntegral.integral_comp_add_right] at hs
  simp only [zero_add] at hs
  have hi := bounded_interval_integrable h hh 1 hb
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 v) (hi v (1+v))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 v) (hi v (u+v))
  unfold primitive
  linarith

noncomputable def joined (b0 b1 : ℝ → Bool) (s : ℝ) : Bool :=
  if s < 1 then b0 s else b1 (s-1)
noncomputable def diagonal (b0 b1 : ℝ → Bool) (p : ℝ × ℝ) : Bool := joined b0 b1 (p.1+p.2)
noncomputable def F (b0 b1 : ℝ → Bool) (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t, (spin (b0 s)+spin (b1 s))

theorem joined_measurable (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1) :
    Measurable (joined b0 b1) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) h0
    (h1.comp (measurable_id.sub_const 1))

theorem diagonal_measurable (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1) :
    Measurable (diagonal b0 b1) :=
  (joined_measurable b0 b1 h0 h1).comp (measurable_fst.add measurable_snd)

theorem primitive_joined_lower (b0 b1 : ℝ → Bool) (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
    primitive (fun s => spin (joined b0 b1 s)) v = primitive (fun s => spin (b0 s)) v := by
  apply intervalIntegral.integral_congr_Ioo_of_le hv.1
  intro s hs
  simp [joined,show s < 1 by linarith [hs.2,hv.2]]

theorem primitive_joined_upper (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1)
    (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
    primitive (fun s => spin (joined b0 b1 s)) (1+v) =
      primitive (fun s => spin (joined b0 b1 s)) 1+primitive (fun s => spin (b1 s)) v := by
  have hj := joined_measurable b0 b1 h0 h1
  have hi := bounded_interval_integrable _ (measurable_spin_comp _ hj) 1
    (fun s => le_of_eq (spin_norm _))
  have hsum := intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 (1+v))
  have he : (∫ s in (1:ℝ)..1+v, spin (joined b0 b1 s)) = primitive (fun s => spin (b1 s)) v := by
    have hshift := intervalIntegral.integral_comp_add_right (fun s => spin (joined b0 b1 s)) 1
      (a := (0:ℝ)) (b := v)
    simp only [zero_add] at hshift
    rw [add_comm v 1] at hshift
    rw [← hshift]
    apply intervalIntegral.integral_congr_Ioo_of_le hv.1
    intro s hs
    simp [joined,show ¬s+1 < 1 by linarith [hs.1]]
  unfold primitive at *
  linarith

/-- Formula (2.8) for the actual coordinate operators, with no operator
identity as a hypothesis. It holds for any two measurable sign halves. -/
theorem operator_difference (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1)
    (u v : ℝ) (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) :
    Q4.Candidate.ComparisonEnergy.rowOp unit (diagonal b0 b1) (u,v) -
      Q4.Candidate.ComparisonEnergy.colOp unit (diagonal b0 b1) (u,v) = F b0 b1 v-F b0 b1 u := by
  let h : ℝ → ℝ := fun s => spin (joined b0 b1 s)
  have hm : Measurable h := measurable_spin_comp _ (joined_measurable b0 b1 h0 h1)
  have hb (s : ℝ) : ‖h s‖ ≤ 1 := le_of_eq (spin_norm _)
  have hr := shifted_kernel_primitive h hm hb u v hu
  have hc := shifted_kernel_primitive h hm hb v u hv
  have hL (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) := primitive_joined_lower b0 b1 t ht
  have hU (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) := primitive_joined_upper b0 b1 h0 h1 t ht
  have hi0 := bounded_interval_integrable _ (measurable_spin_comp _ h0) 1 (fun s => le_of_eq (spin_norm _))
  have hi1 := bounded_interval_integrable _ (measurable_spin_comp _ h1) 1 (fun s => le_of_eq (spin_norm _))
  have hF (t : ℝ) : F b0 b1 t = primitive (fun s => spin (b0 s)) t+primitive (fun s => spin (b1 s)) t :=
    intervalIntegral.integral_add (hi0 0 t) (hi1 0 t)
  change (∫ s, AlternationKernel.cmp u s*h (s+v) ∂unit)-(∫ s, AlternationKernel.cmp v s*h (u+s) ∂unit) = _
  simp_rw [add_comm u]
  rw [hr,hc]
  dsimp [h]
  rw [hU v hv,hU u hu,hL v hv,hL u hu,hF v,hF u]
  rw [add_comm v u]
  ring

theorem sum_spin_norm (b0 b1 : ℝ → Bool) (s : ℝ) : ‖spin (b0 s)+spin (b1 s)‖ ≤ 2 := by
  have h := norm_add_le (spin (b0 s)) (spin (b1 s))
  simpa only [spin_norm,one_add_one_eq_two] using h

theorem F_continuous (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1) :
    Continuous (F b0 b1) :=
  intervalIntegral.continuous_primitive (bounded_interval_integrable _
    ((measurable_spin_comp _ h0).add (measurable_spin_comp _ h1)) 2 (sum_spin_norm b0 b1)) 0

theorem F_integrable (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1) :
    Integrable (F b0 b1) unit := by
  rw [unit_eq_closed_interval]
  exact (F_continuous b0 b1 h0 h1).continuousOn.integrableOn_Icc

theorem F_sq_integrable (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1) :
    Integrable (fun s => (F b0 b1 s)^2) unit := by
  rw [unit_eq_closed_interval]
  exact ((F_continuous b0 b1 h0 h1).pow 2).continuousOn.integrableOn_Icc

/-- The actual squared coordinate-operator norm is twice the actual variance,
with Fubini/integrability and the operator identity discharged here. -/
theorem differenceSq_eq_twice_variance (b0 b1 : ℝ → Bool)
    (h0 : Measurable b0) (h1 : Measurable b1) :
    Q4.Candidate.ComparisonEnergy.differenceSq unit (diagonal b0 b1) =
      2*(∫ s, (F b0 b1 s-(∫ t, F b0 b1 t ∂unit))^2 ∂unit) := by
  let f := diagonal b0 b1
  have hf : Measurable f := diagonal_measurable b0 b1 h0 h1
  have hD : Integrable (fun p =>
      (Q4.Candidate.ComparisonEnergy.rowOp unit f p-Q4.Candidate.ComparisonEnergy.colOp unit f p)^2)
      (unit.prod unit) := by
    apply Integrable.of_bound
      (((Q4.Candidate.ComparisonEnergy.rowOp_measurable unit f hf).sub
        (Q4.Candidate.ComparisonEnergy.colOp_measurable unit f hf)).pow_const 2).aestronglyMeasurable 4
    filter_upwards [] with p
    rw [norm_pow]
    have hr := Q4.Candidate.ComparisonEnergy.rowOp_norm_le unit f p
    have hc := Q4.Candidate.ComparisonEnergy.colOp_norm_le unit f p
    have hd := norm_sub_le (Q4.Candidate.ComparisonEnergy.rowOp unit f p)
      (Q4.Candidate.ComparisonEnergy.colOp unit f p)
    have hn := norm_nonneg (Q4.Candidate.ComparisonEnergy.rowOp unit f p-
      Q4.Candidate.ComparisonEnergy.colOp unit f p)
    dsimp only [Pi.sub_apply]
    nlinarith
  have hmem : ∀ᵐ s ∂unit, s ∈ Icc (0:ℝ) 1 := by
    rw [unit_eq_closed_interval]
    exact ae_restrict_mem measurableSet_Icc
  have hid : Q4.Candidate.ComparisonEnergy.differenceSq unit f =
      ∫ u, ∫ v, (F b0 b1 v-F b0 b1 u)^2 ∂unit ∂unit := by
    unfold Q4.Candidate.ComparisonEnergy.differenceSq
    rw [integral_prod _ hD]
    apply integral_congr_ae
    filter_upwards [hmem] with u hu
    apply integral_congr_ae
    filter_upwards [hmem] with v hv
    exact congrArg (fun z : ℝ => z^2) (operator_difference b0 b1 h0 h1 u v hu hv)
  rw [hid]
  exact Q4.Candidate.AnalyticVariance.double_difference_eq_twice_variance _
    (F_integrable b0 b1 h0 h1) (F_sq_integrable b0 b1 h0 h1)

noncomputable def threshold (o : Bool) (c x : ℝ) : Bool := if x ≤ c then o else !o

theorem threshold_measurable (o : Bool) (c : ℝ) : Measurable (threshold o c) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem threshold_spin (o : Bool) (c x : ℝ) :
    spin (threshold o c x) = Q4.Candidate.ThresholdApproximation.sign
      (if o then Iic c else Ioi c) x := by
  cases o <;> by_cases hx : x ≤ c <;>
    simp [threshold,spin,Q4.Candidate.ThresholdApproximation.sign,hx,not_le.mp,not_lt.mpr]

theorem same_threshold_eq (o : Bool) (c d x : ℝ) (hcd : c ≤ d) :
    threshold o c x = threshold o d x ↔ x ≤ c ∨ d < x := by
  by_cases hx : x ≤ c
  · simp [threshold,hx,le_trans hx hcd]
  · by_cases hy : x ≤ d
    · cases o <;> simp [threshold,hx,hy,not_lt.mpr hy]
    · simp [threshold,hx,hy,lt_of_not_ge hy]

theorem opposite_threshold_eq (o : Bool) (c d x : ℝ) (hcd : c ≤ d) :
    threshold o c x = threshold (!o) d x ↔ c < x ∧ x ≤ d := by
  by_cases hx : x ≤ c
  · cases o <;> simp [threshold,hx,le_trans hx hcd,not_lt.mpr hx]
  · by_cases hy : x ≤ d
    · cases o <;> simp [threshold,hx,hy,lt_of_not_ge hx]
    · cases o <;> simp [threshold,hx,hy]

noncomputable def agreementMass (b0 b1 : ℝ → Bool) : ℝ := unit.real {s | b0 s = b1 s}

theorem agreementMass_nonneg (b0 b1 : ℝ → Bool) : 0 ≤ agreementMass b0 b1 := measureReal_nonneg

/-- Equal-orientation halves agree on exactly two end intervals inside the
unit interval. This is an actual set/measure computation, including all ties. -/
theorem agreement_same (o : Bool) (c d : ℝ) (hc : c ∈ Icc (0:ℝ) 1)
    (hd : d ∈ Icc (0:ℝ) 1) (hcd : c ≤ d) :
    agreementMass (threshold o c) (threshold o d) = c+(1-d) := by
  have hmeas := measurableSet_eq_fun (threshold_measurable o c) (threshold_measurable o d)
  have he : {s | threshold o c s = threshold o d s} ∩ Ioc (0:ℝ) 1 = Ioc 0 c ∪ Ioc d 1 := by
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq,same_threshold_eq o c d x hcd,mem_Ioc,mem_union]
    constructor
    · rintro ⟨h,hx⟩
      rcases h with h|h
      · exact Or.inl ⟨hx.1,h⟩
      · exact Or.inr ⟨h,hx.2⟩
    · intro h
      rcases h with h|h
      · exact ⟨Or.inl h.2,h.1,le_trans h.2 hc.2⟩
      · exact ⟨Or.inr h.1,lt_of_le_of_lt hd.1 h.1,h.2⟩
  have hdis : Disjoint (Ioc (0:ℝ) c) (Ioc d 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    linarith [hx.2,hy.1]
  unfold agreementMass unit
  rw [measureReal_restrict_apply hmeas,he,measureReal_union hdis measurableSet_Ioc
      (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioc]),
    Real.volume_real_Ioc_of_le hc.1,Real.volume_real_Ioc_of_le hd.2]
  ring

/-- Opposite-orientation halves agree on the single interval between their
two threshold positions. -/
theorem agreement_opposite (o : Bool) (c d : ℝ) (hc : c ∈ Icc (0:ℝ) 1)
    (hd : d ∈ Icc (0:ℝ) 1) (hcd : c ≤ d) :
    agreementMass (threshold o c) (threshold (!o) d) = d-c := by
  have hmeas := measurableSet_eq_fun (threshold_measurable o c) (threshold_measurable (!o) d)
  have he : {s | threshold o c s = threshold (!o) d s} ∩ Ioc (0:ℝ) 1 = Ioc c d := by
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq,opposite_threshold_eq o c d x hcd,mem_Ioc]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,lt_of_le_of_lt hc.1 h.1,le_trans h.2 hd.2⟩
  unfold agreementMass unit
  rw [measureReal_restrict_apply hmeas,he,Real.volume_real_Ioc_of_le hcd]

/-- Constant sum on an actual interval gives a genuine affine primitive
there, derived by interval additivity; no derivative/ramp premise is assumed. -/
theorem F_affine_on (b0 b1 : ℝ → Bool) (h0 : Measurable b0) (h1 : Measurable b1)
    (a b k : ℝ) (_hab : a ≤ b)
    (hconst : ∀ s ∈ Ioo a b, spin (b0 s)+spin (b1 s) = 2*k) :
    ∀ s ∈ Icc a b, F b0 b1 s = F b0 b1 a+2*k*(s-a) := by
  have hi := bounded_interval_integrable _
    ((measurable_spin_comp _ h0).add (measurable_spin_comp _ h1)) 2 (sum_spin_norm b0 b1)
  intro s hs
  have hpart := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a s)
  have he : (∫ x in a..s, spin (b0 x)+spin (b1 x)) = (s-a)*(2*k) := by
    calc
      _ = ∫ x in a..s, (2*k) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.1
        intro x hx
        exact hconst x ⟨hx.1,lt_of_lt_of_le hx.2 hs.2⟩
      _ = _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]
  dsimp only [Pi.add_apply] at hpart
  dsimp [F]
  rw [he] at hpart
  linarith

theorem spin_cases (o : Bool) : spin o = 1 ∨ spin o = -1 := by cases o <;> simp [spin]

/-- The agreement set has a constant-sign interval of length at least half
its actual measure. The two end intervals and middle interval are constructed. -/
theorem ordered_threshold_ramp (o0 o1 : Bool) (c d : ℝ)
    (hc : c ∈ Icc (0:ℝ) 1) (hd : d ∈ Icc (0:ℝ) 1) (hcd : c ≤ d) :
    ∃ a b k : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      agreementMass (threshold o0 c) (threshold o1 d)/2 ≤ b-a ∧
      (k=1 ∨ k=-1) ∧ ∀ s ∈ Icc a b,
        F (threshold o0 c) (threshold o1 d) s =
          F (threshold o0 c) (threshold o1 d) a+2*k*(s-a) := by
  by_cases ho : o1 = o0
  · subst o1
    rw [agreement_same o0 c d hc hd hcd]
    by_cases hlong : 1-d ≤ c
    · refine ⟨0,c,spin o0,le_rfl,hc.1,hc.2,by linarith,spin_cases o0,?_⟩
      apply F_affine_on _ _ (threshold_measurable _ _) (threshold_measurable _ _) _ _ _ hc.1
      intro s hs
      simp [threshold,hs.2.le,show s ≤ d by linarith [hs.2]]
      ring
    · refine ⟨d,1,spin (!o0),hd.1,hd.2,le_rfl,by linarith,spin_cases (!o0),?_⟩
      apply F_affine_on _ _ (threshold_measurable _ _) (threshold_measurable _ _) _ _ _ hd.2
      intro s hs
      simp [threshold,show ¬s ≤ c by linarith [hs.1],not_le.mpr hs.1]
      ring
  · have ho' : o1 = !o0 := by cases o0 <;> cases o1 <;> simp_all
    rw [ho',agreement_opposite o0 c d hc hd hcd]
    refine ⟨c,d,spin (!o0),hc.1,hcd,hd.2,by linarith,spin_cases (!o0),?_⟩
    apply F_affine_on _ _ (threshold_measurable _ _) (threshold_measurable _ _) _ _ _ hcd
    intro s hs
    simp [threshold,not_le.mpr hs.1,hs.2.le]
    ring

theorem F_swap (b0 b1 : ℝ → Bool) : F b0 b1 = F b1 b0 := by
  funext t
  unfold F
  simp_rw [add_comm]

theorem agreementMass_swap (b0 b1 : ℝ → Bool) : agreementMass b0 b1 = agreementMass b1 b0 := by
  unfold agreementMass
  congr 1
  ext x
  exact eq_comm

theorem threshold_ramp (o0 o1 : Bool) (c d : ℝ)
    (hc : c ∈ Icc (0:ℝ) 1) (hd : d ∈ Icc (0:ℝ) 1) :
    ∃ a b k : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      agreementMass (threshold o0 c) (threshold o1 d)/2 ≤ b-a ∧
      (k=1 ∨ k=-1) ∧ ∀ s ∈ Icc a b,
        F (threshold o0 c) (threshold o1 d) s =
          F (threshold o0 c) (threshold o1 d) a+2*k*(s-a) := by
  rcases le_total c d with hcd|hdc
  · exact ordered_threshold_ramp o0 o1 c d hc hd hcd
  · rw [agreementMass_swap,F_swap]
    exact ordered_threshold_ramp o1 o0 d c hd hc hdc

theorem signed_ramp_variance_lower (G : ℝ → ℝ) (hG : Continuous G)
    (a b k c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hk : k=1 ∨ k=-1) (hramp : ∀ s ∈ Icc a b, G s = G a+2*k*(s-a)) :
    (b-a)^3/3 ≤ ∫ s in (0:ℝ)..1, (G s-c)^2 := by
  have hI : IntervalIntegrable (fun s => (G s-c)^2) volume 0 1 :=
    ((hG.sub continuous_const).pow 2).intervalIntegrable _ _
  have he : (∫ s in a..b, (G s-c)^2) =
      ∫ s in a..b, (2*(s-a)-k*(c-G a))^2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    dsimp only
    rw [hramp s hs]
    rcases hk with rfl|rfl <;> ring
  have hshift : (∫ s in a..b, (2*(s-a)-k*(c-G a))^2) =
      ∫ s in (0:ℝ)..(b-a), (2*s-k*(c-G a))^2 := by
    simpa using intervalIntegral.integral_comp_sub_right
      (fun s : ℝ => (2*s-k*(c-G a))^2) a (a := a) (b := b)
  calc
    _ ≤ ∫ s in (0:ℝ)..(b-a), (2*s-k*(c-G a))^2 :=
      Q4.Candidate.AnalyticVariance.affine_ramp_lower _ _ (sub_nonneg.mpr hab)
    _ = ∫ s in a..b, (G s-c)^2 := (he.trans hshift).symm
    _ ≤ _ := intervalIntegral.integral_mono_interval ha hab hb
      (ae_of_all _ (fun s => sq_nonneg (G s-c))) hI

/-- The exact antiperiodicity cubic estimate: m0³ ≤ 12 times the actual
squared coordinate-operator difference. No ramp or variance premise remains. -/
theorem agreement_cubic (o0 o1 : Bool) (c d : ℝ)
    (hc : c ∈ Icc (0:ℝ) 1) (hd : d ∈ Icc (0:ℝ) 1) :
    (agreementMass (threshold o0 c) (threshold o1 d))^3 ≤
      12*Q4.Candidate.ComparisonEnergy.differenceSq unit
        (diagonal (threshold o0 c) (threshold o1 d)) := by
  let b0 := threshold o0 c
  let b1 := threshold o1 d
  let G := F b0 b1
  let mean := ∫ t, G t ∂unit
  obtain ⟨a,b,k,ha,hab,hb,hlen,hk,hramp⟩ := threshold_ramp o0 o1 c d hc hd
  have hG : Continuous G := F_continuous _ _ (threshold_measurable _ _) (threshold_measurable _ _)
  have hv := signed_ramp_variance_lower G hG a b k mean ha hab hb hk hramp
  have hunit : (∫ s in (0:ℝ)..1, (G s-mean)^2) = ∫ s, (G s-mean)^2 ∂unit := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rfl
  rw [hunit] at hv
  have hm := agreementMass_nonneg b0 b1
  have hpow : (agreementMass b0 b1)^3 ≤ (2*(b-a))^3 :=
    pow_le_pow_left₀ hm (by dsimp [b0,b1]; linarith) 3
  have hid := differenceSq_eq_twice_variance b0 b1 (threshold_measurable _ _) (threshold_measurable _ _)
  change Q4.Candidate.ComparisonEnergy.differenceSq unit (diagonal b0 b1) =
    2*(∫ s, (G s-mean)^2 ∂unit) at hid
  change (agreementMass b0 b1)^3 ≤ _
  nlinarith

/-- The manuscript constant in the immediate application of (2.7)-(2.8). -/
theorem agreement_cubic_of_operator_bound (o0 o1 : Bool) (c d A : ℝ)
    (hc : c ∈ Icc (0:ℝ) 1) (hd : d ∈ Icc (0:ℝ) 1)
    (hbound : Q4.Candidate.ComparisonEnergy.differenceSq unit
      (diagonal (threshold o0 c) (threshold o1 d)) ≤ 512*A) :
    (agreementMass (threshold o0 c) (threshold o1 d))^3 ≤ 6144*A := by
  have h := agreement_cubic o0 o1 c d hc hd
  linarith

end Q4.Candidate.DiagonalHalves

#print axioms Q4.Candidate.DiagonalHalves.kernel_integral_split
#print axioms Q4.Candidate.DiagonalHalves.operator_difference
#print axioms Q4.Candidate.DiagonalHalves.differenceSq_eq_twice_variance
#print axioms Q4.Candidate.DiagonalHalves.agreement_same
#print axioms Q4.Candidate.DiagonalHalves.agreement_opposite
#print axioms Q4.Candidate.DiagonalHalves.threshold_ramp
#print axioms Q4.Candidate.DiagonalHalves.agreement_cubic
#print axioms Q4.Candidate.DiagonalHalves.agreement_cubic_of_operator_bound
