import Q4.Candidate.ComparisonEnergy
import Q4.Candidate.SquareTranslation
import Q4.Candidate.BoxAverage
import Q4.Candidate.DiagonalCoordinates
import Q4.Candidate.DiagonalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
Actual box smoothing and its diagonal derivative. Finite operator increments,
affine change of variables, Lipschitz regularity, Lebesgue differentiation and
Rademacher give the genuine four-corner formula. Its L1 bound is then inserted
into the actual diagonal Poincaré inequality; no derivative identity is assumed.
-/
open MeasureTheory MeasureTheory.Measure Set

namespace Q4.Candidate.BoxDerivative
open Q4.Candidate.UnitIntervalMeasure
open Q4.Candidate.AlternationKernel
open Q4.Candidate.ComparisonEnergy

noncomputable def operatorDifference (f : Point → Bool) (p : Point) : ℝ :=
  rowOp unit f p - colOp unit f p

/-- Exact jump of the antisymmetric kernel, with the correct half-open interval. -/
theorem cmp_increment (a b y : ℝ) (hab : a ≤ b) :
    AlternationKernel.cmp b y - AlternationKernel.cmp a y =
      -2 * (Ioc a b).indicator (fun _ => (1:ℝ)) y := by
  classical
  by_cases hay : a < y <;> by_cases hby : b < y
  · simp [AlternationKernel.cmp,hay,hby,not_le_of_gt hby]
  · norm_num [AlternationKernel.cmp,hay,hby,le_of_not_gt hby]
  · exfalso; exact hay (lt_of_le_of_lt hab hby)
  · simp [AlternationKernel.cmp,hay,hby]

theorem fixed_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ℝ → Bool) (hh : Measurable h) (a : ℝ) :
    Integrable (fun y => kernel h a y) μ :=
  bounded_integrable μ _ ((kernel_measurable h hh).comp (measurable_const.prodMk measurable_id))
    (fun y => le_of_eq (kernel_norm h a y))

/-- An actual operator increment is exactly an integral over (a,b]. -/
theorem transform_increment (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ℝ → Bool) (hh : Measurable h) (a b : ℝ) (hab : a ≤ b) :
    transform μ h b - transform μ h a = -2 * ∫ y in Ioc a b, spin (h y) ∂μ := by
  rw [transform,transform,←integral_sub (fixed_kernel_integrable μ h hh b)
    (fixed_kernel_integrable μ h hh a)]
  calc
    _ = ∫ y, -2 * (Ioc a b).indicator (fun y => spin (h y)) y ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he := cmp_increment a b y hab
      by_cases hy : y ∈ Ioc a b
      · simp only [indicator_of_mem hy] at he ⊢
        dsimp [kernel]
        rw [←sub_mul,he]
        ring
      · simp only [indicator_of_notMem hy,mul_zero] at he ⊢
        dsimp [kernel]
        rw [←sub_mul,he]
        ring
    _ = _ := by rw [integral_const_mul,integral_indicator measurableSet_Ioc]

theorem unit_restrict_subinterval (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    unit.restrict (Ioc a b) = volume.restrict (Ioc a b) := by
  have hs : Ioc a b ⊆ Ioc (0:ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_le_of_lt ha hx.1,le_trans hx.2 hb⟩
  rw [unit,Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr hs]

theorem row_increment (f : Point → Bool) (hf : Measurable f) (a b v : ℝ)
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    rowOp unit f (b,v)-rowOp unit f (a,v) = -2*∫ u in Ioc a b, spin (f (u,v)) := by
  have he := transform_increment unit (fun u => f (u,v))
    (hf.comp (measurable_id.prodMk measurable_const)) a b hab
  rw [unit_restrict_subinterval a b ha hb] at he
  exact he

theorem col_increment (f : Point → Bool) (hf : Measurable f) (c d u : ℝ)
    (hcd : c ≤ d) (hc : 0 ≤ c) (hd : d ≤ 1) :
    colOp unit f (u,d)-colOp unit f (u,c) = -2*∫ v in Ioc c d, spin (f (u,v)) := by
  have he := transform_increment unit (fun v => f (u,v))
    (hf.comp (measurable_const.prodMk measurable_id)) c d hcd
  rw [unit_restrict_subinterval c d hc hd] at he
  exact he

/-- The exact rectangle identity underlying (∂u-∂v)f = (∂u∂v D)/2.
The boundary integrals are displayed separately, avoiding any derivative
assumption or exceptional-point convention. -/
theorem rectangle_identity (f : Point → Bool) (hf : Measurable f) (a b c d : ℝ)
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hcd : c ≤ d) (hc : 0 ≤ c) (hd : d ≤ 1) :
    operatorDifference f (b,d)-operatorDifference f (a,d)-
      operatorDifference f (b,c)+operatorDifference f (a,c) =
      2*((∫ v in Ioc c d, spin (f (b,v)))-(∫ v in Ioc c d, spin (f (a,v)))-
        (∫ u in Ioc a b, spin (f (u,d)))+(∫ u in Ioc a b, spin (f (u,c)))) := by
  have hrd := row_increment f hf a b d hab ha hb
  have hrc := row_increment f hf a b c hab ha hb
  have hcb := col_increment f hf c d b hcd hc hd
  have hca := col_increment f hf c d a hcd hc hd
  dsimp [operatorDifference]
  linarith

noncomputable def cornerDifference (D : Point → ℝ) (h : ℝ) (p : Point) : ℝ :=
  D (p+(h,h))-D (p+(-h,h))-D (p+(h,-h))+D (p+(-h,-h))
noncomputable def cornerQuotient (D : Point → ℝ) (h : ℝ) (p : Point) : ℝ :=
  cornerDifference D h p / (8*h^2)

/-- The four-corner finite difference is an actual integrable function. -/
theorem cornerDifference_integrable (D : Point → ℝ) (hD : Integrable D) (h : ℝ) :
    Integrable (cornerDifference D h) :=
  (((hD.comp_add_right (h,h)).sub (hD.comp_add_right (-h,h))).sub
    (hD.comp_add_right (h,-h))).add (hD.comp_add_right (-h,-h))

theorem cornerDifference_abs_bound (D : Point → ℝ) (hD : Integrable D) (h : ℝ) :
    (∫ p, |cornerDifference D h p|) ≤ 4 * ∫ p, |D p| := by
  have h1 := (hD.comp_add_right (h,h)).abs
  have h2 := (hD.comp_add_right (-h,h)).abs
  have h3 := (hD.comp_add_right (h,-h)).abs
  have h4 := (hD.comp_add_right (-h,-h)).abs
  have hs12 : Integrable (fun p => |D (p+(h,h))|+|D (p+(-h,h))|) := h1.add h2
  have hs123 : Integrable (fun p => |D (p+(h,h))|+|D (p+(-h,h))|+|D (p+(h,-h))|) := hs12.add h3
  calc
    _ ≤ ∫ p, |D (p+(h,h))|+|D (p+(-h,h))|+|D (p+(h,-h))|+|D (p+(-h,-h))| := by
      apply integral_mono (cornerDifference_integrable D hD h).abs (hs123.add h4)
      intro p
      dsimp only [cornerDifference,Pi.add_apply]
      have hA := abs_add_le (D (p+(h,h))-D (p+(-h,h))-D (p+(h,-h))) (D (p+(-h,-h)))
      have hB := abs_sub (D (p+(h,h))-D (p+(-h,h))) (D (p+(h,-h)))
      have hC := abs_sub (D (p+(h,h))) (D (p+(-h,h)))
      linarith
    _ = _ := by
      rw [integral_add hs123 h4,integral_add hs12 h3,integral_add h1 h2]
      simp_rw [integral_add_right_eq_self (fun p => |D p|)]
      ring

/-- The coefficient 1/(2h²) is derived from all four translated corners. -/
theorem cornerQuotient_L1_bound (D : Point → ℝ) (hD : Integrable D) (h : ℝ) (hh : 0 < h) :
    (∫ p, |cornerQuotient D h p|) ≤ (∫ p, |D p|)/(2*h^2) := by
  have hden : 0 < 8*h^2 := by positivity
  simp_rw [cornerQuotient,abs_div,abs_of_pos hden]
  rw [integral_div]
  calc
    _ ≤ (4*(∫ p, |D p|))/(8*h^2) :=
      (div_le_div_iff_of_pos_right hden).2 (cornerDifference_abs_bound D hD h)
    _ = _ := by field_simp; ring

theorem cornerQuotient_restrict_L1_bound (D : Point → ℝ) (hD : Integrable D)
    (h : ℝ) (hh : 0 < h) (S : Set Point) :
    (∫ p in S, |cornerQuotient D h p|) ≤ (∫ p, |D p|)/(2*h^2) := by
  have hi := ((cornerDifference_integrable D hD h).div_const (8*h^2)).abs
  exact (integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun p => abs_nonneg (cornerQuotient D h p))) hi).trans
      (cornerQuotient_L1_bound D hD h hh)

noncomputable def zeroDifference (f : Point → Bool) : Point → ℝ :=
  ((Ioc (0:ℝ) 1) ×ˢ (Ioc (0:ℝ) 1)).indicator (operatorDifference f)

theorem operatorDifference_measurable (f : Point → Bool) (hf : Measurable f) :
    Measurable (operatorDifference f) :=
  (rowOp_measurable unit f hf).sub (colOp_measurable unit f hf)

theorem zeroDifference_integrable (f : Point → Bool) (hf : Measurable f) :
    Integrable (zeroDifference f) := by
  have hi : Integrable (operatorDifference f) (unit.prod unit) :=
    Integrable.of_bound (operatorDifference_measurable f hf).aestronglyMeasurable 2
      (Filter.Eventually.of_forall (fun p => by
        have ht := norm_sub_le (rowOp unit f p) (colOp unit f p)
        have hr := rowOp_norm_le unit f p
        have hc := colOp_norm_le unit f p
        change ‖rowOp unit f p-colOp unit f p‖ ≤ 2
        linarith))
  rw [unit,Measure.prod_restrict,←Measure.volume_eq_prod] at hi
  exact (show IntegrableOn (operatorDifference f)
    ((Ioc (0:ℝ) 1) ×ˢ (Ioc (0:ℝ) 1)) volume from hi).integrable_indicator
      (measurableSet_Ioc.prod measurableSet_Ioc)

theorem integral_zeroDifference_abs (f : Point → Bool) :
    (∫ p, |zeroDifference f p|) = ∫ p, |operatorDifference f p| ∂unit.prod unit := by
  classical
  have he : (fun p => |zeroDifference f p|) =
      ((Ioc (0:ℝ) 1) ×ˢ (Ioc (0:ℝ) 1)).indicator (fun p => |operatorDifference f p|) := by
    funext p
    by_cases hp : p ∈ (Ioc (0:ℝ) 1) ×ˢ (Ioc (0:ℝ) 1) <;> simp [zeroDifference,hp]
  rw [he,integral_indicator (measurableSet_Ioc.prod measurableSet_Ioc),
    unit,Measure.prod_restrict,←Measure.volume_eq_prod]

/-- The actual four-corner quotient of D has the required interior L1 bound. -/
theorem operator_corner_L1_bound (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (S : Set Point) :
    (∫ p in S, |cornerQuotient (zeroDifference f) h p|) ≤
      (∫ p, |operatorDifference f p| ∂unit.prod unit)/(2*h^2) := by
  rw [←integral_zeroDifference_abs f]
  exact cornerQuotient_restrict_L1_bound _ (zeroDifference_integrable f hf) h hh S

noncomputable def boundaryQuotient (f : Point → Bool) (h : ℝ) (p : Point) : ℝ :=
  ((∫ v in Ioc (p.2-h) (p.2+h), spin (f (p.1+h,v)))-
    (∫ v in Ioc (p.2-h) (p.2+h), spin (f (p.1-h,v)))-
    (∫ u in Ioc (p.1-h) (p.1+h), spin (f (u,p.2+h)))+
    (∫ u in Ioc (p.1-h) (p.1+h), spin (f (u,p.2-h))))/(4*h^2)

/-- Inside the closed inner square, the actual four-operator corner quotient
is exactly the signed difference of the four boundary integrals. -/
theorem corner_boundary_identity (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (p : Point)
    (hp : h ≤ p.1 ∧ p.1 ≤ 1-h ∧ h ≤ p.2 ∧ p.2 ≤ 1-h) :
    cornerQuotient (operatorDifference f) h p = boundaryQuotient f h p := by
  have he := rectangle_identity f hf (p.1-h) (p.1+h) (p.2-h) (p.2+h)
    (by linarith) (by linarith [hp.1]) (by linarith [hp.2.1])
    (by linarith) (by linarith [hp.2.2.1]) (by linarith [hp.2.2.2])
  unfold cornerQuotient cornerDifference boundaryQuotient
  simp only [Prod.add_def,sub_eq_add_neg] at he ⊢
  rw [he]
  field_simp
  ring

/-- On the open inner square all four corners lie in (0,1]², so the zero
extension introduces no boundary terms in the preceding exact identity. -/
theorem zero_corner_boundary_identity (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (p : Point)
    (hp : h < p.1 ∧ p.1 < 1-h ∧ h < p.2 ∧ p.2 < 1-h) :
    cornerQuotient (zeroDifference f) h p = boundaryQuotient f h p := by
  have hc : ∀ a b, |a| ≤ h → |b| ≤ h →
      zeroDifference f (p+(a,b)) = operatorDifference f (p+(a,b)) := by
    intro a b ha hb
    have hpa := abs_le.mp ha
    have hpb := abs_le.mp hb
    apply indicator_of_mem
    constructor <;> constructor <;> dsimp only [Prod.add_def] <;>
      linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
  unfold cornerQuotient cornerDifference
  rw [hc h h (by simp [abs_of_pos hh]) (by simp [abs_of_pos hh]),
    hc (-h) h (by simp [abs_of_pos hh]) (by simp [abs_of_pos hh]),
    hc h (-h) (by simp [abs_of_pos hh]) (by simp [abs_of_pos hh]),
    hc (-h) (-h) (by simp [abs_of_pos hh]) (by simp [abs_of_pos hh])]
  exact corner_boundary_identity f hf h hh p
    ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hp.2.2.2.le⟩

/-- The moving-window derivative is proved from the Lebesgue differentiation
 theorem, with both translated exceptional sets removed. -/
theorem moving_interval_ae_derivative (g : ℝ → ℝ) (hg : Integrable g) (h : ℝ) :
    ∀ᵐ x, HasDerivAt (fun x => ∫ t in (x-h)..(x+h), g t)
      (g (x+h)-g (x-h)) x := by
  have ht := LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable
  have hp := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae ht
  have hm := (measurePreserving_add_right volume (-h)).quasiMeasurePreserving.ae ht
  filter_upwards [hp,hm] with x hp hm
  have hplus : HasDerivAt (fun y => ∫ t in (0:ℝ)..(y+h), g t) (g (x+h)) x := by
    exact (hp 0).comp_add_const x h
  have hminus : HasDerivAt (fun y => ∫ t in (0:ℝ)..(y-h), g t) (g (x-h)) x := by
    simpa only [sub_eq_add_neg] using (hm 0).comp_add_const x (-h)
  apply (hplus.sub hminus).congr_of_eventuallyEq
  filter_upwards [] with y
  exact (intervalIntegral.integral_interval_sub_left hg.intervalIntegrable
    hg.intervalIntegrable).symm

/-- Affine transport of the probability interval equals the normalized
Lebesgue interval integral; this is a genuine change of variables. -/
theorem unit_affine_integral (g : ℝ → ℝ) (c d : ℝ) (hc : 0 < c) :
    (∫ x, g (c*x+d) ∂unit) = (∫ y in Ioc d (c+d), g y)/c := by
  change (∫ x in Ioc (0:ℝ) 1, g (c*x+d)) = _
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_add g hc.ne' d]
  simp only [mul_zero,zero_add,mul_one,smul_eq_mul]
  rw [intervalIntegral.integral_of_le (by linarith : d ≤ c+d)]
  ring

noncomputable def rowWindow (f : Point → Bool) (h v u : ℝ) : ℝ :=
  ∫ t in Ioc (v-h) (v+h), SquareTranslation.zeroSquare f (u,t)

noncomputable def rectangleAverage (f : Point → Bool) (h : ℝ) (p : Point) : ℝ :=
  (∫ u in Ioc (p.1-h) (p.1+h), rowWindow f h p.2 u)/(4*h^2)

theorem zeroSquare_norm_le (f : Point → Bool) (p : Point) :
    ‖SquareTranslation.zeroSquare f p‖ ≤ 1 := by
  classical
  by_cases hp : p ∈ (Ioc (0:ℝ) 1) ×ˢ (Ioc (0:ℝ) 1)
  · rw [SquareTranslation.zeroSquare,indicator_of_mem hp]
    exact (spin_norm (f p)).le
  · simp [SquareTranslation.zeroSquare,hp]

/-- The affine-probability smoothing used in BoxAverage is exactly the
normalized moving Lebesgue rectangle average. -/
theorem average_eq_rectangle (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (p : Point) :
    BoxAverage.average (BoxAverage.boxMeasure h) (SquareTranslation.zeroSquare f) p =
      rectangleAverage f h p := by
  have hz := SquareTranslation.zeroSquare_measurable f hf
  have hm : Measurable (fun z : Point => SquareTranslation.zeroSquare f (BoxAverage.boxMap h z+p)) :=
    hz.comp ((BoxAverage.boxMap_measurable h).add measurable_const)
  have hi := bounded_integrable (unit.prod unit) _ hm (fun z => zeroSquare_norm_le f _)
  unfold BoxAverage.average BoxAverage.boxMeasure
  have hmap : AEStronglyMeasurable (fun z : Point => SquareTranslation.zeroSquare f (z+p))
      ((unit.prod unit).map (BoxAverage.boxMap h)) :=
    (hz.comp (measurable_id.add measurable_const)).aestronglyMeasurable
  rw [integral_map (BoxAverage.boxMap_measurable h).aemeasurable hmap,
    integral_prod _ hi]
  have hcoord (x v : ℝ) : h*(2*x-1)+v = (2*h)*x+(v-h) := by ring
  change (∫ u, ∫ v, SquareTranslation.zeroSquare f
    (h*(2*u-1)+p.1,h*(2*v-1)+p.2) ∂unit ∂unit) = _
  simp_rw [hcoord]
  have hint (u : ℝ) : (∫ v, SquareTranslation.zeroSquare f
      ((2*h)*u+(p.1-h),(2*h)*v+(p.2-h)) ∂unit) =
      rowWindow f h p.2 ((2*h)*u+(p.1-h))/(2*h) := by
    have he := unit_affine_integral
      (fun t => SquareTranslation.zeroSquare f ((2*h)*u+(p.1-h),t))
      (2*h) (p.2-h) (by positivity)
    simpa only [show 2*h+(p.2-h) = p.2+h by ring,rowWindow] using he
  simp_rw [hint]
  rw [integral_div,unit_affine_integral (rowWindow f h p.2) (2*h) (p.1-h) (by positivity)]
  rw [show 2*h+(p.1-h) = p.1+h by ring]
  unfold rectangleAverage
  field_simp
  ring

theorem rowWindow_measurable (f : Point → Bool) (hf : Measurable f) (h v : ℝ) :
    Measurable (rowWindow f h v) := by
  have hz := SquareTranslation.zeroSquare_measurable f hf
  exact hz.stronglyMeasurable.integral_prod_right'.measurable

theorem rowWindow_norm_le (f : Point → Bool) (h v u : ℝ) (hh : 0 ≤ h) :
    ‖rowWindow f h v u‖ ≤ 2*h := by
  unfold rowWindow
  rw [←intervalIntegral.integral_of_le (by linarith : v-h ≤ v+h)]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := v-h) (b := v+h) (fun t _ => zeroSquare_norm_le f (u,t))
  simpa only [one_mul, show v+h-(v-h) = 2*h by ring, abs_of_nonneg (by positivity : 0 ≤ 2*h)] using he

theorem rowWindow_integrable (f : Point → Bool) (hf : Measurable f) (h v : ℝ) :
    Integrable (rowWindow f h v) := by
  have hi := (SquareTranslation.zeroSquare_integrable f hf).integrableOn
    (s := Set.univ ×ˢ Ioc (v-h) (v+h))
  unfold IntegrableOn at hi
  rw [Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  rw [Measure.restrict_univ] at hi
  change Integrable (fun u => ∫ t in Ioc (v-h) (v+h), SquareTranslation.zeroSquare f (u,t))
  exact hi.integral_prod_left

/-- Each fixed horizontal slice has its actual two boundary integrals as
the a.e. derivative of the moving box average. -/
theorem rectangle_row_ae_derivative (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 ≤ h) (v : ℝ) :
    ∀ᵐ u, HasDerivAt (fun u => rectangleAverage f h (u,v))
      ((rowWindow f h v (u+h)-rowWindow f h v (u-h))/(4*h^2)) u := by
  filter_upwards [moving_interval_ae_derivative _ (rowWindow_integrable f hf h v) h] with u hu
  have he : (fun u => ∫ t in (u-h)..(u+h), rowWindow f h v t) =
      (fun u => ∫ t in Ioc (u-h) (u+h), rowWindow f h v t) := by
    funext u
    exact intervalIntegral.integral_of_le (by linarith)
  rw [he] at hu
  exact hu.div_const _

/-- A bounded integrand gives a quantitative Lipschitz estimate for the
moving interval, directly from its two endpoint primitives. -/
theorem moving_interval_lipschitz (g : ℝ → ℝ) (hg : Integrable g)
    (B h x y : ℝ) (hB : ∀ t, ‖g t‖ ≤ B) :
    |(∫ t in (x-h)..(x+h), g t)-(∫ t in (y-h)..(y+h), g t)| ≤ 2*B*|x-y| := by
  let F (z : ℝ) := ∫ t in (0:ℝ)..z, g t
  have he (a b : ℝ) : F a-F b = ∫ t in b..a, g t :=
    intervalIntegral.integral_interval_sub_left hg.intervalIntegrable hg.intervalIntegrable
  have hb (a b : ℝ) : |F a-F b| ≤ B*|a-b| := by
    rw [he]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hB t)
  rw [←he,←he]
  have hid : F (x+h)-F (x-h)-(F (y+h)-F (y-h)) =
      (F (x+h)-F (y+h))-(F (x-h)-F (y-h)) := by ring
  rw [hid]
  have htri := abs_sub (F (x+h)-F (y+h)) (F (x-h)-F (y-h))
  have hp := hb (x+h) (y+h)
  have hm := hb (x-h) (y-h)
  simp only [add_sub_add_right_eq_sub,sub_sub_sub_cancel_right] at hp hm
  linarith

theorem rectangle_row_lipschitz (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (v x y : ℝ) :
    |rectangleAverage f h (x,v)-rectangleAverage f h (y,v)| ≤ |x-y|/h := by
  have hb := moving_interval_lipschitz _ (rowWindow_integrable f hf h v)
    (2*h) h x y (fun u => rowWindow_norm_le f h v u hh.le)
  rw [intervalIntegral.integral_of_le (by linarith : x-h ≤ x+h),
    intervalIntegral.integral_of_le (by linarith : y-h ≤ y+h)] at hb
  unfold rectangleAverage
  simp only [←sub_div,abs_div,abs_of_pos (by positivity : 0 < 4*h^2)]
  calc
    _ ≤ (2*(2*h)*|x-y|)/(4*h^2) := (div_le_div_iff_of_pos_right (by positivity)).2 hb
    _ = _ := by field_simp; ring

def swapColor (f : Point → Bool) (p : Point) : Bool := f p.swap

theorem zeroSquare_swap (f : Point → Bool) (u v : ℝ) :
    SquareTranslation.zeroSquare (swapColor f) (u,v) = SquareTranslation.zeroSquare f (v,u) := by
  classical
  by_cases hu : u ∈ Ioc (0:ℝ) 1 <;> by_cases hv : v ∈ Ioc (0:ℝ) 1 <;>
    simp [SquareTranslation.zeroSquare,swapColor,hu,hv]

theorem rectangle_swap (f : Point → Bool) (hf : Measurable f) (h u v : ℝ) :
    rectangleAverage (swapColor f) h (v,u) = rectangleAverage f h (u,v) := by
  have hi := (SquareTranslation.zeroSquare_integrable f hf).integrableOn
    (s := Ioc (u-h) (u+h) ×ˢ Ioc (v-h) (v+h))
  unfold IntegrableOn at hi
  rw [Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  unfold rectangleAverage rowWindow
  simp only [zeroSquare_swap]
  rw [integral_integral_swap (f := fun u v => SquareTranslation.zeroSquare f (u,v)) hi]

theorem rectangle_col_lipschitz (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (u x y : ℝ) :
    |rectangleAverage f h (u,x)-rectangleAverage f h (u,y)| ≤ |x-y|/h := by
  simpa only [rectangle_swap f hf] using rectangle_row_lipschitz
    (swapColor f) (hf.comp measurable_swap) h hh u x y

/-- The actual box average is globally Lipschitz; its diagonal restrictions
are therefore absolutely continuous, independently of exceptional sets. -/
theorem rectangle_lipschitz (f : Point → Bool) (hf : Measurable f) (h : ℝ) (hh : 0 < h) :
    LipschitzWith ⟨2/h,by positivity⟩ (rectangleAverage f h) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change |rectangleAverage f h p-rectangleAverage f h q| ≤ (2/h)*dist p q
  have hr := rectangle_row_lipschitz f hf h hh p.2 p.1 q.1
  have hc := rectangle_col_lipschitz f hf h hh q.1 p.2 q.2
  have ht := abs_sub_le (rectangleAverage f h p) (rectangleAverage f h (q.1,p.2))
    (rectangleAverage f h q)
  have h1 : |p.1-q.1| ≤ dist p q := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have h2 : |p.2-q.2| ≤ dist p q := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  have h1' := (div_le_div_iff_of_pos_right hh).2 h1
  have h2' := (div_le_div_iff_of_pos_right hh).2 h2
  calc
    _ ≤ |p.1-q.1|/h+|p.2-q.2|/h := ht.trans (add_le_add hr hc)
    _ ≤ dist p q/h+dist p q/h := add_le_add h1' h2'
    _ = _ := by ring

noncomputable def rowBoundary (f : Point → Bool) (h : ℝ) (p : Point) : ℝ :=
  (rowWindow f h p.2 (p.1+h)-rowWindow f h p.2 (p.1-h))/(4*h^2)
noncomputable def colBoundary (f : Point → Bool) (h : ℝ) (p : Point) : ℝ :=
  rowBoundary (swapColor f) h p.swap

theorem rectangle_col_ae_derivative (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 ≤ h) (u : ℝ) :
    ∀ᵐ v, HasDerivAt (fun v => rectangleAverage f h (u,v)) (colBoundary f h (u,v)) v := by
  have he := rectangle_row_ae_derivative (swapColor f) (hf.comp measurable_swap) h hh u
  simpa only [rectangle_swap f hf,colBoundary,rowBoundary,Prod.swap_prod_mk] using he

theorem rowWindow_joint_measurable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Measurable (fun p : Point => rowWindow f h p.2 p.1) := by
  let S : Set (Point × ℝ) := {q | q.1.2-h < q.2 ∧ q.2 ≤ q.1.2+h}
  have hS : MeasurableSet S :=
    (measurableSet_lt (measurable_fst.snd.sub measurable_const) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.snd.add measurable_const))
  have hm : Measurable (S.indicator (fun q : Point × ℝ =>
      SquareTranslation.zeroSquare f (q.1.1,q.2))) :=
    ((SquareTranslation.zeroSquare_measurable f hf).comp
      (measurable_fst.fst.prodMk measurable_snd)).indicator hS
  have he (p : Point) : (∫ t, S.indicator (fun q : Point × ℝ =>
      SquareTranslation.zeroSquare f (q.1.1,q.2)) (p,t)) = rowWindow f h p.2 p.1 := by
    change (∫ t, (Ioc (p.2-h) (p.2+h)).indicator
      (fun t => SquareTranslation.zeroSquare f (p.1,t)) t) = _
    exact integral_indicator measurableSet_Ioc
  simpa only [he] using (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem rowBoundary_measurable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Measurable (rowBoundary f h) := by
  have hm := rowWindow_joint_measurable f hf h
  exact ((hm.comp ((measurable_fst.add measurable_const).prodMk measurable_snd)).sub
    (hm.comp ((measurable_fst.sub measurable_const).prodMk measurable_snd))).div_const _

theorem colBoundary_measurable (f : Point → Bool) (hf : Measurable f) (h : ℝ) :
    Measurable (colBoundary f h) :=
  (rowBoundary_measurable (swapColor f) (hf.comp measurable_swap) h).comp measurable_swap

theorem rectangle_diagonal_ac (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (s a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun u => rectangleAverage f h (u,s-u)) a b := by
  have hl : LipschitzWith 1 (fun u : ℝ => (u,s-u)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul,Prod.dist_eq,Real.dist_eq,
      sub_sub_sub_cancel_left,abs_sub_comm y x,max_self,le_refl]
  exact ((rectangle_lipschitz f hf h hh).comp hl).lipschitzOnWith.absolutelyContinuousOnInterval

/-- The horizontal coefficient of the true Fréchet derivative equals its
boundary integral almost everywhere. Measurability of the coefficient lets
Fubini assemble the sectionwise Lebesgue differentiation result. -/
theorem rectangle_fderiv_row (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) :
    ∀ᵐ p : Point, fderiv ℝ (rectangleAverage f h) p (1,0) = rowBoundary f h p := by
  have hd : ∀ᵐ p ∂(volume : Measure ℝ).prod volume,
      DifferentiableAt ℝ (rectangleAverage f h) p :=
    (rectangle_lipschitz f hf h hh).ae_differentiableAt
  have hs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).quasiMeasurePreserving.ae hd)
  have he : ∀ᵐ v : ℝ, ∀ᵐ u : ℝ,
      fderiv ℝ (rectangleAverage f h) (u,v) (1,0) = rowBoundary f h (u,v) := by
    filter_upwards [hs] with v hv
    filter_upwards [hv,rectangle_row_ae_derivative f hf h hh.le v] with u hu hr
    have hc := hu.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))
    exact hc.unique hr
  have hm := measurableSet_eq_fun (measurable_fderiv_apply_const ℝ (rectangleAverage f h) (1,0))
    (rowBoundary_measurable f hf h)
  have he' := (Measure.ae_ae_comm hm).mpr he
  exact (Measure.ae_prod_iff_ae_ae hm).mpr he'

theorem rectangle_fderiv_col (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) :
    ∀ᵐ p : Point, fderiv ℝ (rectangleAverage f h) p (0,1) = colBoundary f h p := by
  have hd : ∀ᵐ p ∂(volume : Measure ℝ).prod volume,
      DifferentiableAt ℝ (rectangleAverage f h) p :=
    (rectangle_lipschitz f hf h hh).ae_differentiableAt
  have he : ∀ᵐ u : ℝ, ∀ᵐ v : ℝ,
      fderiv ℝ (rectangleAverage f h) (u,v) (0,1) = colBoundary f h (u,v) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hd] with u hu
    filter_upwards [hu,rectangle_col_ae_derivative f hf h hh.le u] with v hv hc
    have hr := hv.hasFDerivAt.comp_hasDerivAt v ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))
    exact hr.unique hc
  have hm := measurableSet_eq_fun (measurable_fderiv_apply_const ℝ (rectangleAverage f h) (0,1))
    (colBoundary_measurable f hf h)
  exact (Measure.ae_prod_iff_ae_ae hm).mpr he

/-- Genuine diagonal derivative after assembling the two Fréchet
coefficients. The quantifiers are a.e. diagonal line, then a.e. point. -/
theorem rectangle_diagonal_ae_derivative (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) :
    ∀ᵐ s : ℝ, ∀ᵐ u : ℝ, HasDerivAt (fun t => rectangleAverage f h (t,s-t))
      (rowBoundary f h (u,s-u)-colBoundary f h (u,s-u)) u := by
  have hd : ∀ᵐ p ∂(volume : Measure ℝ).prod volume, DifferentiableAt ℝ (rectangleAverage f h) p :=
    (rectangle_lipschitz f hf h hh).ae_differentiableAt
  have hr := rectangle_fderiv_row f hf h hh
  have hc := rectangle_fderiv_col f hf h hh
  have hall : ∀ᵐ p : Point, DifferentiableAt ℝ (rectangleAverage f h) p ∧
      fderiv ℝ (rectangleAverage f h) p (1,0) = rowBoundary f h p ∧
      fderiv ℝ (rectangleAverage f h) p (0,1) = colBoundary f h p :=
    hd.and (hr.and hc)
  have hdiag := DiagonalCoordinates.diagonal_preserving.quasiMeasurePreserving.ae hall
  have hsplit := Measure.ae_ae_of_ae_prod hdiag
  filter_upwards [hsplit] with s hs
  filter_upwards [hs] with u hu
  have hd' := hu.1.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_id u).prodMk ((hasDerivAt_id u).const_sub s))
  have he : ((1,-1) : Point) = (1,0)-(0,1) := by ext <;> norm_num
  have hv : fderiv ℝ (rectangleAverage f h) (u,s-u) (1,-1) =
      rowBoundary f h (u,s-u)-colBoundary f h (u,s-u) := by
    rw [he,map_sub]
    exact congrArg₂ (·-·) hu.2.1 hu.2.2
  change HasDerivAt (fun t => rectangleAverage f h (t,s-t))
    (fderiv ℝ (rectangleAverage f h) (u,s-u) (1,-1)) u at hd'
  rwa [hv] at hd'

/-- In the open inner square, zero extension changes none of the four
boundary integrals. -/
theorem boundary_eq_corner (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (p : Point)
    (hp : h < p.1 ∧ p.1 < 1-h ∧ h < p.2 ∧ p.2 < 1-h) :
    rowBoundary f h p-colBoundary f h p = cornerQuotient (zeroDifference f) h p := by
  rw [zero_corner_boundary_identity f hf h hh p hp]
  have hr (a : ℝ) (ha : a ∈ Ioc (0:ℝ) 1) : rowWindow f h p.2 a =
      ∫ t in Ioc (p.2-h) (p.2+h), spin (f (a,t)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht' : t ∈ Ioc (0:ℝ) 1 := ⟨by linarith [ht.1,hp.2.2.1],by linarith [ht.2,hp.2.2.2]⟩
    change SquareTranslation.zeroSquare f (a,t) = _
    unfold SquareTranslation.zeroSquare
    rw [indicator_of_mem (show (a,t) ∈ (Ioc (0:ℝ) 1) ×ˢ Ioc (0:ℝ) 1 from ⟨ha,ht'⟩)]
  have hc (a : ℝ) (ha : a ∈ Ioc (0:ℝ) 1) : rowWindow (swapColor f) h p.1 a =
      ∫ t in Ioc (p.1-h) (p.1+h), spin (f (t,a)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change SquareTranslation.zeroSquare (swapColor f) (a,t) = _
    rw [zeroSquare_swap]
    have ht' : t ∈ Ioc (0:ℝ) 1 := ⟨by linarith [ht.1,hp.1],by linarith [ht.2,hp.2.1]⟩
    unfold SquareTranslation.zeroSquare
    rw [indicator_of_mem (show (t,a) ∈ (Ioc (0:ℝ) 1) ×ˢ Ioc (0:ℝ) 1 from ⟨ht',ha⟩)]
  unfold rowBoundary colBoundary boundaryQuotient
  dsimp only [rowBoundary,Prod.swap]
  rw [hr (p.1+h) ⟨by linarith [hp.1],by linarith [hp.2.1]⟩,
    hr (p.1-h) ⟨by linarith [hp.1],by linarith [hp.2.1]⟩,
    hc (p.2+h) ⟨by linarith [hp.2.2.1],by linarith [hp.2.2.2]⟩,
    hc (p.2-h) ⟨by linarith [hp.2.2.1],by linarith [hp.2.2.2]⟩]
  ring

/-- The actual diagonal derivative equals the four-corner quotient on
almost every point of almost every interior diagonal. Endpoints are removed
using atomlessness; this also covers zero-length and empty fibers. -/
theorem rectangle_diagonal_corner_deriv (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) :
    ∀ᵐ s : ℝ, (fun u => deriv (fun t => rectangleAverage f h (t,s-t)) u) =ᵐ[
      volume.restrict (Icc (DiagonalCoordinates.lower h s) (DiagonalCoordinates.upper h s))]
      (fun u => cornerQuotient (zeroDifference f) h (u,s-u)) := by
  filter_upwards [rectangle_diagonal_ae_derivative f hf h hh] with s hs
  filter_upwards [ae_restrict_of_ae hs,ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (DiagonalCoordinates.lower h s)),
    ae_restrict_of_ae (volume.ae_ne (DiagonalCoordinates.upper h s))] with u hu hm hlo hhi
  have hu1 : DiagonalCoordinates.lower h s < u := lt_of_le_of_ne hm.1 (Ne.symm hlo)
  have hu2 : u < DiagonalCoordinates.upper h s := lt_of_le_of_ne hm.2 hhi
  have hp : h < u ∧ u < 1-h ∧ h < s-u ∧ s-u < 1-h := by
    have hl1 := le_max_left h (s-(1-h))
    have hl2 := le_max_right h (s-(1-h))
    have hr1 := min_le_left (1-h) (s-h)
    have hr2 := min_le_right (1-h) (s-h)
    dsimp only [DiagonalCoordinates.lower,DiagonalCoordinates.upper] at hu1 hu2
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  exact hu.deriv.trans (boundary_eq_corner f hf h hh (u,s-u) hp)

theorem rectangle_norm_le (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (p : Point) : |rectangleAverage f h p| ≤ 1 := by
  rw [←average_eq_rectangle f hf h hh p]
  have he := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := BoxAverage.boxMeasure h)
    (Filter.Eventually.of_forall (fun z => zeroSquare_norm_le f (z+p)))
  simpa only [probReal_univ,mul_one,Real.norm_eq_abs,BoxAverage.average] using he

theorem box_diagonal_ac (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (s a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun u => BoxAverage.average (BoxAverage.boxMeasure h) (SquareTranslation.zeroSquare f) (u,s-u)) a b := by
  simp_rw [average_eq_rectangle f hf h hh]
  exact rectangle_diagonal_ac f hf h hh s a b

theorem box_diagonal_corner_deriv (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) :
    ∀ᵐ s : ℝ, (fun u => deriv (fun t =>
      BoxAverage.average (BoxAverage.boxMeasure h) (SquareTranslation.zeroSquare f) (t,s-t)) u) =ᵐ[
      volume.restrict (Icc (DiagonalCoordinates.lower h s) (DiagonalCoordinates.upper h s))]
      (fun u => cornerQuotient (zeroDifference f) h (u,s-u)) := by
  simp_rw [average_eq_rectangle f hf h hh]
  exact rectangle_diagonal_corner_deriv f hf h hh

/-- Actual L1-L2 comparison on the probability square, proved by integrating
the nonnegative square around the mean absolute value. -/
theorem operatorDifference_L1_sq_le (f : Point → Bool) (hf : Measurable f) :
    (∫ p, |operatorDifference f p| ∂unit.prod unit)^2 ≤ differenceSq unit f := by
  have hD : Integrable (operatorDifference f) (unit.prod unit) :=
    Integrable.of_bound (operatorDifference_measurable f hf).aestronglyMeasurable 2
      (Filter.Eventually.of_forall (fun p => by
        have ht := norm_sub_le (rowOp unit f p) (colOp unit f p)
        have hr := rowOp_norm_le unit f p
        have hc := colOp_norm_le unit f p
        change ‖rowOp unit f p-colOp unit f p‖ ≤ 2
        linarith))
  have hD2 : Integrable (fun p => (operatorDifference f p)^2) (unit.prod unit) := by
    have hR := rowSq_integrable unit f hf
    have hC := colSq_integrable unit f hf
    have hI := inner_integrable unit f hf
    have hs := (hR.add hC).sub (hI.const_mul 2)
    apply hs.congr
    filter_upwards [] with p
    dsimp [operatorDifference]
    ring
  let a := ∫ p, |operatorDifference f p| ∂unit.prod unit
  have hlin : Integrable (fun p => 2*a*|operatorDifference f p|-a^2) (unit.prod unit) :=
    (hD.abs.const_mul (2*a)).sub (integrable_const _)
  calc
    _ = ∫ p, 2*a*|operatorDifference f p|-a^2 ∂unit.prod unit := by
      rw [integral_sub (hD.abs.const_mul _) (integrable_const _),integral_const_mul]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      change a^2 = 2*a*a-a^2
      ring
    _ ≤ ∫ p, (operatorDifference f p)^2 ∂unit.prod unit := by
      apply integral_mono hlin hD2
      intro p
      dsimp only [Pi.sub_apply]
      nlinarith [sq_nonneg (|operatorDifference f p|-a),sq_abs (operatorDifference f p)]
    _ = differenceSq unit f := rfl

/-- With h⁶ energy excess, the actual four-corner quotient has L1 cost ≤2h. -/
theorem operator_corner_small_energy (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (hE : energy unit f ≤ 1/12+h^6) (S : Set Point) :
    (∫ p in S, |cornerQuotient (zeroDifference f) h p|) ≤ 2*h := by
  have hs := operatorDifference_L1_sq_le f hf
  have hdef := (deficit_bounds unit f hf (h^6) hE).2.1
  have hL : (∫ p, |operatorDifference f p| ∂unit.prod unit) ≤ 4*h^3 := by
    have hr : 0 ≤ 4*h^3 := by positivity
    nlinarith [sq_nonneg ((∫ p, |operatorDifference f p| ∂unit.prod unit)+4*h^3)]
  calc
    _ ≤ (∫ p, |operatorDifference f p| ∂unit.prod unit)/(2*h^2) :=
      operator_corner_L1_bound f hf h hh S
    _ ≤ (4*h^3)/(2*h^2) := (div_le_div_iff_of_pos_right (by positivity : 0 < 2*h^2)).2 hL
    _ = 2*h := by field_simp; ring

/-- The genuine box smoothing has a measurable diagonal mean and total
interior L1 deviation at most 2h under h⁶ excess. No derivative or AC
hypothesis remains in this instantiated theorem. -/
theorem box_diagonal_poincare (f : Point → Bool) (hf : Measurable f)
    (h : ℝ) (hh : 0 < h) (hE : energy unit f ≤ 1/12+h^6) :
    (∫ p in DiagonalCoordinates.interior h,
      |BoxAverage.average (BoxAverage.boxMeasure h) (SquareTranslation.zeroSquare f) p-
        DiagonalAverage.lineMean
          (BoxAverage.average (BoxAverage.boxMeasure h) (SquareTranslation.zeroSquare f))
          h (p.1+p.2)|) ≤ 2*h := by
  have hK : IntegrableOn (cornerQuotient (zeroDifference f) h) (DiagonalCoordinates.interior h) :=
    ((cornerDifference_integrable _ (zeroDifference_integrable f hf) h).div_const (8*h^2)).integrableOn
  have hG : Measurable (BoxAverage.average (BoxAverage.boxMeasure h) (SquareTranslation.zeroSquare f)) := by
    have he : BoxAverage.average (BoxAverage.boxMeasure h) (SquareTranslation.zeroSquare f) =
        rectangleAverage f h := funext (average_eq_rectangle f hf h hh)
    rw [he]
    exact (rectangle_lipschitz f hf h hh).continuous.measurable
  have hb : ∀ p ∈ DiagonalCoordinates.interior h,
      |BoxAverage.average (BoxAverage.boxMeasure h) (SquareTranslation.zeroSquare f) p| ≤ 1 := by
    intro p _
    rw [average_eq_rectangle f hf h hh p]
    exact rectangle_norm_le f hf h hh p
  exact (DiagonalAverage.diagonal_poincare _ _ h hh.le hG hb hK
    (Filter.Eventually.of_forall (fun s => box_diagonal_ac f hf h hh s _ _))
    (box_diagonal_corner_deriv f hf h hh)).trans
      (operator_corner_small_energy f hf h hh hE _)

end Q4.Candidate.BoxDerivative

#print axioms Q4.Candidate.BoxDerivative.cmp_increment
#print axioms Q4.Candidate.BoxDerivative.transform_increment
#print axioms Q4.Candidate.BoxDerivative.rectangle_identity

#print axioms Q4.Candidate.BoxDerivative.cornerQuotient_L1_bound
#print axioms Q4.Candidate.BoxDerivative.operator_corner_L1_bound
#print axioms Q4.Candidate.BoxDerivative.corner_boundary_identity
#print axioms Q4.Candidate.BoxDerivative.zero_corner_boundary_identity

#print axioms Q4.Candidate.BoxDerivative.moving_interval_ae_derivative
#print axioms Q4.Candidate.BoxDerivative.operatorDifference_L1_sq_le
#print axioms Q4.Candidate.BoxDerivative.operator_corner_small_energy

#print axioms Q4.Candidate.BoxDerivative.average_eq_rectangle
#print axioms Q4.Candidate.BoxDerivative.rectangle_row_ae_derivative

#print axioms Q4.Candidate.BoxDerivative.rectangle_lipschitz
#print axioms Q4.Candidate.BoxDerivative.rectangle_col_ae_derivative

#print axioms Q4.Candidate.BoxDerivative.rectangle_diagonal_ac
#print axioms Q4.Candidate.BoxDerivative.rectangle_fderiv_row
#print axioms Q4.Candidate.BoxDerivative.rectangle_fderiv_col

#print axioms Q4.Candidate.BoxDerivative.rectangle_diagonal_ae_derivative
#print axioms Q4.Candidate.BoxDerivative.boundary_eq_corner

#print axioms Q4.Candidate.BoxDerivative.rectangle_diagonal_corner_deriv
#print axioms Q4.Candidate.BoxDerivative.box_diagonal_ac
#print axioms Q4.Candidate.BoxDerivative.box_diagonal_corner_deriv

#print axioms Q4.Candidate.BoxDerivative.box_diagonal_poincare
