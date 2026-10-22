import Q4.SimultaneousFlip

/-!
Joint change-of-internal-state and one-bridge-flip bounds, from actual finite
same-color pair counts. All objectives are doubled; no integer division occurs.
Every listed interaction occurrence is counted, including repeated pairs.
The bridge list is duplicate-free and the interaction list has no loops.
The geometric neighborhood-difference bound is an explicit external interface.
-/

namespace Q4.JointProbe

open Q4.SimultaneousFlip (intSum intSum_zero intSum_add intSum_sub intSum_congr
  intSum_point same flipOne edgeEnergy_eq_monoCount)

variable {α : Type u} {β : Type v} {σ : Type w}

def spin (b : Bool) : Int := if b then 1 else -1

def absZ (x : Int) : Int := if 0 ≤ x then x else -x

theorem absZ_nonneg (x : Int) : 0 ≤ absZ x := by
  unfold absZ; split <;> omega

theorem absZ_le_iff (x D : Int) : absZ x ≤ D ↔ -D ≤ x ∧ x ≤ D := by
  unfold absZ; split <;> omega

theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> rfl

theorem intSum_mul_left (xs : List α) (k : Int) (f : α → Int) :
    intSum xs (fun x => k * f x) = k * intSum xs f := by
  induction xs with
  | nil => simp [intSum]
  | cons x xs ih => simp only [intSum, ih, Int.mul_add]

theorem intSum_neg (xs : List α) (f : α → Int) :
    intSum xs (fun x => -f x) = -intSum xs f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [intSum, ih]; omega

/-- Arbitrary integral coefficients are the sum of the endpoint fields. -/
def bridgeEnergy (vs : List α) (es : List (α × α))
    (a : α → Int) (χ : α → Bool) : Int :=
  2 * (Q4.monoCount es χ : Int) + intSum vs (fun v => a v * spin (χ v))

/-- The field part of the difference, before any bridge is flipped. -/
def fieldDifference (vs : List α) (a b : α → Int) (χ : α → Bool) : Int :=
  intSum vs (fun v => (b v - a v) * spin (χ v))

theorem bridgeEnergy_change_field (vs : List α) (es : List (α × α))
    (a b : α → Int) (χ : α → Bool) :
    bridgeEnergy vs es b χ - bridgeEnergy vs es a χ = fieldDifference vs a b χ := by
  have h := intSum_sub vs (fun v => b v * spin (χ v))
    (fun v => a v * spin (χ v))
  simp only [← Int.sub_mul] at h
  unfold bridgeEnergy fieldDifference
  omega

variable [DecidableEq α]

/-- Incidence sum over the real pair list; both orientations are supported. -/
def neighborhood (es : List (α × α)) (χ : α → Bool) (v : α) : Int :=
  intSum es (fun e =>
    (if v = e.1 then spin (χ e.2) else 0) +
    (if v = e.2 then spin (χ e.1) else 0))

/-- This is the undoubled local fee, proved below to be the actual change. -/
def singleFee (es : List (α × α)) (a : α → Int) (χ : α → Bool) (v : α) : Int :=
  -spin (χ v) * (neighborhood es χ v + a v)

theorem pair_single_spin (χ : α → Bool) (v x y : α) (hxy : x ≠ y) :
    same (flipOne χ v x) (flipOne χ v y) - same (χ x) (χ y) =
      -spin (χ v) * ((if v = x then spin (χ y) else 0) +
        (if v = y then spin (χ x) else 0)) := by
  by_cases hvx : v = x
  · subst x
    simp only [flipOne, ite_true, Ne.symm hxy, ite_false, hxy]
    cases χ v <;> cases χ y <;> decide
  · by_cases hvy : v = y
    · subst y
      simp only [flipOne, ite_true, Ne.symm hvx, ite_false, hvx]
      cases χ x <;> cases χ v <;> decide
    · simp [flipOne, hvx, hvy, Ne.symm hvx, Ne.symm hvy]

theorem monoCount_single_difference (es : List (α × α)) (χ : α → Bool) (v : α)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    (Q4.monoCount es (flipOne χ v) : Int) - (Q4.monoCount es χ : Int) =
      -spin (χ v) * neighborhood es χ v := by
  rw [← edgeEnergy_eq_monoCount, ← edgeEnergy_eq_monoCount, ← intSum_sub]
  have h := intSum_congr es
    (fun e => same (flipOne χ v e.1) (flipOne χ v e.2) - same (χ e.1) (χ e.2))
    (fun e => -spin (χ v) * ((if v = e.1 then spin (χ e.2) else 0) +
      (if v = e.2 then spin (χ e.1) else 0)))
    (fun e he => pair_single_spin χ v e.1 e.2 (hloop e he))
  rw [h, intSum_mul_left]
  rfl

theorem field_single_difference (vs : List α) (a : α → Int) (χ : α → Bool)
    (v : α) (hn : vs.Nodup) (hv : v ∈ vs) :
    intSum vs (fun x => a x * spin (flipOne χ v x)) -
      intSum vs (fun x => a x * spin (χ x)) = -2 * spin (χ v) * a v := by
  rw [← intSum_sub]
  have h := intSum_congr vs
    (fun x => a x * spin (flipOne χ v x) - a x * spin (χ x))
    (fun x => if x = v then -2 * spin (χ v) * a v else 0) (by
      intro x _
      by_cases hx : x = v
      · subst x
        cases hcv : χ v <;> simp [flipOne, spin, hcv, Int.mul_neg, Int.neg_mul] <;> omega
      · simp [flipOne, hx])
  rw [h, intSum_point vs v _ hn hv]

/-- Exact single-flip accounting, derived from all same-color pair occurrences. -/
theorem bridgeEnergy_single_difference (vs : List α) (es : List (α × α))
    (a : α → Int) (χ : α → Bool) (v : α) (hn : vs.Nodup) (hv : v ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    bridgeEnergy vs es a (flipOne χ v) - bridgeEnergy vs es a χ =
      2 * singleFee es a χ v := by
  have hm := monoCount_single_difference es χ v hloop
  have hf := field_single_difference vs a χ v hn hv
  unfold bridgeEnergy singleFee
  cases hcv : χ v <;> simp only [spin, hcv, Bool.false_eq_true, ite_false, ite_true,
    Int.neg_neg, Int.neg_mul, Int.one_mul, Int.mul_add] at * <;> omega

/-- The new field is used when charging the flip; the mixed term is explicit. -/
theorem bridgeEnergy_joint_difference (vs : List α) (es : List (α × α))
    (a b : α → Int) (χ : α → Bool) (v : α) (hn : vs.Nodup) (hv : v ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    bridgeEnergy vs es b (flipOne χ v) - bridgeEnergy vs es a χ =
      fieldDifference vs a b χ + 2 * singleFee es a χ v -
        2 * spin (χ v) * (b v - a v) := by
  have hs := bridgeEnergy_single_difference vs es b χ v hn hv hloop
  have hc := bridgeEnergy_change_field vs es a b χ
  unfold singleFee at *
  cases hcv : χ v <;> simp only [spin, hcv, Bool.false_eq_true, ite_false, ite_true,
    Int.neg_neg, Int.neg_mul, Int.one_mul, Int.mul_add, Int.mul_sub] at * <;> omega

/-- Scalar form of the soft-pair argument; the neighborhood bound is external. -/
theorem soft_fees_bound (es : List (α × α)) (a : α → Int) (χ : α → Bool)
    (p m : α) (D : Int) (hp : χ p = true) (hm : χ m = false)
    (ha : a p = a m) (hD : absZ (neighborhood es χ p - neighborhood es χ m) ≤ D)
    (hpos : 0 ≤ singleFee es a χ p) (hneg : 0 ≤ singleFee es a χ m) :
    0 ≤ singleFee es a χ p ∧ singleFee es a χ p ≤ D ∧
    0 ≤ singleFee es a χ m ∧ singleFee es a χ m ≤ D := by
  have hd := (absZ_le_iff _ _).mp hD
  simp only [singleFee, hp, hm, spin, ite_true, Bool.false_eq_true, ite_false,
    Int.neg_neg, Int.neg_mul, Int.one_mul] at *
  omega

/-- An arbitrary internal state has its actual internal cost and endpoint field. -/
def stateEnergy (vs : List α) (es : List (α × α)) (I : σ → Int)
    (A : σ → α → Int) (s : σ) (χ : α → Bool) : Int :=
  2 * I s + bridgeEnergy vs es (A s) χ

/-- All competitor states and bridge colorings are covered by the minimum. -/
def GlobalMinimum (vs : List α) (es : List (α × α)) (I : σ → Int)
    (A : σ → α → Int) (s : σ) (χ : α → Bool) : Prop :=
  ∀ t ψ, stateEnergy vs es I A s χ ≤ stateEnergy vs es I A t ψ

theorem global_single_nonnegative (vs : List α) (es : List (α × α))
    (I : σ → Int) (A : σ → α → Int) (s : σ) (χ : α → Bool)
    (v : α) (hn : vs.Nodup) (hv : v ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hmin : GlobalMinimum vs es I A s χ) :
    0 ≤ singleFee es (A s) χ v := by
  have h := hmin s (flipOne χ v)
  have he := bridgeEnergy_single_difference vs es (A s) χ v hn hv hloop
  unfold stateEnergy at h
  omega

/-- R112 (5), with doubled energy and arbitrary internal cost difference. -/
theorem global_joint_probe (vs : List α) (es : List (α × α))
    (I : σ → Int) (A : σ → α → Int) (s t : σ) (χ : α → Bool)
    (p m : α) (D : Int) (hn : vs.Nodup) (hvp : p ∈ vs) (hvm : m ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hmin : GlobalMinimum vs es I A s χ)
    (hp : χ p = true) (hm : χ m = false) (ha : A s p = A s m)
    (hb : A t p - A s p = A t m - A s m)
    (hD : absZ (neighborhood es χ p - neighborhood es χ m) ≤ D) :
    2 * (I t - I s) + fieldDifference vs (A s) (A t) χ ≥
      2 * absZ (A t p - A s p) - 2 * D := by
  have hsp := global_single_nonnegative vs es I A s χ p hn hvp hloop hmin
  have hsm := global_single_nonnegative vs es I A s χ m hn hvm hloop hmin
  have hf := soft_fees_bound es (A s) χ p m D hp hm ha hD hsp hsm
  have hjp := bridgeEnergy_joint_difference vs es (A s) (A t) χ p hn hvp hloop
  have hjm := bridgeEnergy_joint_difference vs es (A s) (A t) χ m hn hvm hloop
  have hmp := hmin t (flipOne χ p)
  have hmm := hmin t (flipOne χ m)
  unfold stateEnergy at hmp hmm
  simp only [hp, hm, spin, ite_true, Bool.false_eq_true, ite_false] at hjp hjm
  unfold absZ
  split <;> omega


/-! The following layer derives the field vector from actual internal spins.
    Other cores are held fixed in `ext`; no assumption about their size is used. -/

omit [DecidableEq α] in
theorem intSum_mul_right (xs : List α) (f : α → Int) (k : Int) :
    intSum xs (fun x => f x * k) = intSum xs f * k := by
  simpa only [Int.mul_comm] using intSum_mul_left xs k f

/-- Incidence is explicitly 0/1. More than one selected port is permitted. -/
def readerField (ports : List β) (read : α → β → Bool) (c : β → Int) (e : α) : Int :=
  intSum ports (fun u => if read e u then c u else 0)

def portStar (vs : List α) (read : α → β → Bool) (χ : α → Bool) (u : β) : Int :=
  intSum vs (fun e => if read e u then spin (χ e) else 0)

def fieldDot (ports : List β) (c S : β → Int) : Int :=
  intSum ports (fun u => c u * S u)

omit [DecidableEq α] in
/-- The field pairing is exactly the dot product with the actual bridge stars. -/
theorem readerField_pairing (vs : List α) (ports : List β)
    (read : α → β → Bool) (c : β → Int) (χ : α → Bool) :
    intSum vs (fun e => readerField ports read c e * spin (χ e)) =
      fieldDot ports c (portStar vs read χ) := by
  have h := intSum_congr vs
    (fun e => readerField ports read c e * spin (χ e))
    (fun e => intSum ports (fun u => c u * (if read e u then spin (χ e) else 0)))
    (by
      intro e _
      unfold readerField
      rw [← intSum_mul_right]
      apply intSum_congr
      intro u _
      cases read e u <;> simp)
  rw [h, Q4.SimultaneousFlip.intSum_swap]
  unfold fieldDot portStar
  apply intSum_congr
  intro u _
  exact intSum_mul_left vs (c u) _

omit [DecidableEq α] in
theorem readerField_neg (ports : List β) (read : α → β → Bool) (c : β → Int) (e : α) :
    readerField ports read (fun u => -c u) e = -readerField ports read c e := by
  unfold readerField
  rw [← intSum_neg]
  apply intSum_congr
  intro u _
  cases read e u <;> simp

/-- Port cuts are finite lists of the actual internal edge variables. -/
def cutField {γ : Type z} (cuts : β → List γ) (ξ : γ → Bool) (u : β) : Int :=
  intSum (cuts u) (fun x => spin (ξ x))

def complement {γ : Type z} (ξ : γ → Bool) (x : γ) : Bool := !(ξ x)

theorem cutField_complement {γ : Type z} (cuts : β → List γ) (ξ : γ → Bool) (u : β) :
    cutField cuts (complement ξ) u = -cutField cuts ξ u := by
  unfold cutField complement
  simp only [spin_not]
  exact intSum_neg _ _

/-- Internal cost is an actual monochromatic-pair count. -/
def internalCost {γ : Type z} (pairs : List (γ × γ)) (ξ : γ → Bool) : Int :=
  (Q4.monoCount pairs ξ : Int)

theorem internalCost_complement {γ : Type z} (pairs : List (γ × γ)) (ξ : γ → Bool) :
    internalCost pairs (complement ξ) = internalCost pairs ξ := by
  unfold internalCost
  congr 1
  induction pairs with
  | nil => rfl
  | cons e pairs ih =>
    simp only [Q4.monoCount]
    have he : (if (complement ξ e.1) = (complement ξ e.2) then 1 else 0 : Nat) =
        (if ξ e.1 = ξ e.2 then 1 else 0 : Nat) := by
      cases h₁ : ξ e.1 <;> cases h₂ : ξ e.2 <;> simp [complement, h₁, h₂]
    rw [he, ih]

def cutCoefficient {γ : Type z} (ports : List β) (read : α → β → Bool)
    (cuts : β → List γ) (ext : α → Int) (ξ : γ → Bool) (e : α) : Int :=
  ext e + readerField ports read (cutField cuts ξ) e

omit [DecidableEq α] in
theorem cutCoefficient_complement {γ : Type z} (ports : List β)
    (read : α → β → Bool) (cuts : β → List γ) (ext : α → Int)
    (ξ : γ → Bool) (e : α) :
    cutCoefficient ports read cuts ext (complement ξ) e =
      ext e - readerField ports read (cutField cuts ξ) e := by
  unfold cutCoefficient
  have h : (cutField cuts (complement ξ)) = (fun u => -cutField cuts ξ u) := by
    funext u
    exact cutField_complement cuts ξ u
  rw [h, readerField_neg]
  omega

omit [DecidableEq α] in
/-- Full field change under complement, with every bridge occurrence retained. -/
theorem complement_fieldDifference {γ : Type z} (vs : List α) (ports : List β)
    (read : α → β → Bool) (cuts : β → List γ) (ext : α → Int)
    (ξ : γ → Bool) (χ : α → Bool) :
    fieldDifference vs (cutCoefficient ports read cuts ext ξ)
      (cutCoefficient ports read cuts ext (complement ξ)) χ =
      -2 * fieldDot ports (cutField cuts ξ) (portStar vs read χ) := by
  have h := intSum_congr vs
    (fun e => (cutCoefficient ports read cuts ext (complement ξ) e -
      cutCoefficient ports read cuts ext ξ e) * spin (χ e))
    (fun e => -2 * (readerField ports read (cutField cuts ξ) e * spin (χ e)))
    (by
      intro e _
      rw [cutCoefficient_complement]
      unfold cutCoefficient
      have he : ext e - readerField ports read (cutField cuts ξ) e -
          (ext e + readerField ports read (cutField cuts ξ) e) =
          -2 * readerField ports read (cutField cuts ξ) e := by omega
      rw [he, Int.mul_assoc])
  unfold fieldDifference
  rw [h, intSum_mul_left, readerField_pairing]

omit [DecidableEq α] in
theorem cutCoefficient_equal_readers {γ : Type z} (ports : List β)
    (read : α → β → Bool) (cuts : β → List γ) (ext : α → Int)
    (ξ : γ → Bool) (p m : α) (hext : ext p = ext m)
    (hread : ∀ u, u ∈ ports → read p u = read m u) :
    cutCoefficient ports read cuts ext ξ p = cutCoefficient ports read cuts ext ξ m := by
  unfold cutCoefficient readerField
  rw [hext]
  congr 1
  apply intSum_congr
  intro u hu
  rw [hread u hu]

theorem absZ_neg_two (x : Int) : absZ (-2 * x) = 2 * absZ x := by
  unfold absZ
  split <;> split <;> omega

/-- R112 (6), from actual internal and bridge pair counts and cut spin fields.
    The geometry supplies only the list interpretation, equal soft readers,
    equal external endpoint fields, and the explicit neighborhood bound. -/
theorem cut_global_complement_probe {γ : Type z} (vs : List α)
    (es : List (α × α)) (pairs : List (γ × γ)) (ports : List β)
    (read : α → β → Bool) (cuts : β → List γ) (ext : α → Int)
    (ξ : γ → Bool) (χ : α → Bool) (p m : α) (D : Int)
    (hn : vs.Nodup) (hvp : p ∈ vs) (hvm : m ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hmin : GlobalMinimum vs es (internalCost pairs)
      (cutCoefficient ports read cuts ext) ξ χ)
    (hp : χ p = true) (hm : χ m = false) (hext : ext p = ext m)
    (hread : ∀ u, u ∈ ports → read p u = read m u)
    (hD : absZ (neighborhood es χ p - neighborhood es χ m) ≤ D) :
    -fieldDot ports (cutField cuts ξ) (portStar vs read χ) ≥
      2 * absZ (readerField ports read (cutField cuts ξ) p) - D := by
  have ha := cutCoefficient_equal_readers ports read cuts ext ξ p m hext hread
  have hb := cutCoefficient_equal_readers ports read cuts ext (complement ξ) p m hext hread
  have h := global_joint_probe vs es (internalCost pairs)
    (cutCoefficient ports read cuts ext) ξ (complement ξ) χ p m D
    hn hvp hvm hloop hmin hp hm ha (by omega) hD
  rw [internalCost_complement, complement_fieldDifference, cutCoefficient_complement] at h
  have hd : ext p - readerField ports read (cutField cuts ξ) p -
      cutCoefficient ports read cuts ext ξ p =
      -2 * readerField ports read (cutField cuts ξ) p := by
    unfold cutCoefficient
    omega
  rw [hd, absZ_neg_two] at h
  omega

omit [DecidableEq α] in
/-- A geometric bridge reading one port recovers exactly that port's field. -/
theorem readerField_single_port [DecidableEq β] (ports : List β)
    (read : α → β → Bool) (c : β → Int) (e : α) (u : β)
    (hn : ports.Nodup) (hu : u ∈ ports)
    (hread : ∀ v, v ∈ ports → read e v = decide (v = u)) :
    readerField ports read c e = c u := by
  unfold readerField
  have h := intSum_congr ports
    (fun v => if read e v then c v else 0)
    (fun v => if v = u then c u else 0) (by
      intro v hv
      rw [hread v hv]
      by_cases h : v = u
      · subst v; simp
      · simp [h])
  rw [h, intSum_point ports u _ hn hu]


omit [DecidableEq α] in
theorem readerField_sub (ports : List β) (read : α → β → Bool)
    (a b : β → Int) (e : α) :
    readerField ports read (fun u => b u - a u) e =
      readerField ports read b e - readerField ports read a e := by
  unfold readerField
  rw [← intSum_sub]
  apply intSum_congr
  intro u _
  cases read e u <;> simp

omit [DecidableEq α] in
/-- Arbitrary internal recoloring yields the exact vector delta dotted with S. -/
theorem cut_fieldDifference {γ : Type z} (vs : List α) (ports : List β)
    (read : α → β → Bool) (cuts : β → List γ) (ext : α → Int)
    (ξ ζ : γ → Bool) (χ : α → Bool) :
    fieldDifference vs (cutCoefficient ports read cuts ext ξ)
      (cutCoefficient ports read cuts ext ζ) χ =
      fieldDot ports (fun u => cutField cuts ζ u - cutField cuts ξ u) (portStar vs read χ) := by
  have h := intSum_congr vs
    (fun e => (cutCoefficient ports read cuts ext ζ e -
      cutCoefficient ports read cuts ext ξ e) * spin (χ e))
    (fun e => readerField ports read (fun u => cutField cuts ζ u - cutField cuts ξ u) e *
      spin (χ e)) (by
        intro e _
        rw [readerField_sub]
        unfold cutCoefficient
        congr 1
        omega)
  unfold fieldDifference
  rw [h, readerField_pairing]

/-- Actual cut-field version of R112 (5), for every competing internal coloring.
    The conclusion is twice δI + (b-a)·S/2 ≥ |b_u-a_u| - D. -/
theorem cut_global_joint_probe {γ : Type z} [DecidableEq β] (vs : List α)
    (es : List (α × α)) (pairs : List (γ × γ)) (ports : List β)
    (read : α → β → Bool) (cuts : β → List γ) (ext : α → Int)
    (ξ ζ : γ → Bool) (χ : α → Bool) (p m : α) (u : β) (D : Int)
    (hn : vs.Nodup) (hvp : p ∈ vs) (hvm : m ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hmin : GlobalMinimum vs es (internalCost pairs)
      (cutCoefficient ports read cuts ext) ξ χ)
    (hp : χ p = true) (hm : χ m = false) (hext : ext p = ext m)
    (hread : ∀ v, v ∈ ports → read p v = read m v)
    (hports : ports.Nodup) (hu : u ∈ ports)
    (hport : ∀ v, v ∈ ports → read p v = decide (v = u))
    (hD : absZ (neighborhood es χ p - neighborhood es χ m) ≤ D) :
    2 * (internalCost pairs ζ - internalCost pairs ξ) +
      fieldDot ports (fun v => cutField cuts ζ v - cutField cuts ξ v) (portStar vs read χ) ≥
      2 * absZ (cutField cuts ζ u - cutField cuts ξ u) - 2 * D := by
  have ha := cutCoefficient_equal_readers ports read cuts ext ξ p m hext hread
  have hb := cutCoefficient_equal_readers ports read cuts ext ζ p m hext hread
  have h := global_joint_probe vs es (internalCost pairs)
    (cutCoefficient ports read cuts ext) ξ ζ χ p m D
    hn hvp hvm hloop hmin hp hm ha (by omega) hD
  rw [cut_fieldDifference] at h
  have hpa := readerField_single_port ports read (cutField cuts ξ) p u hports hu hport
  have hpb := readerField_single_port ports read (cutField cuts ζ) p u hports hu hport
  have hd : cutCoefficient ports read cuts ext ζ p - cutCoefficient ports read cuts ext ξ p =
      cutField cuts ζ u - cutField cuts ξ u := by
    unfold cutCoefficient
    rw [hpa, hpb]
    omega
  rw [hd] at h
  exact h

/-- Single-port complement corollary: -a·S ≥ 2|a_u| - D. -/
theorem cut_global_single_port_complement {γ : Type z} [DecidableEq β] (vs : List α)
    (es : List (α × α)) (pairs : List (γ × γ)) (ports : List β)
    (read : α → β → Bool) (cuts : β → List γ) (ext : α → Int)
    (ξ : γ → Bool) (χ : α → Bool) (p m : α) (u : β) (D : Int)
    (hn : vs.Nodup) (hvp : p ∈ vs) (hvm : m ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hmin : GlobalMinimum vs es (internalCost pairs)
      (cutCoefficient ports read cuts ext) ξ χ)
    (hp : χ p = true) (hm : χ m = false) (hext : ext p = ext m)
    (hread : ∀ v, v ∈ ports → read p v = read m v)
    (hports : ports.Nodup) (hu : u ∈ ports)
    (hport : ∀ v, v ∈ ports → read p v = decide (v = u))
    (hD : absZ (neighborhood es χ p - neighborhood es χ m) ≤ D) :
    -fieldDot ports (cutField cuts ξ) (portStar vs read χ) ≥
      2 * absZ (cutField cuts ξ u) - D := by
  have h := cut_global_complement_probe vs es pairs ports read cuts ext ξ χ p m D
    hn hvp hvm hloop hmin hp hm hext hread hD
  rw [readerField_single_port ports read (cutField cuts ξ) p u hports hu hport] at h
  exact h

end Q4.JointProbe

#print axioms Q4.JointProbe.absZ_nonneg
#print axioms Q4.JointProbe.absZ_le_iff
#print axioms Q4.JointProbe.spin_not
#print axioms Q4.JointProbe.intSum_mul_left
#print axioms Q4.JointProbe.intSum_neg
#print axioms Q4.JointProbe.bridgeEnergy_change_field
#print axioms Q4.JointProbe.pair_single_spin
#print axioms Q4.JointProbe.monoCount_single_difference
#print axioms Q4.JointProbe.field_single_difference
#print axioms Q4.JointProbe.bridgeEnergy_single_difference
#print axioms Q4.JointProbe.bridgeEnergy_joint_difference
#print axioms Q4.JointProbe.soft_fees_bound
#print axioms Q4.JointProbe.global_single_nonnegative
#print axioms Q4.JointProbe.global_joint_probe
#print axioms Q4.JointProbe.intSum_mul_right
#print axioms Q4.JointProbe.readerField_pairing
#print axioms Q4.JointProbe.readerField_neg
#print axioms Q4.JointProbe.cutField_complement
#print axioms Q4.JointProbe.internalCost_complement
#print axioms Q4.JointProbe.cutCoefficient_complement
#print axioms Q4.JointProbe.complement_fieldDifference
#print axioms Q4.JointProbe.cutCoefficient_equal_readers
#print axioms Q4.JointProbe.absZ_neg_two
#print axioms Q4.JointProbe.cut_global_complement_probe
#print axioms Q4.JointProbe.readerField_single_port
#print axioms Q4.JointProbe.readerField_sub
#print axioms Q4.JointProbe.cut_fieldDifference
#print axioms Q4.JointProbe.cut_global_joint_probe
#print axioms Q4.JointProbe.cut_global_single_port_complement
