import Q4.Counting

/-!
Exact finite-energy accounting for simultaneous Boolean flips.

The vertex list is duplicate-free and contains both endpoints of every listed
edge. Edges have distinct endpoints; repeated edge occurrences are allowed and
count with their multiplicity. Unary costs are arbitrary integers.

No grid neighborhood bound, distance-count estimate, or geometric realization
is assumed to have been established by this module.
-/

namespace Q4.SimultaneousFlip

variable {α : Type u} {β : Type v}

def intSum : List α → (α → Int) → Int
  | [], _ => 0
  | a :: as, f => f a + intSum as f

theorem intSum_zero (xs : List α) : intSum xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [intSum, ih]

theorem intSum_add (xs : List α) (f g : α → Int) :
    intSum xs (fun x => f x + g x) = intSum xs f + intSum xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [intSum, ih]; omega

theorem intSum_sub (xs : List α) (f g : α → Int) :
    intSum xs (fun x => f x - g x) = intSum xs f - intSum xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [intSum, ih]; omega

theorem intSum_congr (xs : List α) (f g : α → Int)
    (h : ∀ x, x ∈ xs → f x = g x) : intSum xs f = intSum xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [intSum]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem intSum_swap (xs : List α) (ys : List β) (f : α → β → Int) :
    intSum xs (fun x => intSum ys (f x)) =
      intSum ys (fun y => intSum xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [intSum, intSum_zero]
  | cons a xs ih =>
    simp only [intSum, ih]
    rw [← intSum_add]

variable [DecidableEq α]

theorem intSum_point_absent (xs : List α) (a : α) (w : Int) (ha : a ∉ xs) :
    intSum xs (fun x => if x = a then w else 0) = 0 := by
  apply Eq.trans (intSum_congr xs _ (fun _ => 0) ?_) (intSum_zero xs)
  intro x hx
  have hxa : x ≠ a := by intro h; subst x; exact ha hx
  simp [hxa]

theorem intSum_point (xs : List α) (a : α) (w : Int)
    (hn : xs.Nodup) (ha : a ∈ xs) :
    intSum xs (fun x => if x = a then w else 0) = w := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hba : b = a
    · subst b
      simp only [intSum, ite_true]
      rw [intSum_point_absent xs a w hn'.1]
      omega
    · simp only [intSum, hba, ite_false]
      have hax : a ∈ xs := by simpa [hba, Ne.symm hba] using ha
      rw [ih hn'.2 hax]
      omega

def same (a b : Bool) : Int := if a = b then 1 else 0

def flip (χ mask : α → Bool) (v : α) : Bool :=
  if mask v then !(χ v) else χ v

def flipOne (χ : α → Bool) (v x : α) : Bool :=
  if x = v then !(χ x) else χ x

def totalEnergy (vs : List α) (es : List (α × α))
    (unary : α → Bool → Int) (χ : α → Bool) : Int :=
  intSum vs (fun v => unary v (χ v)) +
    intSum es (fun e => same (χ e.1) (χ e.2))

omit [DecidableEq α] in
/-- The pair part agrees with the project's existing monochromatic count. -/
theorem edgeEnergy_eq_monoCount (es : List (α × α)) (χ : α → Bool) :
    intSum es (fun e => same (χ e.1) (χ e.2)) = (Q4.monoCount es χ : Int) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    simp only [intSum]
    rw [ih]
    by_cases hab : χ a = χ b <;>
      simp [same, Q4.monoCount, hab]

/-- This is an actual change of the entire energy, not an incidence proxy. -/
def singleDelta (vs : List α) (es : List (α × α))
    (unary : α → Bool → Int) (χ : α → Bool) (v : α) : Int :=
  totalEnergy vs es unary (flipOne χ v) - totalEnergy vs es unary χ

def unaryGain (unary : α → Bool → Int) (χ : α → Bool) (v : α) : Int :=
  unary v (!(χ v)) - unary v (χ v)

def leftGain (χ : α → Bool) (e : α × α) : Int :=
  same (!(χ e.1)) (χ e.2) - same (χ e.1) (χ e.2)

def rightGain (χ : α → Bool) (e : α × α) : Int :=
  same (χ e.1) (!(χ e.2)) - same (χ e.1) (χ e.2)

def selected (b : Bool) (w : Int) : Int := if b then w else 0

theorem selected_add (b : Bool) (x y : Int) :
    selected b (x + y) = selected b x + selected b y := by
  cases b <;> simp [selected]

theorem selected_sum (b : Bool) (xs : List β) (f : β → Int) :
    selected b (intSum xs f) = intSum xs (fun x => selected b (f x)) := by
  cases b <;> simp [selected, intSum_zero]

theorem selected_point (mask : α → Bool) (v a : α) (w : Int) :
    selected (mask v) (if v = a then w else 0) =
      if v = a then selected (mask a) w else 0 := by
  by_cases h : v = a
  · subst v; simp
  · simp [h, selected]

def correction (χ mask : α → Bool) (e : α × α) : Int :=
  if mask e.1 && mask e.2 then 4 * same (χ e.1) (χ e.2) - 2 else 0

/-- The two independently charged endpoint changes need exactly this correction. -/
theorem edge_flip_identity (a b p q : Bool) :
    same (if p then !a else a) (if q then !b else b) - same a b =
      selected p (same (!a) b - same a b) +
      selected q (same a (!b) - same a b) +
      (if p && q then 4 * same a b - 2 else 0) := by
  cases a <;> cases b <;> cases p <;> cases q <;> decide

theorem edge_single_identity (χ : α → Bool) (v a b : α) (hab : a ≠ b) :
    same (flipOne χ v a) (flipOne χ v b) - same (χ a) (χ b) =
      (if v = a then leftGain χ (a, b) else 0) +
      (if v = b then rightGain χ (a, b) else 0) := by
  by_cases hva : v = a
  · subst v
    simp [flipOne, hab, Ne.symm hab, leftGain]
  · by_cases hvb : v = b
    · subst v
      simp [flipOne, hab, Ne.symm hab, rightGain]
    · simp [flipOne, hva, hvb, Ne.symm hva, Ne.symm hvb]

theorem unary_single_identity (vs : List α) (unary : α → Bool → Int)
    (χ : α → Bool) (v : α) (hn : vs.Nodup) (hv : v ∈ vs) :
    intSum vs (fun x => unary x (flipOne χ v x)) -
      intSum vs (fun x => unary x (χ x)) = unaryGain unary χ v := by
  rw [← intSum_sub]
  have heq : intSum vs (fun x => unary x (flipOne χ v x) - unary x (χ x)) =
      intSum vs (fun x => if x = v then unaryGain unary χ v else 0) := by
    apply intSum_congr
    intro x _
    by_cases hx : x = v
    · subst x; simp [flipOne, unaryGain]
    · simp [flipOne, hx]
  rw [heq, intSum_point vs v (unaryGain unary χ v) hn hv]

theorem singleDelta_local (vs : List α) (es : List (α × α))
    (unary : α → Bool → Int) (χ : α → Bool) (v : α)
    (hn : vs.Nodup) (hv : v ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    singleDelta vs es unary χ v = unaryGain unary χ v +
      intSum es (fun e =>
        (if v = e.1 then leftGain χ e else 0) +
        (if v = e.2 then rightGain χ e else 0)) := by
  have hu := unary_single_identity vs unary χ v hn hv
  have he : intSum es (fun e => same (flipOne χ v e.1) (flipOne χ v e.2)) -
      intSum es (fun e => same (χ e.1) (χ e.2)) =
      intSum es (fun e =>
        (if v = e.1 then leftGain χ e else 0) +
        (if v = e.2 then rightGain χ e else 0)) := by
    rw [← intSum_sub]
    apply intSum_congr
    intro e he
    exact edge_single_identity χ v e.1 e.2 (hloop e he)
  unfold singleDelta totalEnergy
  omega

theorem sum_singleDelta (vs : List α) (es : List (α × α))
    (unary : α → Bool → Int) (χ mask : α → Bool)
    (hn : vs.Nodup)
    (hends : ∀ e, e ∈ es → e.1 ∈ vs ∧ e.2 ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    intSum vs (fun v => selected (mask v) (singleDelta vs es unary χ v)) =
      intSum vs (fun v => selected (mask v) (unaryGain unary χ v)) +
      intSum es (fun e => selected (mask e.1) (leftGain χ e) +
        selected (mask e.2) (rightGain χ e)) := by
  have hlocal := intSum_congr vs
    (fun v => selected (mask v) (singleDelta vs es unary χ v))
    (fun v => selected (mask v) (unaryGain unary χ v) +
      intSum es (fun e =>
        selected (mask v) (if v = e.1 then leftGain χ e else 0) +
        selected (mask v) (if v = e.2 then rightGain χ e else 0)))
    (by
      intro v hv
      rw [singleDelta_local vs es unary χ v hn hv hloop, selected_add, selected_sum]
      congr 1
      apply intSum_congr
      intro e _
      exact selected_add _ _ _)
  rw [hlocal, intSum_add, intSum_swap]
  congr 1
  apply intSum_congr
  intro e he
  simp only [selected_point, intSum_add]
  rw [intSum_point vs e.1 _ hn (hends e he).1,
      intSum_point vs e.2 _ hn (hends e he).2]

/-- Exact global accounting; every listed edge occurrence is charged once. -/
theorem totalEnergy_flip_identity (vs : List α) (es : List (α × α))
    (unary : α → Bool → Int) (χ mask : α → Bool)
    (hn : vs.Nodup)
    (hends : ∀ e, e ∈ es → e.1 ∈ vs ∧ e.2 ∈ vs)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    totalEnergy vs es unary (flip χ mask) - totalEnergy vs es unary χ =
      intSum vs (fun v => selected (mask v) (singleDelta vs es unary χ v)) +
      intSum es (correction χ mask) := by
  rw [sum_singleDelta vs es unary χ mask hn hends hloop]
  have hu : intSum vs (fun v => unary v (flip χ mask v)) -
      intSum vs (fun v => unary v (χ v)) =
      intSum vs (fun v => selected (mask v) (unaryGain unary χ v)) := by
    rw [← intSum_sub]
    apply intSum_congr
    intro v _
    cases h : mask v <;> simp [flip, selected, unaryGain, h]
  have he : intSum es (fun e => same (flip χ mask e.1) (flip χ mask e.2)) -
      intSum es (fun e => same (χ e.1) (χ e.2)) =
      intSum es (fun e => selected (mask e.1) (leftGain χ e) +
        selected (mask e.2) (rightGain χ e)) + intSum es (correction χ mask) := by
    rw [← intSum_sub, ← intSum_add]
    apply intSum_congr
    intro e _
    exact edge_flip_identity (χ e.1) (χ e.2) (mask e.1) (mask e.2)
  unfold totalEnergy
  omega

end Q4.SimultaneousFlip
