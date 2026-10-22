import Q4.SimultaneousFlip

/-!
Finite colour-objective verification of the candidate §5.

`blowEnergy` explicitly sums every pair of copies for every listed source edge.
The source is loop-free; repeated edges and repeated entries in the copy list
are allowed and are counted with their multiplicities.  No geometric
realisation, palette forcing, or rank-correction statement is asserted here.
-/

namespace Q4.Candidate.CoreEncoding
open Q4.SimultaneousFlip

variable {α : Type u} {β : Type v}

theorem sum_le (xs : List α) (f g : α → Int)
    (h : ∀ a, a ∈ xs → f a ≤ g a) : intSum xs f ≤ intSum xs g := by
  induction xs with
  | nil => exact Int.le_refl _
  | cons a xs ih =>
    simp only [intSum]
    exact Int.add_le_add (h a (by simp)) (ih (by intro x hx; exact h x (by simp [hx])))

theorem sum_const (xs : List α) (z : Int) :
    intSum xs (fun _ => z) = (xs.length : Int) * z := by
  induction xs with
  | nil => simp [intSum]
  | cons a xs ih => simp [intSum, ih, Int.add_mul, Int.add_comm]

theorem sum_mul_left (xs : List α) (z : Int) (f : α → Int) :
    intSum xs (fun a => z * f a) = z * intSum xs f := by
  induction xs with
  | nil => simp [intSum]
  | cons a xs ih => simp [intSum, ih, Int.mul_add]

theorem sum_append (xs ys : List α) (f : α → Int) :
    intSum (xs ++ ys) f = intSum xs f + intSum ys f := by
  induction xs with
  | nil => simp [intSum]
  | cons a xs ih => simp [intSum, ih, Int.add_assoc]

theorem sum_map (xs : List α) (g : α → β) (f : β → Int) :
    intSum (xs.map g) f = intSum xs (fun a => f (g a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [intSum, ih]

theorem sum_flatMap (xs : List α) (g : α → List β) (f : β → Int) :
    intSum (xs.flatMap g) f = intSum xs (fun a => intSum (g a) f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [intSum, sum_append, ih]

/-- The actual finite list of all copied interaction pairs. -/
def blowupPairs (copies : List β) (es : List (α × α)) :
    List ((α × β) × (α × β)) :=
  es.flatMap fun e => copies.flatMap fun i =>
    copies.map fun j => ((e.1, i), (e.2, j))

def blowEnergy (copies : List β) (es : List (α × α)) (χ : α → β → Bool) : Int :=
  intSum es fun e => intSum copies fun i => intSum copies fun j => same (χ e.1 i) (χ e.2 j)

/-- The double sum is exactly the project's monochromatic-pair objective on
an explicitly constructed finite blowup graph. -/
theorem blowEnergy_eq_monoCount (copies : List β) (es : List (α × α))
    (χ : α → β → Bool) :
    blowEnergy copies es χ =
      (Q4.monoCount (blowupPairs copies es) (fun e => χ e.1 e.2) : Int) := by
  rw [← edgeEnergy_eq_monoCount]
  unfold blowupPairs blowEnergy
  simp only [sum_flatMap, sum_map]

def liftColor (z : α → Bool) : α → β → Bool := fun a _ => z a

theorem lift_energy (copies : List β) (es : List (α × α)) (z : α → Bool) :
    blowEnergy copies es (liftColor z) =
      (copies.length : Int) * (copies.length : Int) * (Q4.monoCount es z : Int) := by
  unfold blowEnergy liftColor
  simp only [sum_const]
  rw [sum_mul_left, sum_mul_left, edgeEnergy_eq_monoCount]
  simp only [Int.mul_assoc]

variable [DecidableEq α]

def uniformAt (χ : α → β → Bool) (v : α) (b : Bool) : α → β → Bool :=
  fun a i => if a = v then b else χ a i

def outsideEnergy (copies : List β) (es : List (α × α))
    (χ : α → β → Bool) (v : α) : Int :=
  intSum es fun e => if v = e.1 ∨ v = e.2 then 0 else
    intSum copies fun i => intSum copies fun j => same (χ e.1 i) (χ e.2 j)

def colorCost (copies : List β) (es : List (α × α))
    (χ : α → β → Bool) (v : α) (b : Bool) : Int :=
  intSum es fun e =>
    if v = e.1 then intSum copies (fun j => same b (χ e.2 j))
    else if v = e.2 then intSum copies (fun i => same (χ e.1 i) b)
    else 0

/-- Decomposition of the actual pair objective around a loop-free copy class. -/
theorem class_decomposition (copies : List β) (es : List (α × α))
    (χ : α → β → Bool) (v : α)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    blowEnergy copies es χ = outsideEnergy copies es χ v +
      intSum copies (fun i => colorCost copies es χ v (χ v i)) := by
  unfold blowEnergy outsideEnergy colorCost
  rw [intSum_swap copies es, ← intSum_add]
  apply intSum_congr
  intro e he
  by_cases hv1 : v = e.1
  · have hv2 : v ≠ e.2 := by intro h; exact hloop e he (hv1.symm.trans h)
    subst v
    simp [hloop e he]
  · by_cases hv2 : v = e.2
    · subst v
      simpa [hloop e he, Ne.symm (hloop e he)] using
        intSum_swap copies copies (fun i j => same (χ e.1 i) (χ e.2 j))
    · simp [hv1, hv2, intSum_zero]

/-- After uniformisation, no neighbouring copy has changed colour. -/
theorem uniform_decomposition (copies : List β) (es : List (α × α))
    (χ : α → β → Bool) (v : α) (b : Bool)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    blowEnergy copies es (uniformAt χ v b) = outsideEnergy copies es χ v +
      intSum copies (fun _ => colorCost copies es χ v b) := by
  unfold blowEnergy outsideEnergy colorCost
  rw [intSum_swap copies es, ← intSum_add]
  apply intSum_congr
  intro e he
  by_cases hv1 : v = e.1
  · have hv2 : v ≠ e.2 := by intro h; exact hloop e he (hv1.symm.trans h)
    subst v
    simp [uniformAt, hloop e he, Ne.symm (hloop e he)]
  · by_cases hv2 : v = e.2
    · subst v
      simpa [uniformAt, hloop e he, Ne.symm (hloop e he)] using
        intSum_swap copies copies (fun i (_ : β) => same (χ e.1 i) b)
    · simp [uniformAt, hv1, hv2, Ne.symm hv1, Ne.symm hv2, intSum_zero]

/-- At least one of the two uniform colours never raises the full blowup cost. -/
theorem uniformize_one (copies : List β) (es : List (α × α))
    (χ : α → β → Bool) (v : α)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    ∃ b : Bool, blowEnergy copies es (uniformAt χ v b) ≤ blowEnergy copies es χ := by
  have choose : ∃ b : Bool, ∀ a : Bool,
      colorCost copies es χ v b ≤ colorCost copies es χ v a := by
    by_cases h : colorCost copies es χ v false ≤ colorCost copies es χ v true
    · exact ⟨false, by intro a; cases a; exact Int.le_refl _; exact h⟩
    · exact ⟨true, by intro a; cases a; omega; exact Int.le_refl _⟩
  obtain ⟨b, hb⟩ := choose
  refine ⟨b, ?_⟩
  rw [uniform_decomposition copies es χ v b hloop,
      class_decomposition copies es χ v hloop]
  exact Int.add_le_add_left (sum_le copies _ _ (fun _ _ => hb _)) _

/-- Sequentially uniformise all classes; already uniform classes stay uniform.
No order or distinctness assumption on `vs` is needed. -/
theorem uniformize_all (copies : List β) (es : List (α × α))
    (vs : List α) (χ : α → β → Bool)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2) :
    ∃ ψ : α → β → Bool, blowEnergy copies es ψ ≤ blowEnergy copies es χ ∧
      ∀ v, v ∈ vs → ∃ b, ∀ i, ψ v i = b := by
  induction vs with
  | nil => exact ⟨χ, Int.le_refl _, by simp⟩
  | cons v vs ih =>
    obtain ⟨ψ, hψ, hu⟩ := ih
    obtain ⟨b, hb⟩ := uniformize_one copies es ψ v hloop
    refine ⟨uniformAt ψ v b, Int.le_trans hb hψ, ?_⟩
    intro a ha
    by_cases hav : a = v
    · exact ⟨b, by intro i; simp [uniformAt, hav]⟩
    · have ha' : a ∈ vs := by simpa [hav] using ha
      obtain ⟨c, hc⟩ := hu a ha'
      exact ⟨c, by intro i; simp [uniformAt, hav, hc i]⟩

/-- Every unrestricted blowup colouring rounds to a source colouring with
at most its cost after multiplication by the square of the class size. -/
theorem blowup_rounding (copies : List β) (es : List (α × α))
    (vs : List α) (χ : α → β → Bool)
    (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hends : ∀ e, e ∈ es → e.1 ∈ vs ∧ e.2 ∈ vs) :
    ∃ z : α → Bool,
      (copies.length : Int) * (copies.length : Int) * (Q4.monoCount es z : Int) ≤
        blowEnergy copies es χ := by
  classical
  obtain ⟨ψ, hψ, hu⟩ := uniformize_all copies es vs χ hloop
  let z : α → Bool := fun a => if ha : a ∈ vs then Classical.choose (hu a ha) else false
  have hagree (a : α) (ha : a ∈ vs) (i : β) : ψ a i = z a := by
    dsimp [z]
    rw [dite_eq_left ha]
    exact Classical.choose_spec (hu a ha) i
  have heq : blowEnergy copies es ψ = blowEnergy copies es (liftColor z) := by
    apply intSum_congr
    intro e he
    apply intSum_congr
    intro i _
    apply intSum_congr
    intro j _
    simp only [liftColor, hagree e.1 (hends e he).1 i, hagree e.2 (hends e he).2 j]
  refine ⟨z, ?_⟩
  rw [heq, lift_energy] at hψ
  exact hψ

private theorem nat_minimum (P : Nat → Prop) (hex : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  classical
  obtain ⟨n, hn⟩ := hex
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : ∃ m, m < n ∧ P m
    · obtain ⟨m, hmn, hm⟩ := hsmall
      exact ih m hmn hm
    · exact ⟨n, hn, by
        intro m hm
        by_cases h : n ≤ m
        · exact h
        · exact False.elim (hsmall ⟨m, by omega, hm⟩)⟩

/-- Source optimum is defined from the actual finite monochromatic count. -/
noncomputable def sourceOpt (es : List (α × α)) : Nat :=
  Classical.choose (nat_minimum (fun n => ∃ z : α → Bool, Q4.monoCount es z = n)
    ⟨Q4.monoCount es (fun _ => false), ⟨fun _ => false, rfl⟩⟩)

omit [DecidableEq α] in
theorem sourceOpt_spec (es : List (α × α)) :
    (∃ z : α → Bool, Q4.monoCount es z = sourceOpt es) ∧
      ∀ z, sourceOpt es ≤ Q4.monoCount es z := by
  have h := Classical.choose_spec
    (nat_minimum (fun n => ∃ z : α → Bool, Q4.monoCount es z = n)
      ⟨Q4.monoCount es (fun _ => false), ⟨fun _ => false, rfl⟩⟩)
  exact ⟨h.1, fun z => h.2 _ ⟨z, rfl⟩⟩

/-- Lemma 5.1, at the exact finite colour-objective level: both a global lower
bound and an attaining unrestricted colouring. The blowup optimum is proved,
not assumed. The geometric identification of the graph is external. -/
theorem independent_blowup_minimum (copies : List β) (es : List (α × α))
    (vs : List α) (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hends : ∀ e, e ∈ es → e.1 ∈ vs ∧ e.2 ∈ vs) :
    (∀ χ : α → β → Bool,
      (copies.length : Int) * (copies.length : Int) * (sourceOpt es : Int) ≤
        blowEnergy copies es χ) ∧
    (∃ χ : α → β → Bool, blowEnergy copies es χ =
      (copies.length : Int) * (copies.length : Int) * (sourceOpt es : Int)) := by
  constructor
  · intro χ
    obtain ⟨z, hz⟩ := blowup_rounding copies es vs χ hloop hends
    have hg : (sourceOpt es : Int) ≤ (Q4.monoCount es z : Int) := by
      exact Int.ofNat_le.mpr ((sourceOpt_spec es).2 z)
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_left hg
      (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))) hz
  · obtain ⟨z, hz⟩ := (sourceOpt_spec es).1
    exact ⟨liftColor z, by rw [lift_energy, hz]⟩

/-! Exact deletion / restoration and independent unary minima. -/

variable {γ : Type w} {δ : Type w'}

def rawSourceUnary (ss : List (α × β)) (r : α × β → Int)
    (χ : α → β → Bool) : Int :=
  intSum ss (fun e => if χ e.1 e.2 then r e else 0)

def sourceUnaryFloor (ss : List (α × β)) (r : α × β → Int) : Int :=
  intSum ss (fun e => min 0 (r e))

def residualUnary (ss : List (α × β)) (r : α × β → Int)
    (χ : α → β → Bool) : Int :=
  intSum ss (fun e => (if χ e.1 e.2 then r e else 0) - min 0 (r e))

omit [DecidableEq α] in
theorem residual_identity (ss : List (α × β)) (r : α × β → Int)
    (χ : α → β → Bool) :
    rawSourceUnary ss r χ = sourceUnaryFloor ss r + residualUnary ss r χ := by
  unfold rawSourceUnary sourceUnaryFloor residualUnary
  rw [intSum_sub]
  omega

theorem residual_bit_bounds (r R : Int) (b : Bool) (hr : -R ≤ r ∧ r ≤ R) :
    0 ≤ (if b then r else 0) - min 0 r ∧
      (if b then r else 0) - min 0 r ≤ R := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.min_def]
  all_goals split <;> omega

omit [DecidableEq α] in
theorem residual_nonnegative (ss : List (α × β)) (r : α × β → Int)
    (χ : α → β → Bool) : 0 ≤ residualUnary ss r χ := by
  unfold residualUnary
  rw [← intSum_zero ss]
  apply sum_le
  intro e _
  cases χ e.1 e.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.min_def]
  all_goals split <;> omega

omit [DecidableEq α] in
theorem residual_upper (ss : List (α × β)) (r : α × β → Int)
    (χ : α → β → Bool) (R : Int)
    (hr : ∀ e, e ∈ ss → -R ≤ r e ∧ r e ≤ R) :
    residualUnary ss r χ ≤ (ss.length : Int) * R := by
  rw [← sum_const ss R]
  exact sum_le ss _ _ (fun e he => (residual_bit_bounds (r e) R (χ e.1 e.2) (hr e he)).2)

def unaryEnergy (vs : List γ) (u : γ → Bool → Int) (η : γ → Bool) : Int :=
  intSum vs (fun a => u a (η a))

def unaryFloor (vs : List γ) (u : γ → Bool → Int) : Int :=
  intSum vs (fun a => min (u a false) (u a true))

def unaryMinColor (u : γ → Bool → Int) (a : γ) : Bool :=
  if u a false ≤ u a true then false else true

theorem unary_lower (vs : List γ) (u : γ → Bool → Int) (η : γ → Bool) :
    unaryFloor vs u ≤ unaryEnergy vs u η := by
  apply sum_le
  intro a _
  cases η a <;> simp only [Int.min_def]
  all_goals split <;> omega

theorem unary_attains (vs : List γ) (u : γ → Bool → Int) :
    unaryEnergy vs u (unaryMinColor u) = unaryFloor vs u := by
  apply intSum_congr
  intro a _
  simp only [unaryMinColor, Int.min_def]
  split <;> rfl

/-- A full unrestricted colouring of source, short, and dummy variables. -/
structure CoreColor (α : Type u) (β : Type v) (γ : Type w) (δ : Type w') where
  source : α → β → Bool
  short : γ → Bool
  dummy : δ → Bool

/-- Tags make the variable sets disjoint without omitting any local pair. -/
abbrev CoreVar (α : Type u) (β : Type v) (γ : Type w) (δ : Type w') :=
  (α × β) ⊕ (γ ⊕ δ)

def CoreColor.read (c : CoreColor α β γ δ) : CoreVar α β γ δ → Bool
  | .inl e => c.source e.1 e.2
  | .inr (.inl a) => c.short a
  | .inr (.inr d) => c.dummy d

/-- The deleted core objective, with all its colour variables explicit. The
geometric proof must identify its coefficients and independent dummy block. -/
def deletedCore (base : Int) (copies : List β) (es : List (α × α))
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyCost : (δ → Bool) → Int)
    (c : CoreColor α β γ δ) : Int :=
  base + blowEnergy copies es c.source + rawSourceUnary ss r c.source +
    unaryEnergy shorts u c.short + dummyCost c.dummy

/-- Restore each local monochromatic constraint exactly once. -/
def fullCore (base : Int) (copies : List β) (es : List (α × α))
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyCost : (δ → Bool) → Int)
    (localPairs : List (CoreVar α β γ δ × CoreVar α β γ δ))
    (c : CoreColor α β γ δ) : Int :=
  deletedCore base copies es ss r shorts u dummyCost c +
    (Q4.monoCount localPairs c.read : Int)

/-- The candidate C₀, evaluating the zero source assignment after minimizing
short unaries and the dummy block. This is an explicit finite expression. -/
def zeroConstant (base : Int) (copies : List β) (es : List (α × α))
    (shorts : List γ) (u : γ → Bool → Int) (dummyMinimum : Int) : Int :=
  base + (copies.length : Int) * (copies.length : Int) * (es.length : Int) +
    unaryFloor shorts u + dummyMinimum

/-- Exactly the single source-edge subtraction in (5.13). -/
def coreConstant (base : Int) (copies : List β) (es : List (α × α))
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyMinimum : Int) : Int :=
  zeroConstant base copies es shorts u dummyMinimum -
    (copies.length : Int) * (copies.length : Int) * (es.length : Int) +
    sourceUnaryFloor ss r

omit [DecidableEq α] in
theorem coreConstant_simplify (base : Int) (copies : List β) (es : List (α × α))
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyMinimum : Int) :
    coreConstant base copies es ss r shorts u dummyMinimum =
      base + unaryFloor shorts u + dummyMinimum + sourceUnaryFloor ss r := by
  unfold coreConstant zeroConstant
  omega

omit [DecidableEq α] in
/-- Formula (5.14) as a genuine conditional minimum: every extension is at
least the expression, and independently minimizing short/dummy colours attains
it. The dummy minimum is the separate Lemma 5.5 interface. -/
theorem deleted_core_minimum (base : Int) (copies : List β) (es : List (α × α))
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyCost : (δ → Bool) → Int) (dummyMinimum : Int)
    (hd : ∀ d, dummyMinimum ≤ dummyCost d)
    (ha : ∃ d, dummyCost d = dummyMinimum) (χ : α → β → Bool) :
    (∀ η d, coreConstant base copies es ss r shorts u dummyMinimum +
      blowEnergy copies es χ + residualUnary ss r χ ≤
      deletedCore base copies es ss r shorts u dummyCost ⟨χ, η, d⟩) ∧
    (∃ η d, deletedCore base copies es ss r shorts u dummyCost ⟨χ, η, d⟩ =
      coreConstant base copies es ss r shorts u dummyMinimum +
      blowEnergy copies es χ + residualUnary ss r χ) := by
  rw [coreConstant_simplify]
  constructor
  · intro η d
    have hu := unary_lower shorts u η
    have hdd := hd d
    have hr := residual_identity ss r χ
    unfold deletedCore
    dsimp only
    omega
  · obtain ⟨d, hd⟩ := ha
    refine ⟨unaryMinColor u, d, ?_⟩
    have hu := unary_attains shorts u
    have hr := residual_identity ss r χ
    unfold deletedCore
    dsimp only
    omega

omit [DecidableEq α] in
theorem restoring_local_bounds (base : Int) (copies : List β) (es : List (α × α))
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyCost : (δ → Bool) → Int)
    (localPairs : List (CoreVar α β γ δ × CoreVar α β γ δ))
    (c : CoreColor α β γ δ) :
    deletedCore base copies es ss r shorts u dummyCost c ≤
      fullCore base copies es ss r shorts u dummyCost localPairs c ∧
    fullCore base copies es ss r shorts u dummyCost localPairs c ≤
      deletedCore base copies es ss r shorts u dummyCost c + (localPairs.length : Int) := by
  have h := Q4.mono_add_cut localPairs c.read
  unfold fullCore
  omega

omit [DecidableEq α] in
theorem mono_zero (es : List (α × α)) :
    Q4.monoCount es (fun _ => false) = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Q4.monoCount, ih, Nat.add_comm]

omit [DecidableEq α] in
/-- C₀ is actually attained by the all-zero source after the stated independent
minimisations; no local term has been subtracted here. -/
theorem zero_constant_evaluation (base : Int) (copies : List β) (es : List (α × α))
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyCost : (δ → Bool) → Int) (dummyMinimum : Int)
    (d : δ → Bool) (hd : dummyCost d = dummyMinimum) :
    deletedCore base copies es ss r shorts u dummyCost
      ⟨liftColor (fun _ => false), unaryMinColor u, d⟩ =
      zeroConstant base copies es shorts u dummyMinimum := by
  unfold deletedCore zeroConstant
  dsimp only
  rw [lift_energy, mono_zero, unary_attains, hd]
  have hz : rawSourceUnary ss r (liftColor (fun _ => false)) = 0 := by
    unfold rawSourceUnary liftColor
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact intSum_zero ss
  rw [hz]
  omega

omit [DecidableEq α] in
/-- Every source colouring has an actual extension with the displayed error.
All restored local pairs are evaluated on that same combined colouring. -/
theorem source_coloring_extension (base : Int) (copies : List β) (es : List (α × α))
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyCost : (δ → Bool) → Int) (dummyMinimum : Int)
    (hd : ∀ d, dummyMinimum ≤ dummyCost d)
    (ha : ∃ d, dummyCost d = dummyMinimum)
    (localPairs : List (CoreVar α β γ δ × CoreVar α β γ δ))
    (R : Int) (hr : ∀ e, e ∈ ss → -R ≤ r e ∧ r e ≤ R) (z : α → Bool) :
    ∃ c : CoreColor α β γ δ, c.source = liftColor z ∧
      fullCore base copies es ss r shorts u dummyCost localPairs c ≤
      coreConstant base copies es ss r shorts u dummyMinimum +
      (copies.length : Int) * (copies.length : Int) * (Q4.monoCount es z : Int) +
      (ss.length : Int) * R + (localPairs.length : Int) := by
  obtain ⟨η, d, hval⟩ := (deleted_core_minimum base copies es ss r shorts u
    dummyCost dummyMinimum hd ha (liftColor z)).2
  let c : CoreColor α β γ δ := ⟨liftColor z, η, d⟩
  refine ⟨c, rfl, ?_⟩
  have hrest := (restoring_local_bounds base copies es ss r shorts u dummyCost localPairs c).2
  have hres := residual_upper ss r (liftColor z) R hr
  rw [lift_energy] at hval
  dsimp [c] at hrest ⊢
  omega

/-- Proposition 5.7 at the explicit finite core-objective level. Its lower
bound holds for *every* colouring; its upper bound has an actual common
extension. Palette forcing and the geometric bounds on `r`, `ss`, and
`localPairs` are external obligations, not axioms concealed in the proof. -/
theorem core_encoding_bounds (base : Int) (copies : List β) (es : List (α × α))
    (vs : List α) (hloop : ∀ e, e ∈ es → e.1 ≠ e.2)
    (hends : ∀ e, e ∈ es → e.1 ∈ vs ∧ e.2 ∈ vs)
    (ss : List (α × β)) (r : α × β → Int) (shorts : List γ)
    (u : γ → Bool → Int) (dummyCost : (δ → Bool) → Int) (dummyMinimum : Int)
    (hd : ∀ d, dummyMinimum ≤ dummyCost d)
    (ha : ∃ d, dummyCost d = dummyMinimum)
    (localPairs : List (CoreVar α β γ δ × CoreVar α β γ δ))
    (R : Int) (hr : ∀ e, e ∈ ss → -R ≤ r e ∧ r e ≤ R) :
    (∀ c : CoreColor α β γ δ,
      coreConstant base copies es ss r shorts u dummyMinimum +
      (copies.length : Int) * (copies.length : Int) * (sourceOpt es : Int) ≤
      fullCore base copies es ss r shorts u dummyCost localPairs c) ∧
    (∃ c : CoreColor α β γ δ,
      fullCore base copies es ss r shorts u dummyCost localPairs c ≤
      coreConstant base copies es ss r shorts u dummyMinimum +
      (copies.length : Int) * (copies.length : Int) * (sourceOpt es : Int) +
      (ss.length : Int) * R + (localPairs.length : Int)) := by
  constructor
  · intro c
    have hmain := (independent_blowup_minimum copies es vs hloop hends).1 c.source
    have hdel := (deleted_core_minimum base copies es ss r shorts u dummyCost
      dummyMinimum hd ha c.source).1 c.short c.dummy
    have hres := residual_nonnegative ss r c.source
    have hrest := (restoring_local_bounds base copies es ss r shorts u dummyCost localPairs c).1
    have hc : CoreColor.mk c.source c.short c.dummy = c := by cases c; rfl
    rw [hc] at hdel
    omega
  · obtain ⟨z, hz⟩ := (sourceOpt_spec es).1
    obtain ⟨c, _, hval⟩ := source_coloring_extension base copies es ss r shorts u
      dummyCost dummyMinimum hd ha localPairs R hr z
    exact ⟨c, by simpa only [hz] using hval⟩

#print axioms Q4.Candidate.CoreEncoding.blowEnergy_eq_monoCount
#print axioms Q4.Candidate.CoreEncoding.uniformize_one
#print axioms Q4.Candidate.CoreEncoding.blowup_rounding
#print axioms Q4.Candidate.CoreEncoding.independent_blowup_minimum
#print axioms Q4.Candidate.CoreEncoding.zero_constant_evaluation
#print axioms Q4.Candidate.CoreEncoding.deleted_core_minimum
#print axioms Q4.Candidate.CoreEncoding.source_coloring_extension
#print axioms Q4.Candidate.CoreEncoding.core_encoding_bounds

end Q4.Candidate.CoreEncoding
