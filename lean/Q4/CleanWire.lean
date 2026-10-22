import Q4.Counting

/-!
A finite integer-coordinate completion counterexample.  Geometric incidence is
encoded by strict determinant signs.  The universal coloring results below are
proved separately from the closed Boolean enumeration certificates.
-/

namespace Q4.CleanWire

abbrev Point := Int × Int
abbrev Edge := Nat × Nat

def orient (a b c : Point) : Int :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- The usual strict orientation-sign test, excluding shared endpoints. -/
def properCross (a b c d : Point) : Bool :=
  decide (orient a b c * orient a b d < 0 ∧ orient c d a * orient c d b < 0)

def edges (n : Nat) : List Edge :=
  (List.range n).flatMap fun i =>
    (List.range n).filterMap fun j => if i < j then some (i, j) else none

def crosses (points : List Point) (e f : Edge) : Bool :=
  properCross (points.getD e.1 (0, 0)) (points.getD e.2 (0, 0))
    (points.getD f.1 (0, 0)) (points.getD f.2 (0, 0))

/-- All complete-graph edge-index pairs, with each unordered pair considered once. -/
def crossings (points : List Point) : List (Nat × Nat) :=
  let es := edges points.length
  (List.range es.length).flatMap fun i =>
    (List.range es.length).filterMap fun j =>
      if i < j ∧ crosses points (es.getD i (0, 0)) (es.getD j (0, 0)) = true
      then some (i, j) else none

def distinctPoints (points : List Point) : Prop :=
  ∀ i j : Fin points.length, i ≠ j → points.get i ≠ points.get j

def noThreeCollinear (points : List Point) : Prop :=
  ∀ i j k : Fin points.length,
    i ≠ j → i ≠ k → j ≠ k → orient (points.get i) (points.get j) (points.get k) ≠ 0

def points6 : List Point :=
  [(0, -10), (0, 10), (10, -10), (10, 10), (-2, 0), (12, 0)]

def points7 : List Point := points6 ++ [(5, 14)]

def pairs6 : List (Nat × Nat) :=
  [(0, 10), (0, 12), (0, 14), (2, 5), (2, 8), (2, 10), (2, 14),
   (4, 5), (4, 9), (4, 10), (5, 12), (5, 14), (8, 9), (8, 12), (9, 14)]

def pairs7 : List (Nat × Nat) :=
  [(0, 12), (0, 15), (0, 18), (0, 19), (2, 6), (2, 9), (2, 12), (2, 14),
   (2, 18), (2, 20), (4, 6), (4, 11), (4, 12), (4, 14), (5, 6), (5, 7),
   (5, 9), (5, 12), (5, 15), (5, 18), (6, 15), (6, 18), (6, 19), (7, 14),
   (7, 19), (7, 20), (9, 11), (9, 14), (9, 15), (9, 19), (11, 18), (11, 20),
   (14, 15), (14, 18), (15, 20)]

set_option maxRecDepth 100000 in
theorem crossings6_exact : crossings points6 = pairs6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem crossings7_exact : crossings points7 = pairs7 := by decide +kernel

theorem points6_distinct : distinctPoints points6 := by unfold distinctPoints; decide +kernel
theorem points7_distinct : distinctPoints points7 := by unfold distinctPoints; decide +kernel
theorem points6_general : noThreeCollinear points6 := by unfold noThreeCollinear; decide +kernel
theorem points7_general : noThreeCollinear points7 := by unfold noThreeCollinear; decide +kernel

theorem signals6_indices :
    (edges points6.length).getD 0 (0, 0) = (0, 1) ∧
    (edges points6.length).getD 9 (0, 0) = (2, 3) := by decide

theorem signals7_indices :
    (edges points7.length).getD 0 (0, 0) = (0, 1) ∧
    (edges points7.length).getD 11 (0, 0) = (2, 3) := by decide

def coloring6 (r b0 b1 b2 b3 b4 b5 b6 : Bool) : Nat → Bool
  | 0 => false | 9 => r
  | 2 => b0 | 4 => b1 | 5 => b2 | 8 => b3 | 10 => b4 | 12 => b5 | 14 => b6
  | _ => false

def coloring7 (r b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) : Nat → Bool
  | 0 => false | 11 => r
  | 2 => b0 | 4 => b1 | 5 => b2 | 6 => b3 | 7 => b4 | 9 => b5
  | 12 => b6 | 14 => b7 | 15 => b8 | 18 => b9 | 19 => b10 | 20 => b11
  | _ => false

def sameWitness6 := coloring6 false false false true true true false true
def diffWitness6 := coloring6 true false false true true true false false
def sameWitness7 := coloring7 false true true false false true true false false true true false false
def diffWitness7 := coloring7 true false false false true true true true false true true false false

theorem same6_upper :
    sameWitness6 0 = sameWitness6 9 ∧ monoCount (crossings points6) sameWitness6 = 3 := by
  rw [crossings6_exact]
  decide

theorem diff6_upper :
    diffWitness6 0 ≠ diffWitness6 9 ∧ monoCount (crossings points6) diffWitness6 = 4 := by
  rw [crossings6_exact]
  decide

theorem same7_upper :
    sameWitness7 0 = sameWitness7 11 ∧ monoCount (crossings points7) sameWitness7 = 9 := by
  rw [crossings7_exact]
  decide

theorem diff7_upper :
    diffWitness7 0 ≠ diffWitness7 11 ∧ monoCount (crossings points7) diffWitness7 = 9 := by
  rw [crossings7_exact]
  decide

/- Closed enumeration over all 2^8 compressed assignments, including the relation bit. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem compressed6_lower : ∀ r b0 b1 b2 b3 b4 b5 b6 : Bool,
    (if r then 4 else 3) ≤ monoCount pairs6 (coloring6 r b0 b1 b2 b3 b4 b5 b6) := by
  decide +kernel

/- Closed enumeration over all 2^13 compressed assignments, including the relation bit. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem compressed7_lower : ∀ r b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
    9 ≤ monoCount pairs7 (coloring7 r b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11) := by
  decide +kernel

def normalized (χ : Nat → Bool) (i : Nat) : Bool := (χ 0).xor (χ i)

theorem monoCount_xor (ps : List (Nat × Nat)) (χ : Nat → Bool) (b : Bool) :
    monoCount ps (fun i => b.xor (χ i)) = monoCount ps χ := by
  have hbool (x y : Bool) : b.xor x = b.xor y ↔ x = y := by
    cases b <;> cases x <;> cases y <;> decide
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, c⟩
    simp only [monoCount, hbool, ih]

theorem normalized_zero (χ : Nat → Bool) : normalized χ 0 = false := by
  cases h : χ 0 <;> simp [normalized, h]

theorem normalization_preserves_score (ps : List (Nat × Nat)) (χ : Nat → Bool) :
    monoCount ps (normalized χ) = monoCount ps χ :=
  monoCount_xor ps χ (χ 0)

/-- Every color affecting K6's score occurs in the compressed tuple. -/
theorem compression6_covers (χ : Nat → Bool) (h : χ 0 = false) :
    monoCount pairs6 χ = monoCount pairs6
      (coloring6 (χ 9) (χ 2) (χ 4) (χ 5) (χ 8) (χ 10) (χ 12) (χ 14)) := by
  simp [pairs6, monoCount, coloring6, h]

/-- Every color affecting K7's score occurs in the compressed tuple. -/
theorem compression7_covers (χ : Nat → Bool) (h : χ 0 = false) :
    monoCount pairs7 χ = monoCount pairs7
      (coloring7 (χ 11) (χ 2) (χ 4) (χ 5) (χ 6) (χ 7) (χ 9)
        (χ 12) (χ 14) (χ 15) (χ 18) (χ 19) (χ 20)) := by
  simp [pairs7, monoCount, coloring7, h]

/-- The enumeration bound applies to every original coloring, not just encoded masks. -/
theorem all_colorings6_lower (χ : Nat → Bool) :
    (if χ 0 = χ 9 then 3 else 4) ≤ monoCount (crossings points6) χ := by
  have h := compressed6_lower (normalized χ 9) (normalized χ 2) (normalized χ 4)
    (normalized χ 5) (normalized χ 8) (normalized χ 10) (normalized χ 12) (normalized χ 14)
  rw [← compression6_covers (normalized χ) (normalized_zero χ),
    normalization_preserves_score] at h
  have hrelation : (if normalized χ 9 then 4 else 3) = (if χ 0 = χ 9 then 3 else 4) := by
    cases h0 : χ 0 <;> cases h9 : χ 9 <;> simp [normalized, h0, h9]
  rw [hrelation] at h
  rw [crossings6_exact]
  exact h

/-- The enumeration bound applies to every original coloring, including inactive edges. -/
theorem all_colorings7_lower (χ : Nat → Bool) :
    9 ≤ monoCount (crossings points7) χ := by
  have h := compressed7_lower (normalized χ 11) (normalized χ 2) (normalized χ 4)
    (normalized χ 5) (normalized χ 6) (normalized χ 7) (normalized χ 9)
    (normalized χ 12) (normalized χ 14) (normalized χ 15) (normalized χ 18)
    (normalized χ 19) (normalized χ 20)
  rw [← compression7_covers (normalized χ) (normalized_zero χ),
    normalization_preserves_score] at h
  rw [crossings7_exact]
  exact h

def IsRelationMinimum (points : List Point) (signal : Nat) (same : Bool) (cost : Nat) : Prop :=
  (∃ χ : Nat → Bool, (χ 0 == χ signal) = same ∧ monoCount (crossings points) χ = cost) ∧
  ∀ χ : Nat → Bool, (χ 0 == χ signal) = same → cost ≤ monoCount (crossings points) χ

theorem same6_exact : IsRelationMinimum points6 9 true 3 := by
  constructor
  · exact ⟨sameWitness6, by decide, same6_upper.2⟩
  · intro χ hχ
    have hsame : χ 0 = χ 9 := by simpa using hχ
    simpa [hsame] using all_colorings6_lower χ

theorem diff6_exact : IsRelationMinimum points6 9 false 4 := by
  constructor
  · exact ⟨diffWitness6, by decide, diff6_upper.2⟩
  · intro χ hχ
    have hdiff : χ 0 ≠ χ 9 := by simpa using hχ
    simpa [hdiff] using all_colorings6_lower χ

theorem same7_exact : IsRelationMinimum points7 11 true 9 := by
  exact ⟨⟨sameWitness7, by decide, same7_upper.2⟩, fun χ _ => all_colorings7_lower χ⟩

theorem diff7_exact : IsRelationMinimum points7 11 false 9 := by
  exact ⟨⟨diffWitness7, by decide, diff7_upper.2⟩, fun χ _ => all_colorings7_lower χ⟩

def extendFiniteColoring {n : Nat} (χ : Fin n → Bool) (i : Nat) : Bool :=
  if h : i < n then χ ⟨i, h⟩ else false

/-- Every finite edge-color vector extends to the unrestricted coloring domain. -/
theorem extendFiniteColoring_agrees {n : Nat} (χ : Fin n → Bool) (i : Fin n) :
    extendFiniteColoring χ i.val = χ i := by
  simp [extendFiniteColoring, i.isLt]

end Q4.CleanWire
