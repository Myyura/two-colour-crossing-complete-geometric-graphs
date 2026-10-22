import Q4.Candidate.DoubleCapGrid
import Q4.Candidate.GridStepBridge

/-!
The exhaustive finite edge set of the actual original/frame/program drawing.
Each edge occurs once, with distinct endpoints. Crossings are evaluated from
actual rational coordinates, and the X/C/Y/I zero terms are derived from the
proved cap geometry rather than postulated as a graph partition hypothesis.
-/
namespace Q4.Candidate.CompleteDrawing

open Q4.Candidate.ConvexSeparation

abbrev Vertex (O B P : Nat) := Fin O ⊕ (Fin B ⊕ Fin P)
abbrev Inner (n : Nat) := {p : Fin n × Fin n // p.1 < p.2}
abbrev YEdge (O P : Nat) := (Fin O × Fin P) ⊕ Inner P
abbrev Outside (O B P : Nat) := (Fin B × Fin P) ⊕ (Inner O ⊕ (YEdge O P ⊕ Inner B))
abbrev Edge (O B P : Nat) := (Fin B × Fin O) ⊕ Outside O B P

def endpoints {O B P : Nat} : Edge O B P → Vertex O B P × Vertex O B P
  | .inl (i,j) => (.inl j,.inr (.inl i))
  | .inr (.inl (i,k)) => (.inr (.inl i),.inr (.inr k))
  | .inr (.inr (.inl p)) => (.inl p.val.1,.inl p.val.2)
  | .inr (.inr (.inr (.inl (.inl (j,k))))) => (.inl j,.inr (.inr k))
  | .inr (.inr (.inr (.inl (.inr p)))) => (.inr (.inr p.val.1),.inr (.inr p.val.2))
  | .inr (.inr (.inr (.inr p))) => (.inr (.inl p.val.1),.inr (.inl p.val.2))

def vertexIndex {O B P : Nat} : Vertex O B P → Nat
  | .inl j => j.val
  | .inr (.inl i) => O+i.val
  | .inr (.inr k) => O+B+k.val

theorem endpoints_increasing {O B P : Nat} (e : Edge O B P) :
    vertexIndex (endpoints e).1 < vertexIndex (endpoints e).2 := by
  rcases e with x | (t | (c | ((y | z) | i)))
  · simp only [endpoints,vertexIndex]
    omega
  · simp only [endpoints,vertexIndex]
    omega
  · exact c.property
  · simp only [endpoints,vertexIndex]
    omega
  · simp only [endpoints,vertexIndex]
    have h := z.property
    exact Nat.add_lt_add_left h _
  · simp only [endpoints,vertexIndex]
    have h := i.property
    exact Nat.add_lt_add_left h _

theorem endpoints_ne {O B P : Nat} (e : Edge O B P) :
    (endpoints e).1 ≠ (endpoints e).2 := by
  intro h
  have hi := endpoints_increasing e
  rw [h] at hi
  exact lt_irrefl _ hi

theorem endpoints_injective {O B P : Nat} : Function.Injective (@endpoints O B P) := by
  intro e f h
  rcases e with x | (t | (c | ((y | z) | i))) <;>
    rcases f with x' | (t' | (c' | ((y' | z') | i'))) <;>
    simp_all [endpoints,Prod.ext_iff,Subtype.ext_iff]

/-- Every unordered pair of distinct actual labels is represented. Together
with endpoint injectivity and increasing endpoint indices this excludes both
omitted completion edges and duplicates. -/
theorem edges_exhaustive {O B P : Nat} (v w : Vertex O B P) (hvw : v ≠ w) :
    ∃ e : Edge O B P, endpoints e = (v,w) ∨ endpoints e = (w,v) := by
  rcases v with j | (i | k) <;> rcases w with j' | (i' | k')
  · have hj : j ≠ j' := fun h => hvw (congrArg Sum.inl h)
    rcases lt_or_gt_of_ne hj with h | h
    · exact ⟨.inr (.inr (.inl ⟨(j,j'),h⟩)),Or.inl rfl⟩
    · exact ⟨.inr (.inr (.inl ⟨(j',j),h⟩)),Or.inr rfl⟩
  · exact ⟨.inl (i',j),Or.inl rfl⟩
  · exact ⟨.inr (.inr (.inr (.inl (.inl (j,k'))))),Or.inl rfl⟩
  · exact ⟨.inl (i,j'),Or.inr rfl⟩
  · have hi : i ≠ i' := fun h => hvw (congrArg (fun z => Sum.inr (Sum.inl z)) h)
    rcases lt_or_gt_of_ne hi with h | h
    · exact ⟨.inr (.inr (.inr (.inr ⟨(i,i'),h⟩))),Or.inl rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr ⟨(i',i),h⟩))),Or.inr rfl⟩
  · exact ⟨.inr (.inl (i,k')),Or.inl rfl⟩
  · exact ⟨.inr (.inr (.inr (.inl (.inl (j',k))))),Or.inr rfl⟩
  · exact ⟨.inr (.inl (i',k)),Or.inr rfl⟩
  · have hk : k ≠ k' := fun h => hvw (congrArg (fun z => Sum.inr (Sum.inr z)) h)
    rcases lt_or_gt_of_ne hk with h | h
    · exact ⟨.inr (.inr (.inr (.inl (.inr ⟨(k,k'),h⟩)))),Or.inl rfl⟩
    · exact ⟨.inr (.inr (.inr (.inl (.inr ⟨(k',k),h⟩)))),Or.inr rfl⟩

theorem unordered_endpoints_injective {O B P : Nat} (e f : Edge O B P)
    (h : endpoints e = endpoints f ∨ endpoints e = ((endpoints f).2,(endpoints f).1)) : e = f := by
  rcases h with h | h
  · exact endpoints_injective h
  · have he := endpoints_increasing e
    have hf := endpoints_increasing f
    rw [h] at he
    dsimp at he
    exact (lt_asymm he hf).elim

def tag {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point) :
    Vertex O B P → ConvexSeparation.Vertex
  | .inl j => .original (ys j)
  | .inr (.inl i) => .frame (ts i)
  | .inr (.inr k) => .program (rs k)

def point {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (v : Vertex O B P) : Point := (tag ys ts rs v).point

def Cross {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e f : Edge O B P) : Prop :=
  ProperCross (point ys ts rs (endpoints e).1) (point ys ts rs (endpoints e).2)
    (point ys ts rs (endpoints f).1) (point ys ts rs (endpoints f).2)

theorem cross_symm {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e f : Edge O B P) : Cross ys ts rs e f ↔ Cross ys ts rs f e :=
  properCross_swap_edges _ _ _ _

theorem cross_irrefl {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e : Edge O B P) : ¬ Cross ys ts rs e e := by
  simp [Cross,ProperCross,orient]

theorem tag_valid {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : ∀ j, |ys j| ≤ 1) (ht : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid) (v : Vertex O B P) :
    (tag ys ts rs v).valid := by
  rcases v with j | (i | k)
  · exact abs_le.mp (hy j)
  · exact abs_le.mp (ht i)
  · exact hr k

theorem X_cross_X {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : StrictMono ys) (ht : StrictAnti ts)
    (hybox : ∀ j, |ys j| ≤ 1) (htbox : ∀ i, |ts i| ≤ 1)
    (x x' : Fin B × Fin O) :
    Cross ys ts rs (.inl x) (.inl x') ↔ GridCounts.adj x x' := by
  exact DoubleCapGrid.indexed_grid_crossing B O ys ts hy ht hybox htbox x x'

theorem X_cross_outside_only_T {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : ∀ j, |ys j| ≤ 1) (ht : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (x : Fin B × Fin O) (r : Outside O B P) (hc : Cross ys ts rs (.inl x) (.inr r)) :
    ∃ t : Fin B × Fin P, r = .inl t := by
  rcases r with t | (c | ((y | z) | i))
  · exact ⟨t,rfl⟩
  · exact (X_no_cross_C_or_Y (ys x.2) (ts x.1) (.original (ys c.val.1)) (.original (ys c.val.2))
      (abs_le.mp (hy x.2)).1 (abs_le.mp (hy x.2)).2
      (abs_le.mp (hy c.val.1)) (abs_le.mp (hy c.val.2)) (Or.inl rfl) hc).elim
  · exact (X_no_cross_C_or_Y (ys x.2) (ts x.1) (.original (ys y.1)) (.program (rs y.2))
      (abs_le.mp (hy x.2)).1 (abs_le.mp (hy x.2)).2
      (abs_le.mp (hy y.1)) (hr y.2) (Or.inr rfl) hc).elim
  · exact (X_no_cross_C_or_Y (ys x.2) (ts x.1) (.program (rs z.val.1)) (.program (rs z.val.2))
      (abs_le.mp (hy x.2)).1 (abs_le.mp (hy x.2)).2
      (hr z.val.1) (hr z.val.2) (Or.inr rfl) hc).elim
  · exact (I_isolated (ts i.val.1) (ts i.val.2) (.original (ys x.2)) (.frame (ts x.1))
      (abs_le.mp (hy x.2)) (abs_le.mp (ht x.1)) (by simp [edgeKind]) hc).elim

def kind {O B P : Nat} : Edge O B P → EdgeKind
  | .inl _ => .X
  | .inr (.inl _) => .T
  | .inr (.inr (.inl _)) => .C
  | .inr (.inr (.inr (.inl _))) => .Y
  | .inr (.inr (.inr (.inr _))) => .I

theorem kind_from_endpoints {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (e : Edge O B P) :
    edgeKind (tag ys ts rs (endpoints e).1) (tag ys ts rs (endpoints e).2) = kind e := by
  rcases e with x | (t | (c | ((y | z) | i))) <;> rfl

theorem I_no_cross_nonI {O B P : Nat} (ys : Fin O → ℚ) (ts : Fin B → ℚ) (rs : Fin P → Point)
    (hy : ∀ j, |ys j| ≤ 1) (ht : ∀ i, |ts i| ≤ 1)
    (hr : ∀ k, (ConvexSeparation.Vertex.program (rs k)).valid)
    (i : Inner B) (e : Edge O B P) (he : kind e ≠ .I) :
    ¬ Cross ys ts rs e (.inr (.inr (.inr (.inr i)))) := by
  have hk : edgeKind (tag ys ts rs (endpoints e).1) (tag ys ts rs (endpoints e).2) ≠ .I := by
    simpa only [kind_from_endpoints] using he
  exact I_isolated (ts i.val.1) (ts i.val.2)
    (tag ys ts rs (endpoints e).1) (tag ys ts rs (endpoints e).2)
    (tag_valid ys ts rs hy ht hr _) (tag_valid ys ts rs hy ht hr _) hk

end Q4.Candidate.CompleteDrawing

#print axioms Q4.Candidate.CompleteDrawing.edges_exhaustive
#print axioms Q4.Candidate.CompleteDrawing.unordered_endpoints_injective
#print axioms Q4.Candidate.CompleteDrawing.X_cross_X
#print axioms Q4.Candidate.CompleteDrawing.X_cross_outside_only_T
#print axioms Q4.Candidate.CompleteDrawing.I_no_cross_nonI
