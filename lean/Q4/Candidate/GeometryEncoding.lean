import Q4.Candidate.RationalEncoding
import Q4.Candidate.SourceChordGeometry

/-! Explicit coordinate certificates for the actual common-scale construction.
The exponents are deliberately uniform and loose, but independent of rank,
number of prototypes, or number of copies. -/
namespace Q4.Candidate.GeometryEncoding
open Q4.Candidate.RationalEncoding Q4.Candidate.ConvexSeparation
open Q4.Candidate.GlobalGeometryScales Q4.Candidate.RankGap
open Q4.Candidate.DoubleCapGrid Q4.Candidate.OrientationPreservation
open Q4.Candidate.UniformInsertion Q4.Candidate.SourceChordGeometry

theorem point_encoding_mono {p : Point} {H i j : ℕ} (hp : PointBounded p H i)
    (hH : 1 ≤ H) (hij : i ≤ j) : PointBounded p H j :=
  ⟨hp.1.pow_mono hH hij,hp.2.pow_mono hH hij⟩

theorem cap_point_encoding (a : ℚ) (H k : ℕ) (hH : 100 ≤ H)
    (ha : Bounded a (H^k)) :
    PointBounded (original a) H (2*k+3) ∧ PointBounded (frame a) H (2*k+3) := by
  have h1 : 1 ≤ H := by omega
  have h2 : 2 ≤ H := by omega
  have hsq := ha.sq_pow.div_pow (bounded_nat_pow 100 H hH h1)
  have hx := (bounded_nat_pow 10 H (by omega) h1).neg.sub_pow hsq h2
  have hf := (bounded_nat_pow 1 H (by omega) h1).add_pow hsq h2
  refine ⟨⟨?_,ha.pow_mono h1 (by omega)⟩,⟨?_,ha.pow_mono h1 (by omega)⟩⟩
  · exact hx.pow_mono (by omega) (by omega)
  · exact hf.pow_mono (by omega) (by omega)

theorem cloneAt_encoding (a tau w s : ℚ) (H : ℕ) (hH : 2 ≤ H)
    (ha : Bounded a (H^1)) (ht : Bounded tau (H^20))
    (hw : Bounded w (H^1)) (hs : Bounded s (H^1)) :
    Bounded (cloneAt a tau w s) (H^29) := by
  have hone := bounded_nat_pow 1 H (by omega) (by omega)
  have hhalf := hone.div_pow (bounded_nat_pow 2 H hH (by omega))
  exact ha.add_pow (ht.mul_pow ((hs.div_pow (hw.sub_pow hone hH)).sub_pow hhalf hH)) hH

theorem mix_encoding (a b : Point) (l : ℚ) (H k j : ℕ) (hH : 2 ≤ H)
    (ha : PointBounded a H k) (hb : PointBounded b H k) (hl : Bounded l (H^j)) :
    PointBounded (mix a b l) H (2*k+2*j+3) := by
  have hh := (bounded_nat_pow 1 H (by omega) (by omega)).sub_pow hl hH
  constructor
  · have hx := (hh.mul_pow ha.1).add_pow (hl.mul_pow hb.1) hH
    exact hx.pow_mono (by omega) (by omega)
  · have hy := (hh.mul_pow ha.2).add_pow (hl.mul_pow hb.2) hH
    exact hy.pow_mono (by omega) (by omega)

theorem ordinary_encoding (A : Finset ℚ) (W B H : ℕ) (hH : 10000 ≤ H)
    (hW : W ≤ H) (hB : B ≤ H) (hA : ∀a∈A, Bounded a H)
    (a : ℚ) (ha : a∈A) : PointBounded (ordinary a (programScale A W)) H 300 := by
  have hcoord : Bounded a (H^1) := by simpa using hA a ha
  have horig := (cap_point_encoding a H 1 (by omega) hcoord).1
  have hzero : Bounded (0:ℚ) (H^1) := bounded_nat_pow 0 H (by omega) (by omega)
  have hframe := (cap_point_encoding 0 H 1 (by omega) hzero).2
  have hscale := (scales_encoding A W B H hH hW hB hA).1
  exact point_encoding_mono (mix_encoding _ _ _ H 5 10 (by omega) horig hframe hscale.neg) (by omega) (by omega)

theorem height_encoding (a b mu : ℚ) (H : ℕ) (hH : 2 ≤ H)
    (ha : Bounded a (H^1)) (hb : Bounded b (H^1)) (hm : Bounded mu (H^10)) :
    Bounded (leftHeight a b mu) (H^15) ∧ Bounded (rightHeight a b mu) (H^15) :=
  ⟨ha.add_pow (hm.mul_pow (hb.sub_pow ha hH)) hH,
   hb.sub_pow (hm.mul_pow (hb.sub_pow ha hH)) hH⟩

theorem chordX_encoding (a b y : ℚ) (H : ℕ) (hH : 100 ≤ H)
    (ha : Bounded a (H^29)) (hb : Bounded b (H^29)) (hy : Bounded y (H^15)) :
    Bounded (chordX a b y) (H^136) := by
  have hh := ((ha.add_pow hb (by omega)).mul_pow hy).sub_pow (ha.mul_pow hb) (by omega)
  exact (bounded_nat_pow 10 H (by omega) (by omega)).neg.sub_pow
    (hh.div_pow (bounded_nat_pow 100 H hH (by omega))) (by omega)

theorem rank_encoding (A : Finset ℚ) (W B H ell : ℕ) (hH : 10000 ≤ H)
    (hW : W ≤ H) (hB : B ≤ H) (hA : ∀a∈A, Bounded a H)
    (hW2 : 2 ≤ W) (hell : ell+1 ≤ W) (a b : ℚ) (ha : a∈A) (hb : b∈A) :
    PointBounded (leftRank a b (cloneScale A W B) W (programScale A W) ell) H 300 ∧
    PointBounded (rightRank a b (cloneScale A W B) W (programScale A W) ell) H 300 := by
  have h1 : 1 ≤ H := by omega
  have h2 : 2 ≤ H := by omega
  have hscales := scales_encoding A W B H hH hW hB hA
  have ha' : Bounded a (H^1) := by simpa using hA a ha
  have hb' : Bounded b (H^1) := by simpa using hA b hb
  have hw := bounded_nat_pow W H hW h1
  have he := bounded_nat_pow ell H (by omega) h1
  have he1 : Bounded ((ell:ℚ)+1) (H^1) := by
    exact_mod_cast bounded_nat_pow (ell+1) H (by omega) h1
  have hw1 : Bounded ((W:ℚ)-1) (H^1) := by
    rw [←Nat.cast_one,←Nat.cast_sub (by omega : 1 ≤ W)]
    exact bounded_nat_pow (W-1) H (by omega) h1
  have hz := bounded_nat_pow 0 H (by omega) h1
  have hc (v s : ℚ) (hv : Bounded v (H^1)) (hs : Bounded s (H^1)) :=
    cloneAt_encoding v (cloneScale A W B) W s H h2 hv hscales.2 hw hs
  have hy := height_encoding a b (programScale A W) H h2 ha' hb' hscales.1
  have hleft := (chordX_encoding _ _ _ H (by omega) (hc a ell ha' he) (hc b 0 hb' hz) hy.1).add_pow
    (chordX_encoding _ _ _ H (by omega) (hc a (ell+1) ha' he1) (hc b (W-1) hb' hw1) hy.1) h2
  have hright := (chordX_encoding _ _ _ H (by omega) (hc a (W-1) ha' hw1) (hc b (ell+1) hb' he1) hy.2).add_pow
    (chordX_encoding _ _ _ H (by omega) (hc a 0 ha' hz) (hc b ell hb' he) hy.2) h2
  have htwo := bounded_nat_pow 2 H h2 h1
  exact ⟨⟨(hleft.div_pow htwo).pow_mono h1 (by omega),hy.1.pow_mono h1 (by omega)⟩,
    ⟨(hright.div_pow htwo).pow_mono h1 (by omega),hy.2.pow_mono h1 (by omega)⟩⟩

theorem actual_original_encoding (A : Finset ℚ) (W B H s : ℕ) (hH : 10000 ≤ H)
    (hW : W ≤ H) (hB : B ≤ H) (hA : ∀a∈A, Bounded a H)
    (hs : s ≤ W) (a : ℚ) (ha : a∈A) :
    PointBounded (original (cloneAt a (cloneScale A W B) W s)) H 300 := by
  have h1 : 1 ≤ H := by omega
  have ha' : Bounded a (H^1) := by simpa using hA a ha
  have hc := cloneAt_encoding a (cloneScale A W B) W s H (by omega) ha'
    (scales_encoding A W B H hH hW hB hA).2
    (bounded_nat_pow W H hW h1) (bounded_nat_pow s H (by omega) h1)
  exact point_encoding_mono (cap_point_encoding _ H 29 (by omega) hc).1 h1 (by omega)

theorem frame_encoding (B H : ℕ) (hH : 100 ≤ H) (hB : B ≤ H) (i : Fin B) :
    PointBounded (frame (frameParameter B i)) H 300 := by
  have h1 : 1 ≤ H := by omega
  have h2 : 2 ≤ H := by omega
  have hone := bounded_nat_pow 1 H (by omega) h1
  have hi : Bounded ((i.val:ℚ)+1) (H^1) := by
    exact_mod_cast bounded_nat_pow (i.val+1) H (by omega) h1
  have hb := (bounded_nat_pow B H hB h1).add_pow hone h2
  have hp : Bounded (frameParameter B i) (H^7) :=
    hone.sub_pow (((bounded_nat_pow 2 H h2 h1).mul_pow hi).div_pow hb) h2
  exact point_encoding_mono (cap_point_encoding _ H 7 hH hp).2 h1 (by omega)

/-- These are the actual two rational source macro meshes, not an assumed
small input encoding. The denominator is explicitly 8*(n*q+1). -/
theorem source_macro_encoding (n q i H : ℕ) (hi : i ≤ n*q)
    (hH : 8*(n*q+1) ≤ H) :
    Bounded (macroParameter n q (-3/4) i) H ∧
    Bounded (macroParameter n q (5/8) i) H := by
  have hi' : (i:ℤ) ≤ (n*q:ℕ) := by exact_mod_cast hi
  have hH' : (8:ℤ)*((n*q:ℕ)+1) ≤ H := by exact_mod_cast hH
  have hpos : (0:ℤ) < (8:ℤ)*((n*q:ℕ)+1) := by positivity
  have hbase : (0:ℤ) ≤ (n*q:ℕ) := by positivity
  constructor
  · refine ⟨-6*((n*q:ℕ)+1)+(i:ℤ)+1,8*((n*q:ℕ)+1),?_,?_,by omega,?_⟩
    · apply abs_le.mpr
      constructor <;> omega
    · rw [abs_of_pos hpos]
      exact hH'
    · unfold macroParameter
      push_cast
      field_simp
      ring
  · refine ⟨5*((n*q:ℕ)+1)+(i:ℤ)+1,8*((n*q:ℕ)+1),?_,?_,by omega,?_⟩
    · apply abs_le.mpr
      constructor <;> omega
    · rw [abs_of_pos hpos]
      exact hH'
    · unfold macroParameter
      push_cast
      field_simp
      ring

/-- Point membership in the actual fixed double-cap family, including
uncloned dummy macros. This is coordinate provenance, not a bit-bound input. -/
def ActualBase (A : Finset ℚ) (W B : ℕ) (p : Point) : Prop :=
  (∃a∈A, p=original a) ∨
  (∃a∈A, ∃s : ℕ, s ≤ W ∧ p=original (cloneAt a (cloneScale A W B) W s)) ∨
  (∃i : Fin B, p=frame (frameParameter B i))

/-- Actual ordinary, left-rank, and right-rank prototype coordinates. -/
def ActualPrototype (A : Finset ℚ) (W B : ℕ) (p : Point) : Prop :=
  (∃a∈A, p=ordinary a (programScale A W)) ∨
  (∃a∈A, ∃b∈A, ∃ell : ℕ, ell+1 ≤ W ∧
    (p=leftRank a b (cloneScale A W B) W (programScale A W) ell ∨
     p=rightRank a b (cloneScale A W B) W (programScale A W) ell))

theorem actual_base_encoding (A : Finset ℚ) (W B H : ℕ) (hH : 10000 ≤ H)
    (hW : W ≤ H) (hB : B ≤ H) (hA : ∀a∈A, Bounded a H)
    (p : Point) (hp : ActualBase A W B p) : PointBounded p H 300 := by
  rcases hp with ⟨a,ha,rfl⟩ | ⟨a,ha,s,hs,rfl⟩ | ⟨i,rfl⟩
  · have ha' : Bounded a (H^1) := by simpa using hA a ha
    exact point_encoding_mono (cap_point_encoding a H 1 (by omega) ha').1 (by omega) (by omega)
  · exact actual_original_encoding A W B H s hH hW hB hA hs a ha
  · exact frame_encoding B H (by omega) hB i

theorem actual_prototype_encoding (A : Finset ℚ) (W B H : ℕ) (hH : 10000 ≤ H)
    (hW : W ≤ H) (hB : B ≤ H) (hA : ∀a∈A, Bounded a H) (hW2 : 2 ≤ W)
    (p : Point) (hp : ActualPrototype A W B p) : PointBounded p H 300 := by
  rcases hp with ⟨a,ha,rfl⟩ | ⟨a,ha,b,hb,ell,hell,hp⟩
  · exact ordinary_encoding A W B H hH hW hB hA a ha
  · have hh := rank_encoding A W B H ell hH hW hB hA hW2 hell a b ha hb
    rcases hp with rfl | rfl
    · exact hh.1
    · exact hh.2

/-- All actual final program coordinates have a polynomial encoding bound,
using the same radius already proved to preserve the complete local tables. -/
theorem actual_placed_encoding (A : Finset ℚ) (W B M H : ℕ) (hH : 10000 ≤ H)
    (hW : W ≤ H) (hB : B ≤ H) (hM : M ≤ H) (hA : ∀a∈A, Bounded a H) (hW2 : 2 ≤ W)
    (base prototypes : Finset Point)
    (hbase : ∀p∈base, ActualBase A W B p) (hproto : ∀p∈prototypes, ActualPrototype A W B p)
    (r p : Point) (hr : r∈prototypes) (hp : Placed M (constructionRadius base prototypes) r p) :
    PointBounded p H (602*base.card+2719) := by
  have hh := placed_encoding M H 300 (by omega) hM base prototypes
    (fun p hp => actual_base_encoding A W B H hH hW hB hA p (hbase p hp))
    (fun p hp => actual_prototype_encoding A W B H hH hW hB hA hW2 p (hproto p hp)) r p hr hp
  convert hh using 1; ring

theorem actual_placed_binary_coordinates (A : Finset ℚ) (W B M L : ℕ) (hL : 10000 ≤ 2^L)
    (hW : W ≤ 2^L) (hB : B ≤ 2^L) (hM : M ≤ 2^L)
    (hA : ∀a∈A, Bounded a (2^L)) (hW2 : 2 ≤ W)
    (base prototypes : Finset Point)
    (hbase : ∀p∈base, ActualBase A W B p) (hproto : ∀p∈prototypes, ActualPrototype A W B p)
    (r p : Point) (hr : r∈prototypes) (hp : Placed M (constructionRadius base prototypes) r p) :
    ∃ nx dx ny dy : ℤ,
      |nx| ≤ (2:ℤ)^(L*(602*base.card+2719)) ∧
      |dx| ≤ (2:ℤ)^(L*(602*base.card+2719)) ∧ dx≠0 ∧ p.1=(nx:ℚ)/(dx:ℚ) ∧
      |ny| ≤ (2:ℤ)^(L*(602*base.card+2719)) ∧
      |dy| ≤ (2:ℤ)^(L*(602*base.card+2719)) ∧ dy≠0 ∧ p.2=(ny:ℚ)/(dy:ℚ) := by
  have hh := actual_placed_encoding A W B M (2^L) hL hW hB hM hA hW2
    base prototypes hbase hproto r p hr hp
  obtain ⟨nx,dx,hx⟩ := binary_certificate L _ hh.1
  obtain ⟨ny,dy,hy⟩ := binary_certificate L _ hh.2
  exact ⟨nx,dx,ny,dy,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2,hy⟩

#print axioms cap_point_encoding
#print axioms cloneAt_encoding
#print axioms ordinary_encoding
#print axioms rank_encoding
#print axioms actual_original_encoding
#print axioms frame_encoding
#print axioms source_macro_encoding
#print axioms actual_base_encoding
#print axioms actual_prototype_encoding
#print axioms actual_placed_encoding
#print axioms actual_placed_binary_coordinates

end Q4.Candidate.GeometryEncoding

