import Q4.Candidate.OriginalCapAlternation
import Q4.Candidate.PaletteForcing
import Mathlib.Order.Interval.Finset.Fin

/-! Exact finite palette counting on actual rational original-cap chords.
The selected endpoints range over two disjoint consecutive blocks. -/
namespace Q4.Candidate.PaletteCounting
open Q4.Candidate.ConvexSeparation Q4.Candidate.DoubleCapGrid
open Q4.Candidate.OriginalCapAlternation
open scoped BigOperators

/-- A rank is zero based, so its earlier clone count is precisely rank.val. -/
def endpoint {O W : ℕ} (start : ℕ) (h : start+W≤O) (rank : Fin W) : Fin O :=
  ⟨start+rank.val,by omega⟩

def outside (a b W : ℕ) (y : ℕ) : Prop :=
  (y<a ∨ a+W≤y) ∧ (y<b ∨ b+W≤y)

def middle (a b W : ℕ) (y : ℕ) : Prop := a+W≤y ∧ y<b

instance (a b W y : ℕ) : Decidable (outside a b W y) :=
  inferInstanceAs (Decidable ((y<a ∨ a+W≤y) ∧ (y<b ∨ b+W≤y)))

instance (a b W y : ℕ) : Decidable (middle a b W y) :=
  inferInstanceAs (Decidable (a+W≤y ∧ y<b))

/-- All actual early-parent crossings, with shared endpoints excluded. -/
theorem early_cross {O W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (r t s : Fin W) (y : Fin O) (hyout : outside a b W y.val) :
    cross ys (endpoint a ha r) (endpoint b hb t) (endpoint a ha s) y ↔
      if middle a b W y.val then s<r else r<s := by
  have hr := r.isLt
  have ht := t.isLt
  have hs := s.isLt
  have hsel : endpoint a ha r<endpoint b hb t := by simp only [endpoint,Fin.mk_lt_mk]; omega
  rcases hyout.1 with hleft | hright
  · rw [cross_reverse_second,cross_ordered ys hy _ _ _ _ hsel
      (by simp only [endpoint,Fin.lt_def]; omega)]
    simp only [endpoint,Fin.lt_def]
    have hm : ¬middle a b W y.val := by unfold middle; omega
    simp only [hm,ite_false]
    omega
  · rw [cross_ordered ys hy _ _ _ _ hsel
      (by simp only [endpoint,Fin.lt_def]; omega)]
    simp only [endpoint,Fin.lt_def]
    by_cases hm : middle a b W y.val
    · simp only [hm,ite_true]
      have hmid := hm
      unfold middle at hmid
      omega
    · simp only [hm,ite_false]
      unfold middle at hm
      rcases hyout.2 with h | h <;> omega

/-- The actual late-parent crossing table has the complementary rank count. -/
theorem late_cross {O W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (r t s : Fin W) (y : Fin O) (hyout : outside a b W y.val) :
    cross ys (endpoint a ha r) (endpoint b hb t) (endpoint b hb s) y ↔
      if middle a b W y.val then t<s else s<t := by
  have hr := r.isLt
  have ht := t.isLt
  have hs := s.isLt
  have hsel : endpoint a ha r<endpoint b hb t := by simp only [endpoint,Fin.mk_lt_mk]; omega
  rcases hyout.2 with hleft | hright
  · rw [cross_reverse_second,cross_ordered ys hy _ _ _ _ hsel
      (by simp only [endpoint,Fin.lt_def]; omega)]
    simp only [endpoint,Fin.lt_def]
    by_cases hm : middle a b W y.val
    · simp only [hm,ite_true]
      have hmid := hm
      unfold middle at hmid
      omega
    · simp only [hm,ite_false]
      unfold middle at hm
      rcases hyout.1 with h | h <;> omega
  · rw [cross_ordered ys hy _ _ _ _ hsel
      (by simp only [endpoint,Fin.lt_def]; omega)]
    simp only [endpoint,Fin.lt_def]
    have hm : ¬middle a b W y.val := by unfold middle; omega
    simp only [hm,ite_false]
    omega


theorem rank_before_sum {W : ℕ} (r : Fin W) (z : ℤ) :
    (∑ s : Fin W, if s<r then z else 0)=(r.val:ℤ)*z := by
  have he : Finset.univ.filter (fun s : Fin W => s<r)=Finset.Iio r := by ext s; simp
  rw [←Finset.sum_filter,he]
  simp

theorem rank_after_sum {W : ℕ} (r : Fin W) (z : ℤ) :
    (∑ s : Fin W, if r<s then z else 0)=((W:ℤ)-1-r.val)*z := by
  have he : Finset.univ.filter (fun s : Fin W => r<s)=Finset.Ioi r := by ext s; simp
  rw [←Finset.sum_filter,he]
  simp only [Finset.sum_const,Fin.card_Ioi,nsmul_eq_mul]
  have hr := r.isLt
  have hs : ((W-1-r.val:ℕ):ℤ)=(W:ℤ)-1-r.val := by omega
  rw [hs]

def earlyField {O W a b : ℕ} (ys : Fin O → ℚ)
    (ha : a+W≤O) (hb : b+W≤O) (r t : Fin W) (y : Fin O) (z : ℤ) : ℤ :=
  ∑ s : Fin W, if cross ys (endpoint a ha r) (endpoint b hb t) (endpoint a ha s) y then z else 0

def lateField {O W a b : ℕ} (ys : Fin O → ℚ)
    (ha : a+W≤O) (hb : b+W≤O) (r t : Fin W) (y : Fin O) (z : ℤ) : ℤ :=
  ∑ s : Fin W, if cross ys (endpoint a ha r) (endpoint b hb t) (endpoint b hb s) y then z else 0

theorem early_field_affine {O W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (r t : Fin W) (y : Fin O) (hyout : outside a b W y.val) (z : ℤ) :
    earlyField ys ha hb r t y z =
      (if middle a b W y.val then 0 else ((W:ℤ)-1)*z)+
      (if middle a b W y.val then z else -z)*(r.val:ℤ) := by
  unfold earlyField
  simp only [early_cross ys hy ha hb hab r t _ y hyout]
  split_ifs with hm
  · rw [rank_before_sum]; ring
  · rw [rank_after_sum]; ring

theorem late_field_affine {O W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (r t : Fin W) (y : Fin O) (hyout : outside a b W y.val) (z : ℤ) :
    lateField ys ha hb r t y z =
      (if middle a b W y.val then ((W:ℤ)-1)*z else 0)+
      (if middle a b W y.val then -z else z)*(t.val:ℤ) := by
  unfold lateField
  simp only [late_cross ys hy ha hb hab r t _ y hyout]
  split_ifs with hm
  · rw [rank_after_sum]; ring
  · rw [rank_before_sum]; ring

/-- Nonincident palette edges contribute a constant, derived from the actual
cap-crossing predicate and the absence of endpoints inside either block. -/
theorem neutral_cross_independent {O W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (r t r' t' : Fin W) (c d : Fin O) (hcd : c<d)
    (hc : outside a b W c.val) (hd : outside a b W d.val) :
    cross ys (endpoint a ha r) (endpoint b hb t) c d ↔
      cross ys (endpoint a ha r') (endpoint b hb t') c d := by
  have hr := r.isLt
  have ht := t.isLt
  have hr' := r'.isLt
  have ht' := t'.isLt
  have hsel : endpoint a ha r<endpoint b hb t := by simp only [endpoint,Fin.lt_def]; omega
  have hsel' : endpoint a ha r'<endpoint b hb t' := by simp only [endpoint,Fin.lt_def]; omega
  rw [cross_ordered ys hy _ _ _ _ hsel hcd,cross_ordered ys hy _ _ _ _ hsel' hcd]
  simp only [endpoint,Fin.lt_def]
  unfold outside at hc hd
  omega


abbrev CoreEdge (O : ℕ) := {e : Fin O × Fin O // e.1<e.2}

def outsideSet (O W a b : ℕ) : Finset (Fin O) :=
  Finset.univ.filter (fun y => outside a b W y.val)

def spin (color : Bool) : ℤ := if color then 1 else -1

def slopeL {O : ℕ} (a b W : ℕ) (color : Fin O → Bool) : ℤ :=
  ∑ y ∈ outsideSet O W a b, if middle a b W y.val then spin (color y) else -spin (color y)

def slopeR {O : ℕ} (a b W : ℕ) (color : Fin O → Bool) : ℤ :=
  ∑ y ∈ outsideSet O W a b, if middle a b W y.val then -spin (color y) else spin (color y)

/-- This is a sum of actual proper crossings, not an affine surrogate. The
three families have zero, early, or late parent endpoints respectively. -/
def paletteField {O W a b : ℕ} (ys : Fin O → ℚ)
    (ha : a+W≤O) (hb : b+W≤O) (neutral : Finset (CoreEdge O))
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool) (r t : Fin W) : ℤ :=
  (∑ e ∈ neutral, if cross ys (endpoint a ha r) (endpoint b hb t) e.val.1 e.val.2
    then spin (colorN e) else 0)+
  ∑ y ∈ outsideSet O W a b,
    (earlyField ys ha hb r t y (spin (colorL y))+lateField ys ha hb r t y (spin (colorR y)))

/-- The affine identity is proved by summing the actual crossing tables.
No proposed field identity is an input. -/
theorem palette_field_affine {O W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (hW : 0<W)
    (neutral : Finset (CoreEdge O))
    (hneutral : ∀e∈neutral, outside a b W e.val.1.val ∧ outside a b W e.val.2.val)
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool) (r t : Fin W) :
    paletteField ys ha hb neutral colorN colorL colorR r t =
      paletteField ys ha hb neutral colorN colorL colorR ⟨0,hW⟩ ⟨0,hW⟩+
        slopeL a b W colorL*r.val+slopeR a b W colorR*t.val := by
  have hn : (∑ e ∈ neutral, if cross ys (endpoint a ha r) (endpoint b hb t) e.val.1 e.val.2
      then spin (colorN e) else 0)=
      ∑ e ∈ neutral, if cross ys (endpoint a ha ⟨0,hW⟩) (endpoint b hb ⟨0,hW⟩) e.val.1 e.val.2
      then spin (colorN e) else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [neutral_cross_independent ys hy ha hb hab r t ⟨0,hW⟩ ⟨0,hW⟩
      e.val.1 e.val.2 e.property (hneutral e he).1 (hneutral e he).2]
  have hs : (∑ y ∈ outsideSet O W a b,
      (earlyField ys ha hb r t y (spin (colorL y))+lateField ys ha hb r t y (spin (colorR y))))=
      (∑ y ∈ outsideSet O W a b,
      (earlyField ys ha hb ⟨0,hW⟩ ⟨0,hW⟩ y (spin (colorL y))+
        lateField ys ha hb ⟨0,hW⟩ ⟨0,hW⟩ y (spin (colorR y))))+
        slopeL a b W colorL*r.val+slopeR a b W colorR*t.val := by
    unfold slopeL slopeR
    rw [Finset.sum_mul,Finset.sum_mul,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hyset
    have hout : outside a b W y.val := (Finset.mem_filter.mp hyset).2
    rw [early_field_affine ys hy ha hb hab r t y hout,
      late_field_affine ys hy ha hb hab r t y hout,
      early_field_affine ys hy ha hb hab ⟨0,hW⟩ ⟨0,hW⟩ y hout,
      late_field_affine ys hy ha hb hab ⟨0,hW⟩ ⟨0,hW⟩ y hout]
    simp only [Nat.cast_zero,mul_zero,add_zero]
    ring
  unfold paletteField
  rw [hn,hs]
  ring


/-- Each term is a real fixed-color neighbor contribution. A majority of
negative dummy terms forces the total slope strictly negative. -/
theorem signed_sum_negative {O : ℕ} (S D : Finset (Fin O)) (hD : D⊆S)
    (g : Fin O → ℤ) (hg : ∀y∈S, -1≤g y ∧ g y≤1)
    (hgd : ∀y∈D, g y= -1) (hdominant : O<2*D.card) :
    -(O:ℤ)≤∑ y∈S, g y ∧ (∑ y∈S, g y)<0 := by
  have hcardNat : S.card≤O := by simpa using Finset.card_le_univ S
  have hcard : (S.card:ℤ)≤O := by exact_mod_cast hcardNat
  have hdom : (O:ℤ)<2*(D.card:ℤ) := by exact_mod_cast hdominant
  have hlo := Finset.sum_le_sum (fun y hy => (hg y hy).1)
  have h2 : (∑ y∈S, if y∈D then (2:ℤ) else 0)=2*(D.card:ℤ) := by
    rw [←Finset.sum_filter]
    have he : S.filter (fun y => y∈D)=D := by
      ext y
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨hD h,h⟩⟩
    rw [he]
    simp [mul_comm]
  have hhi : (∑ y∈S, g y)≤∑ y∈S, (1-(if y∈D then (2:ℤ) else 0)) := by
    apply Finset.sum_le_sum
    intro y hy
    by_cases hd : y∈D
    · simp only [hd,ite_true,hgd y hd]; norm_num
    · simp only [hd,ite_false,sub_zero]; exact (hg y hy).2
  rw [Finset.sum_sub_distrib,h2] at hhi
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,mul_neg_one] at hlo hhi
  constructor <;> omega

/-- The slopes of the actual palette field are bounded and negative. Only
the dummy colors are specified; all nondummy neighbor colors remain free. -/
theorem palette_slopes_negative {O W a b : ℕ} (D : Finset (Fin O))
    (hD : D⊆outsideSet O W a b) (hmid : ∀y∈D, middle a b W y.val)
    (colorL colorR : Fin O → Bool)
    (hL : ∀y∈D, colorL y=false) (hR : ∀y∈D, colorR y=true)
    (hdominant : O<2*D.card) :
    (-(O:ℤ)≤slopeL a b W colorL ∧ slopeL a b W colorL<0) ∧
    (-(O:ℤ)≤slopeR a b W colorR ∧ slopeR a b W colorR<0) := by
  constructor
  · apply signed_sum_negative (outsideSet O W a b) D hD _ _ _ hdominant
    · intro y _
      unfold spin
      split_ifs <;> norm_num
    · intro y hy
      simp only [hmid y hy,ite_true,hL y hy,spin,Bool.false_eq_true,ite_false]
  · apply signed_sum_negative (outsideSet O W a b) D hD _ _ _ hdominant
    · intro y _
      unfold spin
      split_ifs <;> norm_num
    · intro y hy
      simp only [hmid y hy,ite_true,hR y hy,spin]

/-- Exact dummy contribution, with no asymptotic or discarded endpoint term. -/
theorem dummy_field {O W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (D : Finset (Fin O)) (hD : D⊆outsideSet O W a b)
    (hmid : ∀y∈D, middle a b W y.val) (r t : Fin W) :
    (∑ y∈D, (earlyField ys ha hb r t y (-1)+lateField ys ha hb r t y 1))=
      -(D.card:ℤ)*r.val+(D.card:ℤ)*((W:ℤ)-1-t.val) := by
  calc
    _=∑ y∈D, (-((r.val:ℤ))+((W:ℤ)-1-t.val)) := by
      apply Finset.sum_congr rfl
      intro y hyd
      have hout := (Finset.mem_filter.mp (hD hyd)).2
      rw [early_field_affine ys hy ha hb hab r t y hout,
        late_field_affine ys hy ha hb hab r t y hout]
      simp only [hmid y hyd,ite_true]
      ring
    _=_ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring


abbrev Family {O : ℕ} (W a b : ℕ) (neutral : Finset (CoreEdge O)) :=
  {e // e∈neutral} ⊕ ((Fin W × {y // y∈outsideSet O W a b}) ⊕
    (Fin W × {y // y∈outsideSet O W a b}))

abbrev familyEndpoints {O W a b : ℕ} (ha : a+W≤O) (hb : b+W≤O)
    (neutral : Finset (CoreEdge O)) : Family W a b neutral → Fin O × Fin O
  | .inl e => e.val.val
  | .inr (.inl (r,y)) => (endpoint a ha r,y.val)
  | .inr (.inr (t,y)) => (endpoint b hb t,y.val)

theorem endpoint_injective {O W : ℕ} (a : ℕ) (ha : a+W≤O) :
    Function.Injective (endpoint a ha) := by
  intro r s he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [endpoint] at hv
  omega

/-- The real edge family has neither duplicate neighbors nor repeated labels.
This bounds the actual constant field, not a presumed coefficient size. -/
theorem familyEndpoints_injective {O W a b : ℕ}
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (neutral : Finset (CoreEdge O))
    (hneutral : ∀e∈neutral, outside a b W e.val.1.val ∧ outside a b W e.val.2.val) :
    Function.Injective (familyEndpoints ha hb neutral) := by
  have hleft (r : Fin W) : ¬outside a b W (endpoint a ha r).val := by
    simp only [outside,endpoint,Fin.val_mk]
    have hr := r.isLt
    omega
  have hright (r : Fin W) : ¬outside a b W (endpoint b hb r).val := by
    simp only [outside,endpoint,Fin.val_mk]
    have hr := r.isLt
    omega
  have hlr (r t : Fin W) : endpoint a ha r≠endpoint b hb t := by
    intro he
    have hv := congrArg Fin.val he
    simp only [endpoint] at hv
    have hr := r.isLt
    omega
  intro e f he
  rcases e with n | (⟨r,y⟩ | ⟨t,y⟩) <;> rcases f with n' | (⟨r',y'⟩ | ⟨t',y'⟩)
  · apply congrArg Sum.inl
    apply Subtype.ext
    apply Subtype.ext
    exact he
  · have hh := congrArg Prod.fst he
    change n.val.val.1=endpoint a ha r' at hh
    have hout := (hneutral n.val n.property).1
    rw [hh] at hout
    exact False.elim (hleft r' hout)
  · have hh := congrArg Prod.fst he
    change n.val.val.1=endpoint b hb t' at hh
    have hout := (hneutral n.val n.property).1
    rw [hh] at hout
    exact False.elim (hright t' hout)
  · have hh := congrArg Prod.fst he
    change endpoint a ha r=n'.val.val.1 at hh
    have hout := (hneutral n'.val n'.property).1
    rw [←hh] at hout
    exact False.elim (hleft r hout)
  · have hh1 := congrArg Prod.fst he
    have hh2 := congrArg Prod.snd he
    have hr : r=r' := endpoint_injective a ha hh1
    have hy : y=y' := Subtype.ext hh2
    subst r'; subst y'; rfl
  · have hh := congrArg Prod.fst he
    exact False.elim (hlr r t' hh)
  · have hh := congrArg Prod.fst he
    change endpoint b hb t=n'.val.val.1 at hh
    have hout := (hneutral n'.val n'.property).1
    rw [←hh] at hout
    exact False.elim (hright t hout)
  · have hh := congrArg Prod.fst he
    exact False.elim (hlr r' t hh.symm)
  · have hh1 := congrArg Prod.fst he
    have hh2 := congrArg Prod.snd he
    have ht : t=t' := endpoint_injective b hb hh1
    have hy : y=y' := Subtype.ext hh2
    subst t'; subst y'; rfl

theorem family_card_bound {O W a b : ℕ}
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (neutral : Finset (CoreEdge O))
    (hneutral : ∀e∈neutral, outside a b W e.val.1.val ∧ outside a b W e.val.2.val) :
    neutral.card+2*W*(outsideSet O W a b).card≤O^2 := by
  have hh := Fintype.card_le_of_injective (familyEndpoints ha hb neutral)
    (familyEndpoints_injective ha hb hab neutral hneutral)
  simp only [Family,Fintype.card_sum,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] at hh
  nlinarith


theorem signed_neighbor_bound {α : Type*} [DecidableEq α] (S : Finset α)
    (inc : α → Prop) [DecidablePred inc] (color : α → Bool) :
    |∑ v∈S, if inc v then spin (color v) else 0|≤(S.card:ℤ) := by
  calc
    _≤∑ v∈S, |if inc v then spin (color v) else 0| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ _v∈S, (1:ℤ) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : inc v
      · simp only [hv,ite_true]
        cases color v <;> norm_num [spin]
      · simp only [hv,ite_false,abs_zero]; norm_num
    _=_ := by simp

/-- The constant is the actual field at rank (0,0). Its size is paid by an
injection of the entire finite neighbor family into ordered endpoint pairs. -/
theorem palette_field_bound {O W a b : ℕ} (ys : Fin O → ℚ)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (neutral : Finset (CoreEdge O))
    (hneutral : ∀e∈neutral, outside a b W e.val.1.val ∧ outside a b W e.val.2.val)
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool) (r t : Fin W) :
    |paletteField ys ha hb neutral colorN colorL colorR r t|≤(O:ℤ)^2 := by
  have hn := signed_neighbor_bound neutral
    (fun e => cross ys (endpoint a ha r) (endpoint b hb t) e.val.1 e.val.2) colorN
  have hL (y : Fin O) : |earlyField ys ha hb r t y (spin (colorL y))|≤(W:ℤ) := by
    simpa only [earlyField,Finset.card_univ,Fintype.card_fin] using
      signed_neighbor_bound (Finset.univ : Finset (Fin W))
        (fun s => cross ys (endpoint a ha r) (endpoint b hb t) (endpoint a ha s) y)
        (fun _ => colorL y)
  have hR (y : Fin O) : |lateField ys ha hb r t y (spin (colorR y))|≤(W:ℤ) := by
    simpa only [lateField,Finset.card_univ,Fintype.card_fin] using
      signed_neighbor_bound (Finset.univ : Finset (Fin W))
        (fun s => cross ys (endpoint a ha r) (endpoint b hb t) (endpoint b hb s) y)
        (fun _ => colorR y)
  have hs : |∑ y∈outsideSet O W a b,
      (earlyField ys ha hb r t y (spin (colorL y))+lateField ys ha hb r t y (spin (colorR y)))|
      ≤2*(W:ℤ)*(outsideSet O W a b).card := by
    calc
      _≤∑ y∈outsideSet O W a b,
          |(earlyField ys ha hb r t y (spin (colorL y))+lateField ys ha hb r t y (spin (colorR y)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _≤∑ _y∈outsideSet O W a b, 2*(W:ℤ) := by
        apply Finset.sum_le_sum
        intro y _
        exact (abs_add_le _ _).trans (by linarith [hL y,hR y])
      _=_ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hc : (neutral.card:ℤ)+2*(W:ℤ)*(outsideSet O W a b).card≤(O:ℤ)^2 := by
    exact_mod_cast family_card_bound ha hb hab neutral hneutral
  unfold paletteField
  exact (abs_add_le _ _).trans (by linarith)


/-- A majority of dummy endpoints holds for the manuscript's explicit scale. -/
theorem dummy_dominance (S W : ℕ) (hS : 0<S) (hW : 0<W) :
    514*S*W<2*(512*S*W) := by
  have hp : 0<S*W := Nat.mul_pos hS hW
  nlinarith

/-- Full finite coefficient conclusion for the actual three disjoint palette
families. The integer coefficients are explicit finite crossing sums. -/
theorem palette_parameters {O W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (hW : 0<W)
    (neutral : Finset (CoreEdge O))
    (hneutral : ∀e∈neutral, outside a b W e.val.1.val ∧ outside a b W e.val.2.val)
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool)
    (D : Finset (Fin O)) (hD : D⊆outsideSet O W a b)
    (hmid : ∀y∈D, middle a b W y.val)
    (hL : ∀y∈D, colorL y=false) (hR : ∀y∈D, colorR y=true)
    (hdominant : O<2*D.card) :
    let beta := paletteField ys ha hb neutral colorN colorL colorR ⟨0,hW⟩ ⟨0,hW⟩
    let gammaL := slopeL a b W colorL
    let gammaR := slopeR a b W colorR
    (∀r t, paletteField ys ha hb neutral colorN colorL colorR r t=
      beta+gammaL*r.val+gammaR*t.val) ∧ |beta|≤(O:ℤ)^2 ∧
      (-(O:ℤ)≤gammaL ∧ gammaL<0) ∧ (-(O:ℤ)≤gammaR ∧ gammaR<0) := by
  dsimp only
  exact ⟨palette_field_affine ys hy ha hb hab hW neutral hneutral colorN colorL colorR,
    palette_field_bound ys ha hb hab neutral hneutral colorN colorL colorR ⟨0,hW⟩ ⟨0,hW⟩,
    palette_slopes_negative D hD hmid colorL colorR hL hR hdominant⟩

/-- Reversing an endpoint pair cannot identify two members of the family,
so its true unoriented geometric edges are counted exactly once. -/
theorem family_no_reverse {O W a b : ℕ}
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (neutral : Finset (CoreEdge O))
    (hneutral : ∀e∈neutral, outside a b W e.val.1.val ∧ outside a b W e.val.2.val)
    (e f : Family W a b neutral) :
    familyEndpoints ha hb neutral e≠
      ((familyEndpoints ha hb neutral f).2,(familyEndpoints ha hb neutral f).1) := by
  have hnotL (r : Fin W) (y : Fin O) (hy : outside a b W y.val) : endpoint a ha r≠y := by
    intro he
    have hh := congrArg Fin.val he
    simp only [endpoint] at hh
    have hr := r.isLt
    unfold outside at hy
    omega
  have hnotR (r : Fin W) (y : Fin O) (hy : outside a b W y.val) : endpoint b hb r≠y := by
    intro he
    have hh := congrArg Fin.val he
    simp only [endpoint] at hh
    have hr := r.isLt
    unfold outside at hy
    omega
  intro he
  rcases e with n | (⟨r,y⟩ | ⟨t,y⟩) <;> rcases f with n' | (⟨r',y'⟩ | ⟨t',y'⟩)
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    change n.val.val.1=n'.val.val.2 at h1
    change n.val.val.2=n'.val.val.1 at h2
    have hn := n.val.property
    have hn' := n'.val.property
    rw [h1,h2] at hn
    exact (not_lt_of_ge (le_of_lt hn')) hn
  · have h2 := congrArg Prod.snd he
    exact hnotL r' n.val.val.2 (hneutral n.val n.property).2 h2.symm
  · have h2 := congrArg Prod.snd he
    exact hnotR t' n.val.val.2 (hneutral n.val n.property).2 h2.symm
  · have h1 := congrArg Prod.fst he
    exact hnotL r n'.val.val.2 (hneutral n'.val n'.property).2 h1
  · have h1 := congrArg Prod.fst he
    exact hnotL r y'.val (Finset.mem_filter.mp y'.property).2 h1
  · have h1 := congrArg Prod.fst he
    exact hnotL r y'.val (Finset.mem_filter.mp y'.property).2 h1
  · have h1 := congrArg Prod.fst he
    exact hnotR t n'.val.val.2 (hneutral n'.val n'.property).2 h1
  · have h1 := congrArg Prod.fst he
    exact hnotR t y'.val (Finset.mem_filter.mp y'.property).2 h1
  · have h1 := congrArg Prod.fst he
    exact hnotR t y'.val (Finset.mem_filter.mp y'.property).2 h1


abbrev familyColor {O W a b : ℕ} {neutral : Finset (CoreEdge O)}
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool) : Family W a b neutral → Bool
  | .inl e => colorN e.val
  | .inr (.inl (_,y)) => colorL y.val
  | .inr (.inr (_,y)) => colorR y.val

def familyField {O W a b : ℕ} (ys : Fin O → ℚ)
    (ha : a+W≤O) (hb : b+W≤O) (neutral : Finset (CoreEdge O))
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool) (r t : Fin W) : ℤ :=
  ∑ e : Family W a b neutral,
    if cross ys (endpoint a ha r) (endpoint b hb t)
      (familyEndpoints ha hb neutral e).1 (familyEndpoints ha hb neutral e).2
    then spin (familyColor colorN colorL colorR e) else 0

theorem sum_subtype_mem {α : Type*} [DecidableEq α] (S : Finset α)
    [Fintype {x // x∈S}] (f : α → ℤ) :
    (∑ x : {x // x∈S}, f x.val)=∑ x∈S, f x :=
  (Finset.sum_subtype S (fun _ => Iff.rfl) f).symm

/-- The three-family formula equals the single sum over distinct actual
geometric palette edges. -/
theorem family_field_eq {O W a b : ℕ} (ys : Fin O → ℚ)
    (ha : a+W≤O) (hb : b+W≤O) (neutral : Finset (CoreEdge O))
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool) (r t : Fin W) :
    familyField ys ha hb neutral colorN colorL colorR r t=
      paletteField ys ha hb neutral colorN colorL colorR r t := by
  let fN : CoreEdge O → ℤ := fun e =>
    if cross ys (endpoint a ha r) (endpoint b hb t) e.val.1 e.val.2 then spin (colorN e) else 0
  let fL : Fin W → Fin O → ℤ := fun s y =>
    if cross ys (endpoint a ha r) (endpoint b hb t) (endpoint a ha s) y then spin (colorL y) else 0
  let fR : Fin W → Fin O → ℤ := fun s y =>
    if cross ys (endpoint a ha r) (endpoint b hb t) (endpoint b hb s) y then spin (colorR y) else 0
  unfold familyField
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  change (∑ e : {e // e∈neutral}, fN e.val)+
    ((∑ s : Fin W, ∑ y : {y // y∈outsideSet O W a b}, fL s y.val)+
      ∑ s : Fin W, ∑ y : {y // y∈outsideSet O W a b}, fR s y.val)=
    (∑ e∈neutral, fN e)+∑ y∈outsideSet O W a b,
      ((∑ s : Fin W, fL s y)+(∑ s : Fin W, fR s y))
  rw [sum_subtype_mem neutral fN]
  simp_rw [sum_subtype_mem (outsideSet O W a b)]
  rw [Finset.sum_add_distrib,
    Finset.sum_comm (s:=Finset.univ) (t:=outsideSet O W a b),
    Finset.sum_comm (s:=Finset.univ) (t:=outsideSet O W a b)]


def paletteCost {O W a b : ℕ} (ys : Fin O → ℚ)
    (ha : a+W≤O) (hb : b+W≤O) (neutral : Finset (CoreEdge O))
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool) (r t : Fin W) (x : Bool) : ℤ :=
  ∑ e : Family W a b neutral,
    if cross ys (endpoint a ha r) (endpoint b hb t)
      (familyEndpoints ha hb neutral e).1 (familyEndpoints ha hb neutral e).2
    then (if x=familyColor colorN colorL colorR e then 1 else 0) else 0

/-- The field is exactly cost(true)-cost(false), with unit cost for every
actual crossing and every palette neighbor counted once. -/
theorem palette_cost_difference {O W a b : ℕ} (ys : Fin O → ℚ)
    (ha : a+W≤O) (hb : b+W≤O) (neutral : Finset (CoreEdge O))
    (colorN : CoreEdge O → Bool) (colorL colorR : Fin O → Bool) (r t : Fin W) :
    paletteCost ys ha hb neutral colorN colorL colorR r t true-
      paletteCost ys ha hb neutral colorN colorL colorR r t false=
      paletteField ys ha hb neutral colorN colorL colorR r t := by
  rw [←family_field_eq ys ha hb neutral colorN colorL colorR r t]
  unfold paletteCost familyField
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : cross ys (endpoint a ha r) (endpoint b hb t)
      (familyEndpoints ha hb neutral e).1 (familyEndpoints ha hb neutral e).2
  · cases hc : familyColor colorN colorL colorR e <;> simp [he,spin]
  · simp [he]

end Q4.Candidate.PaletteCounting
#print axioms Q4.Candidate.PaletteCounting.early_cross
#print axioms Q4.Candidate.PaletteCounting.late_cross
#print axioms Q4.Candidate.PaletteCounting.early_field_affine
#print axioms Q4.Candidate.PaletteCounting.late_field_affine
#print axioms Q4.Candidate.PaletteCounting.neutral_cross_independent
#print axioms Q4.Candidate.PaletteCounting.palette_field_affine

#print axioms Q4.Candidate.PaletteCounting.palette_slopes_negative
#print axioms Q4.Candidate.PaletteCounting.dummy_field

#print axioms Q4.Candidate.PaletteCounting.family_card_bound

#print axioms Q4.Candidate.PaletteCounting.palette_field_bound

#print axioms Q4.Candidate.PaletteCounting.palette_parameters
#print axioms Q4.Candidate.PaletteCounting.family_no_reverse

#print axioms Q4.Candidate.PaletteCounting.family_field_eq
#print axioms Q4.Candidate.PaletteCounting.palette_cost_difference
