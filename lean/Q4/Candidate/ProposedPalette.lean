import Q4.Candidate.PaletteCounting

/-! The proposed global palette on all actual original-original edges.
Endpoint-cluster labels determine the prescribed bit; the final edge sum uses
proper crossing on the actual rational cap. -/
namespace Q4.Candidate.ProposedPalette
open Q4.Candidate.PaletteCounting Q4.Candidate.OriginalCapAlternation
open scoped BigOperators

inductive Site (S : ℕ)
  | early : Fin S → Site S
  | dummy : Site S
  | late : Fin S → Site S
  deriving DecidableEq

def allowed {S : ℕ} : Site S → Site S → Prop
  | .early j,.early k => j≠k
  | .late j,.late k => j≠k
  | .early j,.late k => j≠k
  | .late j,.early k => j≠k
  | .dummy,.dummy => False
  | _,_ => True

instance {S : ℕ} (u v : Site S) : Decidable (allowed u v) := by
  cases u <;> cases v <;> unfold allowed <;> infer_instance

/-- Manuscript (5.2), including symmetry under endpoint reversal. -/
def color {S : ℕ} : Site S → Site S → Bool
  | .early j,.late k => decide (j<k)
  | .late k,.early j => decide (j<k)
  | .late _,.late _ => true
  | .late _,.dummy => true
  | .dummy,.late _ => true
  | _,_ => false

theorem allowed_symm {S : ℕ} (u v : Site S) : allowed u v↔allowed v u := by
  cases u <;> cases v <;> simp [allowed,ne_comm]

theorem color_symm {S : ℕ} (u v : Site S) : color u v=color v u := by
  cases u <;> cases v <;> rfl

theorem allowed_early_iff {S : ℕ} (j : Fin S) (v : Site S) :
    allowed (.early j) v ↔ v≠.early j ∧ v≠.late j := by
  cases v <;> simp [allowed,ne_comm]

theorem allowed_late_iff {S : ℕ} (j : Fin S) (v : Site S) :
    allowed (.late j) v ↔ v≠.early j ∧ v≠.late j := by
  cases v <;> simp [allowed,ne_comm]

def palette {O S : ℕ} (site : Fin O → Site S) : Finset (CoreEdge O) :=
  Finset.univ.filter (fun e => allowed (site e.val.1) (site e.val.2))

def neutral {O S : ℕ} (W a b : ℕ) (site : Fin O → Site S) : Finset (CoreEdge O) :=
  (palette site).filter (fun e => outside a b W e.val.1.val ∧ outside a b W e.val.2.val)

def paletteBit {O S : ℕ} (site : Fin O → Site S) (e : CoreEdge O) : Bool :=
  color (site e.val.1) (site e.val.2)

def globalField {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S) (u v : Fin O) : ℤ :=
  ∑ e∈palette site, if cross ys u v e.val.1 e.val.2 then spin (paletteBit site e) else 0

def ordered {O : ℕ} (u v : Fin O) (hne : u≠v) : CoreEdge O :=
  if h : u<v then ⟨(u,v),h⟩ else ⟨(v,u),by exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)⟩

theorem ordered_pair {O : ℕ} (u v : Fin O) (hne : u≠v) :
    (ordered u v hne).val=(u,v) ∨ (ordered u v hne).val=(v,u) := by
  unfold ordered
  split_ifs <;> simp

theorem ordered_eq_iff {O : ℕ} (u v x y : Fin O) (hne : u≠v) (hne' : x≠y) :
    ordered u v hne=ordered x y hne' ↔ (u=x ∧ v=y) ∨ (u=y ∧ v=x) := by
  unfold ordered
  split_ifs <;> simp only [Subtype.mk.injEq,Prod.mk.injEq,Fin.ext_iff] <;>
    simp only [Fin.lt_def] at * <;> omega

theorem ordered_of_increasing {O : ℕ} (e : CoreEdge O) :
    ordered e.val.1 e.val.2 (ne_of_lt e.property)=e := by
  apply Subtype.ext
  simp only [ordered,e.property,dite_eq_left]

/-- The selected fiber hypotheses state only which endpoint labels occupy
the two consecutive blocks; they impose no palette field or cost identity. -/
structure BlockFibers {O S : ℕ} (site : Fin O → Site S) (W a b : ℕ) (j : Fin S) : Prop where
  early : ∀y, site y=.early j ↔ a≤y.val ∧ y.val<a+W
  late : ∀y, site y=.late j ↔ b≤y.val ∧ y.val<b+W

theorem site_endpoint_early {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j) (ha : a+W≤O) (r : Fin W) :
    site (endpoint a ha r)=.early j := by
  apply (hf.early _).2
  simp only [endpoint,Fin.val_mk]
  have hr := r.isLt
  omega

theorem site_endpoint_late {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j) (hb : b+W≤O) (r : Fin W) :
    site (endpoint b hb r)=.late j := by
  apply (hf.late _).2
  simp only [endpoint,Fin.val_mk]
  have hr := r.isLt
  omega

theorem outside_iff {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j) (y : Fin O) :
    outside a b W y.val ↔ site y≠.early j ∧ site y≠.late j := by
  simp only [ne_eq,hf.early,hf.late,outside]
  omega

theorem neutral_outside {O S W a b : ℕ} (site : Fin O → Site S) :
    ∀e∈neutral W a b site, outside a b W e.val.1.val ∧ outside a b W e.val.2.val := by
  intro e he
  exact (Finset.mem_filter.mp he).2

theorem family_endpoint_ne {O W a b : ℕ} (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (N : Finset (CoreEdge O))
    (hN : ∀e∈N, outside a b W e.val.1.val ∧ outside a b W e.val.2.val)
    (e : Family W a b N) :
    (familyEndpoints ha hb N e).1≠(familyEndpoints ha hb N e).2 := by
  intro he
  exact family_no_reverse ha hb hab N hN e e (Prod.ext he he.symm)

def familyToCore {O W a b : ℕ} (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (N : Finset (CoreEdge O))
    (hN : ∀e∈N, outside a b W e.val.1.val ∧ outside a b W e.val.2.val)
    (e : Family W a b N) : CoreEdge O :=
  ordered (familyEndpoints ha hb N e).1 (familyEndpoints ha hb N e).2
    (family_endpoint_ne ha hb hab N hN e)

theorem familyToCore_injective {O W a b : ℕ} (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (N : Finset (CoreEdge O))
    (hN : ∀e∈N, outside a b W e.val.1.val ∧ outside a b W e.val.2.val) :
    Function.Injective (familyToCore ha hb hab N hN) := by
  intro e f he
  unfold familyToCore at he
  rcases (ordered_eq_iff _ _ _ _ _ _).mp he with h | h
  · exact familyEndpoints_injective ha hb hab N hN (Prod.ext h.1 h.2)
  · exact False.elim (family_no_reverse ha hb hab N hN e f (Prod.ext h.1 h.2))


theorem ordered_allowed {O S : ℕ} (site : Fin O → Site S) (u v : Fin O) (hne : u≠v) :
    allowed (site (ordered u v hne).val.1) (site (ordered u v hne).val.2) ↔
      allowed (site u) (site v) := by
  rcases ordered_pair u v hne with h | h
  · simp only [h]
  · simp only [h]; exact allowed_symm _ _

theorem ordered_color {O S : ℕ} (site : Fin O → Site S) (u v : Fin O) (hne : u≠v) :
    paletteBit site (ordered u v hne)=color (site u) (site v) := by
  unfold paletteBit
  rcases ordered_pair u v hne with h | h
  · simp only [h]
  · simp only [h]; exact color_symm _ _

theorem ordered_cross {O : ℕ} (ys : Fin O → ℚ) (r t u v : Fin O) (hne : u≠v) :
    cross ys r t (ordered u v hne).val.1 (ordered u v hne).val.2 ↔cross ys r t u v := by
  rcases ordered_pair u v hne with h | h
  · simp only [h]
  · simp only [h]; exact (cross_reverse_second ys r t u v).symm

theorem family_mem_palette {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (e : Family W a b (neutral W a b site)) :
    familyToCore ha hb hab (neutral W a b site) (neutral_outside site) e∈palette site := by
  simp only [palette,Finset.mem_filter,Finset.mem_univ,true_and,familyToCore,ordered_allowed]
  rcases e with n | (⟨r,y⟩ | ⟨t,y⟩)
  · have hn : n.val∈palette site := (Finset.mem_filter.mp n.property).1
    exact (Finset.mem_filter.mp hn).2
  · change allowed (site (endpoint a ha r)) (site y.val)
    rw [site_endpoint_early site j hf ha r,allowed_early_iff]
    exact (outside_iff site j hf y.val).1 (Finset.mem_filter.mp y.property).2
  · change allowed (site (endpoint b hb t)) (site y.val)
    rw [site_endpoint_late site j hf hb t,allowed_late_iff]
    exact (outside_iff site j hf y.val).1 (Finset.mem_filter.mp y.property).2

theorem family_color_eq {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (e : Family W a b (neutral W a b site)) :
    paletteBit site (familyToCore ha hb hab (neutral W a b site) (neutral_outside site) e)=
      familyColor (paletteBit site) (fun y => color (.early j) (site y))
        (fun y => color (.late j) (site y)) e := by
  unfold familyToCore
  rw [ordered_color]
  rcases e with n | (⟨r,y⟩ | ⟨t,y⟩)
  · rfl
  · change color (site (endpoint a ha r)) (site y.val)=color (.early j) (site y.val)
    rw [site_endpoint_early site j hf ha r]
  · change color (site (endpoint b hb t)) (site y.val)=color (.late j) (site y.val)
    rw [site_endpoint_late site j hf hb t]

theorem endpoint_exists {O W a : ℕ} (ha : a+W≤O) (y : Fin O)
    (hy : a≤y.val ∧ y.val<a+W) : ∃r : Fin W, endpoint a ha r=y := by
  refine ⟨⟨y.val-a,by omega⟩,?_⟩
  apply Fin.ext
  simp only [endpoint,Fin.val_mk]
  omega

theorem familyToCore_eq_of_pair {O W a b : ℕ}
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (N : Finset (CoreEdge O))
    (hN : ∀e∈N, outside a b W e.val.1.val ∧ outside a b W e.val.2.val)
    (e : Family W a b N) (f : CoreEdge O)
    (he : familyEndpoints ha hb N e=f.val ∨ familyEndpoints ha hb N e=(f.val.2,f.val.1)) :
    familyToCore ha hb hab N hN e=f := by
  rw [←ordered_of_increasing f]
  unfold familyToCore
  rw [ordered_eq_iff]
  rcases he with he | he
  · exact Or.inl ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  · exact Or.inr ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- Every member of the global proposed palette has exactly one of the
three forms. In particular no selected or short edge is inserted. -/
theorem palette_exhaustive {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b)
    (f : CoreEdge O) (hfP : f∈palette site) :
    ∃e : Family W a b (neutral W a b site),
      familyToCore ha hb hab (neutral W a b site) (neutral_outside site) e=f := by
  have hp : allowed (site f.val.1) (site f.val.2) := (Finset.mem_filter.mp hfP).2
  have hchoose (y : Fin O) (hy : ¬outside a b W y.val) : site y=.early j ∨ site y=.late j := by
    have hh := outside_iff site j hf y
    tauto
  by_cases hu : outside a b W f.val.1.val
  · by_cases hv : outside a b W f.val.2.val
    · have hn : f∈neutral W a b site := Finset.mem_filter.mpr ⟨hfP,hu,hv⟩
      refine ⟨.inl ⟨f,hn⟩,?_⟩
      apply familyToCore_eq_of_pair
      exact Or.inl rfl
    · have huS : f.val.1∈outsideSet O W a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩
      rcases hchoose f.val.2 hv with h | h
      · obtain ⟨r,hr⟩ := endpoint_exists ha f.val.2 ((hf.early _).1 h)
        refine ⟨.inr (.inl (r,⟨f.val.1,huS⟩)),?_⟩
        apply familyToCore_eq_of_pair
        exact Or.inr (Prod.ext hr rfl)
      · obtain ⟨t,ht⟩ := endpoint_exists hb f.val.2 ((hf.late _).1 h)
        refine ⟨.inr (.inr (t,⟨f.val.1,huS⟩)),?_⟩
        apply familyToCore_eq_of_pair
        exact Or.inr (Prod.ext ht rfl)
  · rcases hchoose f.val.1 hu with h | h
    · have hv : outside a b W f.val.2.val := by
        apply (outside_iff site j hf _).2
        rw [h,allowed_early_iff] at hp
        exact hp
      have hvS : f.val.2∈outsideSet O W a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
      obtain ⟨r,hr⟩ := endpoint_exists ha f.val.1 ((hf.early _).1 h)
      refine ⟨.inr (.inl (r,⟨f.val.2,hvS⟩)),?_⟩
      apply familyToCore_eq_of_pair
      exact Or.inl (Prod.ext hr rfl)
    · have hv : outside a b W f.val.2.val := by
        apply (outside_iff site j hf _).2
        rw [h,allowed_late_iff] at hp
        exact hp
      have hvS : f.val.2∈outsideSet O W a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
      obtain ⟨t,ht⟩ := endpoint_exists hb f.val.1 ((hf.late _).1 h)
      refine ⟨.inr (.inr (t,⟨f.val.2,hvS⟩)),?_⟩
      apply familyToCore_eq_of_pair
      exact Or.inl (Prod.ext ht rfl)


/-- The whole global palette (5.2), on all actual core endpoint pairs, is
exactly the three-family sum. The bijection preserves both crossing and bit. -/
theorem global_field_eq {O S W a b : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (r t : Fin W) :
    globalField ys site (endpoint a ha r) (endpoint b hb t)=
      paletteField ys ha hb (neutral W a b site) (paletteBit site)
        (fun y => color (.early j) (site y)) (fun y => color (.late j) (site y)) r t := by
  rw [←family_field_eq]
  symm
  unfold familyField globalField
  apply Finset.sum_bij (fun e _ => familyToCore ha hb hab (neutral W a b site) (neutral_outside site) e)
  · intro e _
    exact family_mem_palette site j hf ha hb hab e
  · intro e _ f _ he
    exact familyToCore_injective ha hb hab (neutral W a b site) (neutral_outside site) he
  · intro f hfP
    obtain ⟨e,he⟩ := palette_exhaustive site j hf ha hb hab f hfP
    exact ⟨e,Finset.mem_univ _,he⟩
  · intro e _
    rw [family_color_eq site j hf ha hb hab e]
    simp only [familyToCore,ordered_cross]

def dummies {O S : ℕ} (site : Fin O → Site S) : Finset (Fin O) :=
  Finset.univ.filter (fun y => site y=.dummy)

theorem dummies_outside {O S W a b : ℕ} (site : Fin O → Site S) (j : Fin S)
    (hf : BlockFibers site W a b j) : dummies site⊆outsideSet O W a b := by
  intro y hy
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,(outside_iff site j hf y).2 ?_⟩
  have hd := (Finset.mem_filter.mp hy).2
  simp [hd]

/-- Finite Lemma 5.2 for the globally defined proposed palette. The input
conditions describe only the endpoint blocks and dummy locations. All fields,
integer coefficients, and bounds are proved from actual geometric crossings. -/
theorem proposed_palette_parameters {O S W a b : ℕ} (ys : Fin O → ℚ) (hy : StrictMono ys)
    (site : Fin O → Site S) (j : Fin S) (hf : BlockFibers site W a b j)
    (ha : a+W≤O) (hb : b+W≤O) (hab : a+W≤b) (hW : 0<W)
    (hmid : ∀y, site y=.dummy → a+W≤y.val ∧ y.val<b)
    (hdominant : O<2*(dummies site).card) :
    let beta := globalField ys site (endpoint a ha ⟨0,hW⟩) (endpoint b hb ⟨0,hW⟩)
    let gammaL := slopeL a b W (fun y => color (.early j) (site y))
    let gammaR := slopeR a b W (fun y => color (.late j) (site y))
    (∀r t, globalField ys site (endpoint a ha r) (endpoint b hb t)=
      beta+gammaL*r.val+gammaR*t.val) ∧ |beta|≤(O:ℤ)^2 ∧
      (-(O:ℤ)≤gammaL ∧ gammaL<0) ∧ (-(O:ℤ)≤gammaR ∧ gammaR<0) := by
  have hparams := palette_parameters ys hy ha hb hab hW (neutral W a b site)
    (neutral_outside site) (paletteBit site)
    (fun y => color (.early j) (site y)) (fun y => color (.late j) (site y))
    (dummies site) (dummies_outside site j hf)
    (fun y hyd => hmid y (Finset.mem_filter.mp hyd).2)
    (by intro y hyd; simp only [(Finset.mem_filter.mp hyd).2,color])
    (by intro y hyd; simp only [(Finset.mem_filter.mp hyd).2,color]) hdominant
  dsimp only at hparams ⊢
  simp_rw [global_field_eq ys site j hf ha hb hab]
  exact hparams


/-- Explicit finite layout: S early W-blocks, D dummy endpoints, then S late
W-blocks. pi labels the late physical blocks by their selected macro labels. -/
def indexedSite (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (y : Fin (S*W+D+S*W)) : Site S :=
  if he : y.val<S*W then .early ⟨y.val/W,(Nat.div_lt_iff_lt_mul hW).2 he⟩
  else if hd : y.val<S*W+D then .dummy
  else .late (pi ⟨(y.val-(S*W+D))/W,(Nat.div_lt_iff_lt_mul hW).2 (by have hy := y.isLt; omega)⟩)

theorem indexed_dummy (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (y : Fin (S*W+D+S*W)) :
    indexedSite S W D hW pi y=.dummy ↔ S*W≤y.val ∧ y.val<S*W+D := by
  unfold indexedSite
  split_ifs <;> simp_all

theorem indexed_fibers (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) (j : Fin S) :
    BlockFibers (indexedSite S W D hW pi) W (j.val*W) (S*W+D+(pi.symm j).val*W) j := by
  have hj : (j.val+1)*W≤S*W := Nat.mul_le_mul_right W (by omega)
  constructor
  · intro y
    unfold indexedSite
    split_ifs with he hd
    · simp only [Site.early.injEq,Fin.ext_iff]
      rw [Nat.div_eq_iff hW]
      omega
    · constructor
      · intro h; cases h
      · intro h; exfalso; nlinarith [h.2]
    · constructor
      · intro h; cases h
      · intro h; exfalso; nlinarith [h.2]
  · intro y
    unfold indexedSite
    split_ifs with he hd
    · constructor
      · intro h; cases h
      · intro h; exfalso; omega
    · constructor
      · intro h; cases h
      · intro h; exfalso; omega
    · simp only [Site.late.injEq]
      rw [←Equiv.eq_symm_apply]
      simp only [Fin.ext_iff]
      rw [Nat.div_eq_iff hW]
      omega

theorem indexed_bounds (S W D : ℕ) (pi : Equiv.Perm (Fin S)) (j : Fin S) :
    j.val*W+W≤S*W+D+S*W ∧
    S*W+D+(pi.symm j).val*W+W≤S*W+D+S*W ∧
    j.val*W+W≤S*W+D+(pi.symm j).val*W := by
  have hj : (j.val+1)*W≤S*W := Nat.mul_le_mul_right W (by omega)
  have hk : ((pi.symm j).val+1)*W≤S*W := Nat.mul_le_mul_right W (by omega)
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem indexed_dummy_middle (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S)) (j : Fin S)
    (y : Fin (S*W+D+S*W)) (hy : indexedSite S W D hW pi y=.dummy) :
    j.val*W+W≤y.val ∧ y.val<S*W+D+(pi.symm j).val*W := by
  have hd := (indexed_dummy S W D hW pi y).1 hy
  have hj : (j.val+1)*W≤S*W := Nat.mul_le_mul_right W (by omega)
  constructor <;> nlinarith

theorem indexed_dummy_card (S W D : ℕ) (hS : 0<S) (hW : 0<W) (pi : Equiv.Perm (Fin S)) :
    (dummies (indexedSite S W D hW pi)).card=D := by
  have hp : 0<S*W := Nat.mul_pos hS hW
  let lo : Fin (S*W+D+S*W) := ⟨S*W,by omega⟩
  let hi : Fin (S*W+D+S*W) := ⟨S*W+D,by omega⟩
  have he : dummies (indexedSite S W D hW pi)=Finset.Ico lo hi := by
    ext y
    simp only [dummies,Finset.mem_filter,Finset.mem_univ,true_and,
      indexed_dummy,Finset.mem_Ico,Fin.le_def,Fin.lt_def,lo,hi]
  rw [he,Fin.card_Ico]
  dsimp [lo,hi]
  omega


def earlyEndpoint (S W D : ℕ) (pi : Equiv.Perm (Fin S)) (j : Fin S) (r : Fin W) :
    Fin (S*W+D+S*W) := endpoint (j.val*W) (indexed_bounds S W D pi j).1 r

def lateEndpoint (S W D : ℕ) (pi : Equiv.Perm (Fin S)) (j : Fin S) (t : Fin W) :
    Fin (S*W+D+S*W) := endpoint (S*W+D+(pi.symm j).val*W) (indexed_bounds S W D pi j).2.1 t

/-- No layout or palette-counting premise remains: endpoint categories are
computed from the finite index, and late order is an arbitrary permutation. -/
theorem indexed_palette_parameters (S W D : ℕ) (hS : 0<S) (hW : 0<W)
    (pi : Equiv.Perm (Fin S)) (ys : Fin (S*W+D+S*W) → ℚ) (hy : StrictMono ys)
    (hD : 2*S*W<D) (j : Fin S) :
    let site := indexedSite S W D hW pi
    let a := j.val*W
    let b := S*W+D+(pi.symm j).val*W
    let beta := globalField ys site (earlyEndpoint S W D pi j ⟨0,hW⟩) (lateEndpoint S W D pi j ⟨0,hW⟩)
    let gammaL := slopeL a b W (fun y => color (.early j) (site y))
    let gammaR := slopeR a b W (fun y => color (.late j) (site y))
    (∀r t, globalField ys site (earlyEndpoint S W D pi j r) (lateEndpoint S W D pi j t)=
      beta+gammaL*r.val+gammaR*t.val) ∧ |beta|≤((S*W+D+S*W:ℕ):ℤ)^2 ∧
      (-((S*W+D+S*W:ℕ):ℤ)≤gammaL ∧ gammaL<0) ∧
      (-((S*W+D+S*W:ℕ):ℤ)≤gammaR ∧ gammaR<0) := by
  have hdom : S*W+D+S*W<2*(dummies (indexedSite S W D hW pi)).card := by
    rw [indexed_dummy_card S W D hS hW pi]
    nlinarith
  exact proposed_palette_parameters ys hy (indexedSite S W D hW pi) j
    (indexed_fibers S W D hW pi j) (indexed_bounds S W D pi j).1
    (indexed_bounds S W D pi j).2.1 (indexed_bounds S W D pi j).2.2 hW
    (indexed_dummy_middle S W D hW pi j) hdom

theorem candidate_dummy_majority (S W : ℕ) (hS : 0<S) (hW : 0<W) :
    2*S*W<512*S*W := by
  have hp := Nat.mul_pos hS hW
  nlinarith

def globalCost {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S)
    (u v : Fin O) (x : Bool) : ℤ :=
  ∑ e∈palette site, if cross ys u v e.val.1 e.val.2 then
    (if x=paletteBit site e then 1 else 0) else 0

/-- Exact coefficient of the actual global palette cost. -/
theorem global_cost_difference {O S : ℕ} (ys : Fin O → ℚ) (site : Fin O → Site S)
    (u v : Fin O) : globalCost ys site u v true-globalCost ys site u v false=globalField ys site u v := by
  unfold globalCost globalField
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : cross ys u v e.val.1 e.val.2
  · cases paletteBit site e <;> simp [he,spin]
  · simp [he]

end Q4.Candidate.ProposedPalette
#print axioms Q4.Candidate.ProposedPalette.ordered_eq_iff
#print axioms Q4.Candidate.ProposedPalette.outside_iff
#print axioms Q4.Candidate.ProposedPalette.familyToCore_injective

#print axioms Q4.Candidate.ProposedPalette.family_mem_palette
#print axioms Q4.Candidate.ProposedPalette.family_color_eq
#print axioms Q4.Candidate.ProposedPalette.palette_exhaustive

#print axioms Q4.Candidate.ProposedPalette.global_field_eq
#print axioms Q4.Candidate.ProposedPalette.proposed_palette_parameters

#print axioms Q4.Candidate.ProposedPalette.indexed_fibers
#print axioms Q4.Candidate.ProposedPalette.indexed_dummy_card

#print axioms Q4.Candidate.ProposedPalette.indexed_palette_parameters
#print axioms Q4.Candidate.ProposedPalette.global_cost_difference
