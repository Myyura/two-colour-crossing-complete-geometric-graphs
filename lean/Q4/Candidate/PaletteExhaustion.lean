import Q4.Candidate.ProposedPalette

/-! Exhaustion of every actual indexed palette edge by its endpoint types,
including both orders. No class of complete-core palette edges is omitted. -/
namespace Q4.Candidate.PaletteExhaustion
open Q4.Candidate.ProposedPalette

theorem early_exists (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (u : Fin (S*W+D+S*W)) (j : Fin S) (hu : indexedSite S W D hW pi u=.early j) :
    ∃s : Fin W,earlyEndpoint S W D pi j s=u :=
  endpoint_exists (indexed_bounds S W D pi j).1 u ((indexed_fibers S W D hW pi j).early u |>.mp hu)

theorem late_exists (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (u : Fin (S*W+D+S*W)) (j : Fin S) (hu : indexedSite S W D hW pi u=.late j) :
    ∃s : Fin W,lateEndpoint S W D pi j s=u :=
  endpoint_exists (indexed_bounds S W D pi j).2.1 u ((indexed_fibers S W D hW pi j).late u |>.mp hu)

/-- A symmetric predicate holds on every palette pair once proved for the
five real endpoint classes. This is a finite index exhaustion, not a
hypothesis that a palette optimizer has already adopted its colors. -/
theorem all_allowed (S W D : ℕ) (hW : 0<W) (pi : Equiv.Perm (Fin S))
    (Q : Fin (S*W+D+S*W)→Fin (S*W+D+S*W)→Prop)
    (hsym : ∀u v,Q u v→Q v u)
    (hee : ∀j k s t,j≠k→Q (earlyEndpoint S W D pi j s) (earlyEndpoint S W D pi k t))
    (hll : ∀j k s t,j≠k→Q (lateEndpoint S W D pi j s) (lateEndpoint S W D pi k t))
    (hel : ∀j k s t,j≠k→Q (earlyEndpoint S W D pi j s) (lateEndpoint S W D pi k t))
    (hed : ∀j s u,S*W≤u.val∧u.val<S*W+D→Q (earlyEndpoint S W D pi j s) u)
    (hld : ∀j s u,S*W≤u.val∧u.val<S*W+D→Q (lateEndpoint S W D pi j s) u)
    (u v : Fin (S*W+D+S*W)) (h : allowed (indexedSite S W D hW pi u) (indexedSite S W D hW pi v)) : Q u v := by
  cases hu : indexedSite S W D hW pi u <;> cases hv : indexedSite S W D hW pi v
  case early.early j k =>
    obtain ⟨s,rfl⟩ := early_exists S W D hW pi u j hu
    obtain ⟨t,rfl⟩ := early_exists S W D hW pi v k hv
    exact hee j k s t (by simpa only [hu,hv,allowed] using h)
  case early.dummy j =>
    obtain ⟨s,rfl⟩ := early_exists S W D hW pi u j hu
    exact hed j s v ((indexed_dummy S W D hW pi v).mp hv)
  case early.late j k =>
    obtain ⟨s,rfl⟩ := early_exists S W D hW pi u j hu
    obtain ⟨t,rfl⟩ := late_exists S W D hW pi v k hv
    exact hel j k s t (by simpa only [hu,hv,allowed] using h)
  case dummy.early k =>
    obtain ⟨t,rfl⟩ := early_exists S W D hW pi v k hv
    exact hsym _ _ (hed k t u ((indexed_dummy S W D hW pi u).mp hu))
  case dummy.dummy =>
    simp only [hu,hv,allowed] at h
  case dummy.late k =>
    obtain ⟨t,rfl⟩ := late_exists S W D hW pi v k hv
    exact hsym _ _ (hld k t u ((indexed_dummy S W D hW pi u).mp hu))
  case late.early j k =>
    obtain ⟨s,rfl⟩ := late_exists S W D hW pi u j hu
    obtain ⟨t,rfl⟩ := early_exists S W D hW pi v k hv
    exact hsym _ _ (hel k j t s (by simpa only [hu,hv,allowed,ne_comm] using h))
  case late.dummy j =>
    obtain ⟨s,rfl⟩ := late_exists S W D hW pi u j hu
    exact hld j s v ((indexed_dummy S W D hW pi v).mp hv)
  case late.late j k =>
    obtain ⟨s,rfl⟩ := late_exists S W D hW pi u j hu
    obtain ⟨t,rfl⟩ := late_exists S W D hW pi v k hv
    exact hll j k s t (by simpa only [hu,hv,allowed] using h)

end Q4.Candidate.PaletteExhaustion
#print axioms Q4.Candidate.PaletteExhaustion.early_exists
#print axioms Q4.Candidate.PaletteExhaustion.late_exists
#print axioms Q4.Candidate.PaletteExhaustion.all_allowed
