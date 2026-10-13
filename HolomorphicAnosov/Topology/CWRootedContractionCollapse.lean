import Mathlib.Topology.CWComplex.Classical.Subcomplex
import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.CWComplex.HomotopyExtension
import HolomorphicAnosov.Topology.BasedCollapseHomotopyInverse

/-!
# A based inverse to collapse of a rooted contractible CW subcomplex

Source: Hatcher, *Algebraic Topology*, Propositions 0.16–0.17, pp. 15–16,
and the rooted contraction used in Proposition 1A.1, p. 84.
-/

namespace HolomorphicAnosov.Topology

open Set
open scoped unitInterval

/-- A contraction of a CW subcomplex fixing its root gives a based homotopy
inverse to its collapse.

Source: Hatcher, Propositions 0.16–0.17, pp. 15–16, as used in Proposition 1A.1,
p. 84. Compose the intrinsic contraction with the inclusion of the subcomplex
and extend it to X by the CW homotopy extension property, starting at the identity.
The extension preserves the subcomplex at each time, is constant there at time one,
and fixes its root throughout. Its time-one map factors through the collapse to
give r. Composing the entire extension with the collapse also descends, giving
the homotopy from the quotient identity to q ∘ r relative to the collapsed root.
The extension itself gives the homotopy from the identity to r ∘ q relative to
the original root. No finiteness or local-finiteness hypothesis is used. -/
theorem cw_rooted_contraction_collapse_inverse
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)]
    (T : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set X))
    (a : (T : Set X))
    (C : ContinuousMap.HomotopyRel (ContinuousMap.id (T : Set X))
      (ContinuousMap.const (T : Set X) a) {a}) :
    ∃ r : C(GoodPair.Collapsed (T : Set X), X),
      r (GoodPair.collapse (T : Set X) a.val) = a.val ∧
      Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id X)
        (r.comp (GoodPair.collapse (T : Set X))) {a.val}) ∧
      Nonempty (ContinuousMap.HomotopyRel
        (ContinuousMap.id (GoodPair.Collapsed (T : Set X)))
        ((GoodPair.collapse (T : Set X)).comp r)
        {GoodPair.collapse (T : Set X) a.val}) := by
  let h : C(unitInterval × (T : Set X), X) :=
    ⟨fun p ↦ (C p).val, continuous_subtype_val.comp C.continuous⟩
  obtain ⟨H, hzero, hT, _⟩ := cw_pair_homotopy_extension T (ContinuousMap.id X) h
    (fun b ↦ congrArg Subtype.val (C.apply_zero b))
  let endpoint : C(X, X) :=
    ⟨fun x ↦ H (1, x), H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let K : ContinuousMap.HomotopyRel (ContinuousMap.id X) endpoint {a.val} :=
    { toContinuousMap := H
      map_zero_left := hzero
      map_one_left := fun _ ↦ rfl
      prop' := by
        intro t x hx
        have hx' : x = a.val := hx
        subst x
        exact (hT t a).trans (congrArg Subtype.val (C.eq_fst t (mem_singleton a))) }
  have hpres : ∀ t x, x ∈ (T : Set X) → K (t, x) ∈ (T : Set X) := by
    intro t x hx
    change H (t, x) ∈ (T : Set X)
    rw [hT t ⟨x, hx⟩]
    exact (C (t, ⟨x, hx⟩)).property
  have hend : ∀ x ∈ (T : Set X), endpoint x = a.val := by
    intro x hx
    exact (hT 1 ⟨x, hx⟩).trans (congrArg Subtype.val (C.apply_one ⟨x, hx⟩))
  obtain ⟨r, hr, _, hleft, hright⟩ :=
    exists_based_collapse_homotopy_inverse (T : Set X) a.val a.property endpoint K hpres hend
  exact ⟨r, hr, hleft, hright⟩

end HolomorphicAnosov.Topology

