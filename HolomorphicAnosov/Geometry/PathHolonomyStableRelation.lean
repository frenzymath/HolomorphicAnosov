import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation

/-! Finite stable plaque-chain holonomy preserves stable partition classes. (Ghys, Prop. 2.2, p.
589; pp. 594, 597–598) -/

namespace HolomorphicAnosov

universe u v

/-- Every point in the source of a finite stable plaque-chain holonomy remains in its stable
partition class. (Ghys, Prop. 2.2, p. 589; pp. 594, 597–598) -/
theorem path_holonomy_stable_related
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u, v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {a b : unitInterval}
    {h : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
    (hchain : PlaqueChainAlong F γ a b h)
    (z : F.ULeaf (γ a).val) (hz : z ∈ h.source) :
    F.stablePartition z.val (h z).val := by
  induction hchain with
  | single a b hab e hsegment =>
    obtain ⟨w, hw⟩ := e.source_in_plaque z hz
    have hm := e.coordinate_map z w hz hw
    apply Quotient.exact
    rw [← hw, hm, F.stable_label, F.stable_label]
  | @compose a b c h h' hab hbc left right ih ih' =>
    exact F.stablePartition.trans (ih z hz.1) (ih' (h z) hz.2)

end HolomorphicAnosov

