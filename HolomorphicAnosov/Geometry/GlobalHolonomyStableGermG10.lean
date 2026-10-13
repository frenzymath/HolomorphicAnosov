import HolomorphicAnosov.Geometry.GlobalHolonomy
import HolomorphicAnosov.Geometry.PathHolonomyStableRelation

namespace HolomorphicAnosov

open Filter Set _root_.Topology
universe u v

/-- Near its marked source point, whole-leaf holonomy sends each point to a point in the same stable
partition class. (Ghys, proof of Thm B, p.598) -/
theorem global_holonomy_eventually_stable_related_g10
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u, v} s t M)
    (C : IntrinsicComplexUnstableLeaves F) (G : GlobalSHolonomyData F C)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
    ∀ᶠ z : F.ULeaf x.val in 𝓝 (F.uPoint x.val),
      F.stablePartition z.val (G.transport γ z).val := by
  have hcastCont {a b : M} (h : a = b) : Continuous (castIntrinsicULeaf F h) := by
    cases h
    exact continuous_id
  have hcastPoint {a b : M} (h : a = b) :
      castIntrinsicULeaf F h (F.uPoint a) = F.uPoint b := by
    cases h
    rfl
  have hcastVal {a b : M} (h : a = b) (z : F.ULeaf a) :
      (castIntrinsicULeaf F h z).val = z.val := by
    cases h
    rfl
  let e := (G.localContinuation γ).representative 0 1 (by simp)
  let h₀ := (congrArg Subtype.val γ.source).symm
  have hsrc : ∀ᶠ z : F.ULeaf x.val in 𝓝 (F.uPoint x.val),
      castIntrinsicULeaf F h₀ z ∈ e.map.source := by
    have ht := (hcastCont h₀).continuousAt (x := F.uPoint x.val)
    change Tendsto _ _ (𝓝 (castIntrinsicULeaf F h₀ (F.uPoint x.val))) at ht
    rw [hcastPoint] at ht
    exact ht.eventually (e.map.open_source.mem_nhds e.source_point)
  filter_upwards [Germ.coe_eq.mp (G.extends_local γ), hsrc] with z hz hs
  rw [hz, hcastVal]
  have hrel := path_holonomy_stable_related F γ e.chain
    (castIntrinsicULeaf F h₀ z) hs
  simpa only [hcastVal] using hrel

end HolomorphicAnosov
