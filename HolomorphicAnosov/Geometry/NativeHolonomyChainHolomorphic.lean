import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! This file proves holomorphicity of finite compositions of plaque transports on their intrinsic
leaf carriers. (Ghys, pp. 589, 594, 597–598; Zhang, p. 10) -/

open scoped ContDiff

namespace HolomorphicAnosov

universe u v

/-- If every one-box plaque transport is holomorphic, every finite plaque chain is holomorphic on
its source after identification with the specified intrinsic leaves. (Ghys, pp. 589, 594,
597–598; Zhang, p. 10) -/
theorem native_holonomy_chain_holomorphic
    {d s t : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (realModel d) ∞ M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u, v} f Ps Pu s t) :
    letI := A.realAmbientCharts
    letI (x : M) : TopologicalSpace (UnstableAsymptoticLeaf f x) := A.unstableTopology x
    letI (x : M) : ChartedSpace (Fin (A.nativeU x).rank → ℝ)
        (UnstableAsymptoticLeaf f x) := A.unstableCharts x
    letI (x : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f x) :=
      (A.complexU1 x).charts
    (∀ (x y : M) (e : LocalPlaqueTransport A.F x y),
      let h := A.transportUnstableLocalMap x y e.map
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ h h.source) →
    ∀ q : Quotient A.F.stablePartition,
    letI := A.F.stableTopology q
    ∀ (x y : IntrinsicFoliationLeaf A.F.stablePartition q) (γ : Path x y)
      (a b : unitInterval)
      (h : OpenPartialHomeomorph (A.F.ULeaf (γ a).val) (A.F.ULeaf (γ b).val)),
      PlaqueChainAlong A.F γ a b h →
      let h' := A.transportUnstableLocalMap (γ a).val (γ b).val h
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ h' h'.source := by
  let := A.realAmbientCharts
  let (x : M) : TopologicalSpace (UnstableAsymptoticLeaf f x) := A.unstableTopology x
  let (x : M) : ChartedSpace (Fin (A.nativeU x).rank → ℝ)
      (UnstableAsymptoticLeaf f x) := A.unstableCharts x
  let (x : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f x) :=
    (A.complexU1 x).charts
  intro hlocal q
  let := A.F.stableTopology q
  intro x y γ a b h hchain
  induction hchain with
  | single a b hab e hsegment => exact hlocal _ _ e
  | @compose a b c h h' hab hbc left right ih ih' =>
    have hc := ih'.comp' ih
    simpa [NativeTransverseAsymptoticIdentification.transportUnstableLocalMap,
      OpenPartialHomeomorph.trans_source, Set.preimage, Set.ofPred_and,
      Function.comp_def] using hc

end HolomorphicAnosov

