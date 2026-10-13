import HolomorphicAnosov.Ghys.AffineSchwarzianQuadraticForm
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation

/-! Holomorphicity of finite plaque-chain transports. -/

open scoped ContDiff Manifold
namespace HolomorphicAnosov
universe u v

/-- If each single-box transport is biholomorphic in the supplied intrinsic complex charts, then every finite plaque chain is biholomorphic on its full source and target (Ghys, *Holomorphic Anosov systems* (1995), pp.594 and 597–598; Zhang, Proposition 2.9 and Lemma 2.10, p.10).-/
theorem intrinsic_holonomy_chain_holomorphic
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u, v} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F)
    (hlocal : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
      letI := C.charts (Quotient.mk F.unstablePartition x)
      letI := C.charts (Quotient.mk F.unstablePartition y)
      Ghys.IsHolomorphicCurveLocalMap e.map) :
    ∀ q : Quotient F.stablePartition,
    letI := F.stableTopology q
    ∀ (x y : IntrinsicFoliationLeaf F.stablePartition q) (γ : Path x y)
      (a b : unitInterval)
      (h : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)),
      PlaqueChainAlong F γ a b h →
      letI := C.charts (Quotient.mk F.unstablePartition (γ a).val)
      letI := C.charts (Quotient.mk F.unstablePartition (γ b).val)
      Ghys.IsHolomorphicCurveLocalMap h := by
  let (x : M) : ChartedSpace (ComplexModel 1) (F.ULeaf x) :=
    C.charts (Quotient.mk F.unstablePartition x)
  intro q
  let := F.stableTopology q
  intro x y γ a b h hchain
  induction hchain with
  | single a b hab e hsegment => exact hlocal _ _ e
  | @compose a b c h h' hab hbc left right ih ih' =>
    exact ⟨ih'.1.comp' ih.1, ih.2.comp' ih'.2⟩

end HolomorphicAnosov
