import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace HolomorphicAnosov.Ghys

open Set
open scoped ContDiff Manifold
universe u v

/-- A covering of a complex manifold inherits a complex atlas for which its projection is a local
diffeomorphism. (Lee, Prop. 1.15 p.9; Ghys, §5 pp.597–598) -/
theorem projective_cover_chart_data
    {d : ℕ} {M : Type u} {E : Type v}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace E] [T2Space E] [SecondCountableTopology E]
    (p : E → M) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    ∃ charts : ChartedSpace (ComplexModel d) E,
      letI := charts
      ∃ smooth : IsManifold (complexModel d) ∞ E,
        letI := smooth
        IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p ∧
        (∀ y : E, ∃ e : OpenPartialHomeomorph E M,
          y ∈ e.source ∧ Set.EqOn e p e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) := by
  obtain ⟨A, hA, _, hpSmooth, hlocal, _, _⟩ :=
    complex_cover_pullback_atlas (d := d) p hp hsurj
  refine ⟨A, ?_⟩
  let := A
  refine ⟨hA, ?_⟩
  let := hA
  constructor
  · rw [isLocalDiffeomorph_iff]
    intro y
    obtain ⟨e, hy, he, hforward, hinverse⟩ := hlocal y
    let φ : PartialDiffeomorph (complexModel d) (complexModel d)
        E M ∞ := {
      toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := hforward
      contMDiffOn_invFun := hinverse }
    exact ⟨φ, hy, fun x hx ↦ (he hx).symm⟩
  · exact hlocal

end HolomorphicAnosov.Ghys

