import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Pretrivialization
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ContinuousTangentScale
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.QuotientProjectionMap

/-! Continuity of the inverse local tangent quotient coordinates (Demailly, V §1, pp.253–254, §11,
p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The inverse local quotient coordinate map is continuous on its target (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273). -/
theorem QuotientLocalData.continuousOn_inverse
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLocalData P) :
    ContinuousOn D.pretrivialization.toPartialEquiv.symm D.pretrivialization.target := by
  have ht : ContinuousOn (fun p : X × ℂ ↦
      (⟨p.1, D.T p.1⟩ : TangentBundle (complexModel d) X))
      ((D.V : Set X) ×ˢ univ) := D.hT.continuousOn.comp continuousOn_fst
    (fun p (hp : p ∈ (D.V : Set X) ×ˢ univ) ↦ hp.1)
  have hs : ContinuousOn
      (fun p : X × ℂ ↦ (⟨p.1, p.2 • D.T p.1⟩ : TangentBundle (complexModel d) X))
      ((D.V : Set X) ×ˢ univ) :=
    continuous_tangent_scale.comp_continuousOn (ht.prodMk continuousOn_snd)
  exact (quotient_projection_quotient_map P).continuous.comp_continuousOn hs


end HolomorphicAnosov
