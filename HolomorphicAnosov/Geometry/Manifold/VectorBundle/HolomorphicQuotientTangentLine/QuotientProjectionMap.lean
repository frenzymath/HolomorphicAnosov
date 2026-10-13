import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Basic

/-! The tangent-to-quotient total-space projection is a quotient map (Demailly, V §1, pp.253–254,
§11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The tangent-to-quotient total-space projection is a quotient map for the coinduced topology
(Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273). -/
theorem quotient_projection_quotient_map
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) :
    Topology.IsQuotientMap (quotientTangentProjection P) := by
  refine ⟨⟨rfl⟩, ?_⟩
  rintro ⟨x, v⟩
  obtain ⟨w, hw⟩ := (P x).mkQ_surjective v
  exact ⟨⟨x, w⟩, congrArg (TotalSpace.mk x) hw⟩


end HolomorphicAnosov
