import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! Tangent quotient fibres, their projection, their coinduced total-space topology, and the one-
dimensional quotient condition (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273; Zhang,
§2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The complex tangent fibre modulo the subspace `P x` (Demailly, V (14.1), p.273). -/
abbrev HolomorphicQuotientTangentLine
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) (x : X) :=
  TangentSpace (complexModel d) x ⧸ P x

/-- The fibrewise quotient projection from the tangent total space to the quotient total space
(Demailly, V (14.1), p.273; Zhang, §2.1, p.4). -/
def quotientTangentProjection
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) :
    TangentBundle (complexModel d) X → TotalSpace ℂ (HolomorphicQuotientTangentLine P) :=
  fun v ↦ ⟨v.proj, (P v.proj).mkQ v.snd⟩

/-- The topology on the quotient total space coinduced by the tangent quotient projection (Demailly,
V §1, pp.253–254, (14.1), p.273). -/
instance quotientTangentLineTopology
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) :
    TopologicalSpace (TotalSpace ℂ (HolomorphicQuotientTangentLine P)) :=
  TopologicalSpace.coinduced (quotientTangentProjection P) inferInstance

/-- Every tangent quotient fibre has complex dimension one (Zhang, §2.1, p.4). -/
def IsQuotientTangentLine
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) : Prop :=
  ∀ x : X, Module.finrank ℂ (HolomorphicQuotientTangentLine P x) = 1


end HolomorphicAnosov
