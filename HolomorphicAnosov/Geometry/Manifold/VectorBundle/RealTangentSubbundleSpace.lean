import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution

/-! The total space of a real tangent distribution carries the topology induced by its inclusion
into the tangent bundle. -/

namespace HolomorphicAnosov

open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

abbrev RealSubbundleTotalSpace
    (I : ModelWithCorners ℝ E H) (P : RealTangentDistribution I X) (r : ℕ) :=
  Bundle.TotalSpace (Fin r → ℝ) (fun x : X ↦ ↥(P x))

def realSubbundleInclusion
    (I : ModelWithCorners ℝ E H) (P : RealTangentDistribution I X) (r : ℕ) :
    RealSubbundleTotalSpace I P r → TangentBundle I X :=
  fun z ↦ ⟨z.proj, z.snd.val⟩

@[instance_reducible]
def realSubbundleTotalSpaceTopology
    (I : ModelWithCorners ℝ E H) (P : RealTangentDistribution I X) (r : ℕ)
    [IsManifold I ∞ X] : TopologicalSpace (RealSubbundleTotalSpace I P r) :=
  TopologicalSpace.induced (realSubbundleInclusion I P r) inferInstance

end
end HolomorphicAnosov
