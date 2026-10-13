import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution

/-! Continuous real tangent subbundles have finite-dimensional local trivializations for the
topology induced by tangent inclusion (Zhang, p.1). -/

namespace HolomorphicAnosov

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]

/-- A family of real tangent subspaces with base-preserving, fibrewise linear local trivializations
in the topology induced by tangent inclusion (Zhang, p.1). -/
structure ContinuousRealTangentSubbundle (I : ModelWithCorners ℝ E H)
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] where
  /-- The family of real tangent subspaces. -/
  toDistribution : RealTangentDistribution I X
  /-- Each base point has a neighbourhood with a finite-dimensional real linear trivialization. -/
  locally_trivial : ∀ x : X, ∃ r : ℕ,
    letI : TopologicalSpace
        (Bundle.TotalSpace (Fin r → ℝ) (fun y : X ↦ ↥(toDistribution y))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
    ∃ e : Bundle.Trivialization (Fin r → ℝ)
        (Bundle.TotalSpace.proj (F := Fin r → ℝ)
          (E := fun y : X ↦ ↥(toDistribution y))),
      x ∈ e.baseSet ∧ e.IsLinear ℝ

end HolomorphicAnosov
