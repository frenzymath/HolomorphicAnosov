import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic

/-! This file defines continuous complex tangent subbundles using local complex-linear
trivializations and the topology induced by tangent inclusion. (Ghys, Lemma 2.1, p.589) -/

namespace HolomorphicAnosov

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type*} [TopologicalSpace H]

/-- A complex tangent distribution with local finite-dimensional complex-linear bundle
trivializations in the topology induced by its inclusion in the tangent bundle. (Ghys, Lemma
2.1, p.589) -/
structure ContinuousComplexTangentSubbundle (I : ModelWithCorners ℂ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] where
  toDistribution : ∀ x : M, Submodule ℂ (TangentSpace I x)
  locally_trivial : ∀ x : M, ∃ r : ℕ,
    letI : TopologicalSpace
        (Bundle.TotalSpace (Fin r → ℂ) (fun y : M ↦ ↥(toDistribution y))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I M)) inferInstance
    ∃ e : Bundle.Trivialization (Fin r → ℂ)
        (Bundle.TotalSpace.proj (F := Fin r → ℂ)
          (E := fun y : M ↦ ↥(toDistribution y))),
      x ∈ e.baseSet ∧ e.IsLinear ℂ

end HolomorphicAnosov
