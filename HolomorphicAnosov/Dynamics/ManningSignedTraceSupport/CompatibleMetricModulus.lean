import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- On a compact carrier the identity between two metrics with the same topology is
uniformly continuous by Heine--Cantor. The explicit old/new structures give its
literal metric modulus, used to transfer coding mesh and expansivity. -/
theorem compatible_metric_modulus {X : Type*} [old : MetricSpace X] [CompactSpace X]
    (new : MetricSpace X)
    (ht : new.toUniformSpace.toTopologicalSpace = old.toUniformSpace.toTopologicalSpace) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : X, new.dist x y < δ → old.dist x y < ε := by
  have hcomp : @CompactSpace X new.toUniformSpace.toTopologicalSpace := ht.symm ▸
    (inferInstance : @CompactSpace X old.toUniformSpace.toTopologicalSpace)
  have hcont : @Continuous X X new.toUniformSpace.toTopologicalSpace
      old.toUniformSpace.toTopologicalSpace id := by
    rw [ht]
    exact @continuous_id X old.toUniformSpace.toTopologicalSpace
  have huc := @CompactSpace.uniformContinuous_of_continuous X X new.toUniformSpace
    old.toUniformSpace hcomp id hcont
  exact fun ε hε ↦ by
    obtain ⟨δ, hδ, hd⟩ :=
      (@Metric.uniformContinuous_iff X X new.toPseudoMetricSpace
        old.toPseudoMetricSpace id).mp huc ε hε
    exact ⟨δ, hδ, fun x y h ↦ hd h⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
