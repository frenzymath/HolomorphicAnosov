import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

noncomputable section
open Set Filter Topology _root_.Topology

namespace HolomorphicAnosov

/-!
Local path connectedness of the transverse base follows from the supplied atlas
itself. The chart selector is installed as a temporary charted-space structure;
no manifold, Hausdorff, connectedness, or countability assumption is added.
-/
theorem transverseSource_locallyPathConnectedSpace
    {M ι : Type*} [TopologicalSpace M]
    (q : ℕ)
    (b : ι → OpenPartialHomeomorph M ((Fin q → ℝ) × ℂ))
    (hcover : ∀ x : M, ∃ i, x ∈ (b i).source) :
    LocallyPathConnectedSpace M := by
  let indexAt : M → ι := fun x ↦ Classical.choose (hcover x)
  have hindex : ∀ x, x ∈ (b (indexAt x)).source :=
    fun x ↦ Classical.choose_spec (hcover x)
  let : ChartedSpace ((Fin q → ℝ) × ℂ) M :=
    { atlas := Set.range b
      chartAt := fun x ↦ b (indexAt x)
      mem_chart_source := hindex
      chart_mem_atlas := fun x ↦ ⟨indexAt x, rfl⟩ }
  exact ChartedSpace.locallyPathConnectedSpace ((Fin q → ℝ) × ℂ) M

end HolomorphicAnosov
