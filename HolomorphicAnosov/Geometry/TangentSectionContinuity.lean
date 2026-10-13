import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Topology.VectorBundle.Basic

namespace HolomorphicAnosov

universe u

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle
attribute [local instance] complex_isManifold_real

/-- Pointwise scalar multiplication preserves continuity of tangent sections at a point.
(Zhang, Lemma 4.3, p. 15) -/
theorem continuousAt_section_smul {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (v : (x : X) → TangentSpace (complexModel d) x) (c : X → ℂ) (x : X)
    (hv : ContinuousAt (fun y ↦ (⟨y, v y⟩ : TangentBundle (complexModel d) X)) x)
    (hc : ContinuousAt c x) :
    ContinuousAt (fun y ↦ (⟨y, c y • v y⟩ : TangentBundle (complexModel d) X)) x := by
  rw [FiberBundle.continuousAt_section (ComplexModel d)] at hv ⊢
  apply (hc.smul hv).congr_of_eventuallyEq
  filter_upwards [(trivializationAt (ComplexModel d)
    (fun y : X ↦ TangentSpace (complexModel d) y) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt (ComplexModel d)
      (fun y : X ↦ TangentSpace (complexModel d) y) x)] with y hy
  exact ((trivializationAt (ComplexModel d)
    (fun y : X ↦ TangentSpace (complexModel d) y) x).linear ℂ hy).map_smul (c y) (v y)



end HolomorphicAnosov
