import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! Continuity of scalar multiplication in the complex tangent total space (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Scalar multiplication in the complex tangent total space is continuous. -/
theorem continuous_tangent_scale :
    Continuous (fun p : TangentBundle (complexModel d) X × ℂ ↦
      (⟨p.1.proj, p.2 • p.1.snd⟩ : TangentBundle (complexModel d) X)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) p.1.proj
  have hp : p.1.proj ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  apply (FiberBundle.continuousAt_totalSpace (ComplexModel d) _).mpr
  refine ⟨?_, ?_⟩
  · change ContinuousAt (fun q : TangentBundle (complexModel d) X × ℂ ↦ q.1.proj) p
    exact ((FiberBundle.continuous_proj (ComplexModel d)
      (TangentSpace (complexModel d))).comp continuous_fst).continuousAt
  · have hc : ContinuousAt (fun q : TangentBundle (complexModel d) X × ℂ ↦
        q.2 • (e q.1).2) p := continuous_snd.continuousAt.smul
      ((e.continuousAt (e.mem_source.mpr hp)).snd.comp continuous_fst.continuousAt)
    apply hc.congr_of_eventuallyEq
    filter_upwards [((FiberBundle.continuous_proj (ComplexModel d)
      (TangentSpace (complexModel d))).comp continuous_fst).continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds hp)] with q hq
    exact (e.linear ℂ hq).map_smul q.2 q.1.snd


end HolomorphicAnosov
