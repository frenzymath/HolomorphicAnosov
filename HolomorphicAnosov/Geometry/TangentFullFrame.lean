import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
namespace HolomorphicAnosov

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle

/-- A native holomorphic tangent bundle admits a full local frame (Demailly, II §3.1 and V §11). -/
theorem holomorphic_top {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] :
    IsHolomorphicTangentSubbundle (d := d) d (fun _ : X ↦ ⊤) := by
  classical
  intro x
  let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let b := Pi.basisFun ℂ (Fin d)
  refine ⟨e.baseSet, e.localFrame b, FiberBundle.mem_baseSet_trivializationAt
    (ComplexModel d) (TangentSpace (complexModel d)) x,
    ⟨e.open_baseSet, ?_, ?_⟩, ?_⟩
  · intro i
    exact e.contMDiffOn_localFrame_baseSet ∞ b i
  · intro y hy
    simpa only [e.localFrame_apply_of_mem_baseSet b hy] using
      (e.basisAt b hy).linearIndependent
  · intro y hy
    simpa only [e.localFrame_apply_of_mem_baseSet b hy] using (e.basisAt b hy).span_eq


end HolomorphicAnosov
