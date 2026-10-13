import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
namespace HolomorphicAnosov

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle

/-- The zero tangent subbundle is holomorphic. (Demailly, V §11, p. 267) -/
theorem holomorphic_bot {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] :
    IsHolomorphicTangentSubbundle (d := d) 0 (fun _ : X ↦ ⊥) := by
  intro x
  refine ⟨Set.univ, (fun i ↦ Fin.elim0 i), Set.mem_univ x,
    ⟨isOpen_univ, ?_, ?_⟩, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro y hy
    exact linearIndependent_empty_type
  · intro y hy
    simp



end HolomorphicAnosov
