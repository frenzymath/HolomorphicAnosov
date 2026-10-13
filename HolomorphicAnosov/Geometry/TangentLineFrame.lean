import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
namespace HolomorphicAnosov

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle

/-- A nowhere-zero native holomorphic tangent section gives a singleton local frame (Zhang, Thm. 1.3 and Lemma 4.3; Demailly, V §11). -/
theorem holomorphic_line_of_section {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (e : (x : X) → TangentSpace (complexModel d) x)
    (he : ContMDiff (complexModel d) (complexModel d).tangent ∞
      (fun x ↦ (⟨x, e x⟩ : TangentBundle (complexModel d) X)))
    (hne : ∀ x, e x ≠ 0)
    (hspan : ∀ x, S x = Submodule.span ℂ ({e x} : Set _)) :
    IsHolomorphicTangentSubbundle 1 S := by
  intro x
  refine ⟨Set.univ, (fun _ y ↦ e y), Set.mem_univ x, ?_, ?_⟩
  · exact ⟨isOpen_univ, fun _ ↦ he.contMDiffOn,
      fun y _ ↦ LinearIndependent.of_subsingleton (0 : Fin 1) (hne y)⟩
  · intro y _
    simpa only [Set.range_const] using (hspan y).symm


end HolomorphicAnosov
