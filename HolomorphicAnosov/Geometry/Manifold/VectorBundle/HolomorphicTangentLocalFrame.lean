import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Independent holomorphic tangent frames are ordered families of holomorphic tangent sections that
are pointwise complex linearly independent (Demailly, II §3.1, pp.85–86, V Def. 11.1, p.267,
(14.1), p.273). -/

namespace HolomorphicAnosov

universe u

open scoped ContDiff

/-- An ordered family of tangent sections on an open set `U` whose total-space maps are holomorphic
and whose values are complex linearly independent at every point of `U` (Demailly, II
(3.4)–(3.5), pp.85–86, V (11.1), p.267). -/
def IsHolomorphicTangentFrame {d r : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (U : Set X) (s : Fin r → (y : X) → TangentSpace (complexModel d) y) : Prop :=
  IsOpen U ∧
    (∀ i, ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨y, s i y⟩ : TangentBundle (complexModel d) X)) U) ∧
    ∀ y ∈ U, LinearIndependent ℂ (fun i ↦ s i y)

end HolomorphicAnosov
