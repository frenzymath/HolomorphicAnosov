import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentLocalFrame

/-! Rank-`r` holomorphic tangent subbundles are families of complex tangent subspaces locally
spanned by independent holomorphic tangent frames (Demailly, V Def. 11.1, p.267, (14.1), p.273;
Zhang, Thm. 1.3, p.3). -/

namespace HolomorphicAnosov

universe u

open scoped ContDiff

/-- A family `P` of complex tangent subspaces is a rank-`r` holomorphic subbundle if each point has
a neighbourhood with an independent holomorphic tangent frame spanning `P` (Demailly, V (11.1),
p.267, (14.1), p.273). -/
def IsHolomorphicTangentSubbundle {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (r : ℕ) (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) : Prop :=
  ∀ x : X, ∃ (U : Set X) (s : Fin r → (y : X) → TangentSpace (complexModel d) y),
    x ∈ U ∧ IsHolomorphicTangentFrame U s ∧
      ∀ y ∈ U, Submodule.span ℂ (Set.range (fun i ↦ s i y)) = P y

end HolomorphicAnosov
