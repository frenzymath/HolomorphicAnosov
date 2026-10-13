import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! The global C⁰ size of a connection difference is the supremum of the norms of its frame-form
evaluations on closed unit tangent balls for a Riemannian metric (Zhang, Eq. (5), Lemma 2.2,
Estimate (6), p.5). -/

open Set TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.QuotientLineConnection

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}

/-- The norms of differences of connection frame forms evaluated on closed unit tangent balls within
each frame domain (Zhang, Lemma 2.2, Estimate (6), p.5). -/
def differenceValues
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    (D D' : Connection U) : Set ℝ :=
  {t : ℝ | ∃ (V : Opens X) (e : HolomorphicFrame U V) (x : X), x ∈ V ∧
    ∃ v : TangentSpace (realModel d) x,
      g.inner x v v ≤ 1 ∧ t = ‖D.form V e x v - D'.form V e x v‖}

/-- The real supremum of `differenceValues`, giving the global C⁰ difference norm when the value set
is bounded (Zhang, Lemma 2.2, Estimate (6), p.5). -/
def c0Distance
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    (D D' : Connection U) : ℝ :=
  sSup (differenceValues g D D')

end HolomorphicAnosov.QuotientLineConnection
