import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Transition
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Trivialization
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.TrivializationLinear

/-! The scalar transition formula for local tangent quotient trivializations (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- On the overlap of two local quotient coordinate domains, the bundle coordinate change equals
multiplication by `D′.θ x (D.T x)` (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273). -/
theorem QuotientLocalData.transition_eq
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D D' : QuotientLocalData P) (x : X) (hx : x ∈ (D.V : Set X) ∩ D'.V) :
    (D.trivialization.coordChangeL ℂ D'.trivialization x : ℂ →L[ℂ] ℂ) =
      D.transition D' x := by
  apply ContinuousLinearMap.ext
  intro c
  change D.trivialization.coordChangeL ℂ D'.trivialization x c = D.transition D' x c
  rw [Trivialization.coordChangeL_apply' _ _ hx]
  change (if h : x ∈ D'.V then D'.L x h ((P x).mkQ (c • D.T x)) else 0) =
    c • D'.θ x (D.T x)
  have hx' : x ∈ D'.V := hx.2
  rw [dite_eq_left hx', D'.apply_mk, map_smul]


end HolomorphicAnosov
