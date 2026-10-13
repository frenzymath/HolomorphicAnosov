import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Transition

/-! Holomorphicity of scalar transition operators between local tangent quotient coordinates
(Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The scalar transition operator between two local quotient coordinates is holomorphic on the
intersection of their base domains (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273). -/
theorem QuotientLocalData.transition_smooth
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D D' : QuotientLocalData P) :
    ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞ (D.transition D')
      ((D.V : Set X) ∩ D'.V) := by
  have hs : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞
      (fun x ↦ D'.θ x (D.T x)) ((D.V : Set X) ∩ D'.V) := by
    intro x hx
    exact ((D'.hscalar ⟨x, D.T x⟩ hx.2).comp x
      (D.hT.contMDiffAt (D.V.isOpen.mem_nhds hx.1))).contMDiffWithinAt
  exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).contMDiff.comp_contMDiffOn hs


end HolomorphicAnosov
