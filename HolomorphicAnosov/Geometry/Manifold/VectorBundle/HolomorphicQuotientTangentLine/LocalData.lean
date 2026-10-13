import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Basic

/-! Local tangent quotient coordinate data with holomorphic transverse lifts and coefficient maps
(Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Local quotient coordinates consisting of a holomorphic transverse tangent lift, a holomorphic
total coefficient map, and inverse fibrewise continuous linear equivalences. -/
structure QuotientLocalData
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) where
  V : TopologicalSpace.Opens X
  T : (x : X) → TangentSpace (complexModel d) x
  θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ
  hT : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
    (fun y ↦ (⟨y, T y⟩ : TangentBundle (complexModel d) X)) V
  hscalar : ∀ p : TangentBundle (complexModel d) X, p.proj ∈ V →
    ContMDiffAt (complexModel d).tangent 𝓘(ℂ, ℂ) ∞
      (fun q : TangentBundle (complexModel d) X ↦ θ q.proj q.snd) p
  L : ∀ x, x ∈ V → HolomorphicQuotientTangentLine P x ≃L[ℂ] ℂ
  apply_mk : ∀ x hx v, L x hx ((P x).mkQ v) = θ x v
  symm_apply : ∀ x hx c, (L x hx).symm c = (P x).mkQ (c • T x)


end HolomorphicAnosov
