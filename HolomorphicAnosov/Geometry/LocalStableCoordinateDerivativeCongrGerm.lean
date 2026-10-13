import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate

/-! The file proves germ invariance of the restricted transverse derivative. (Zhang, Lemma 2.5) -/

open scoped Manifold
namespace HolomorphicAnosov
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The restricted transverse differential depends only on the germ at the mark. (Zhang, Lemma 2.5) -/
theorem localStableCoordinateDerivative_congr_germ (S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (t t' : X → ℂ) (x : X) (h : t' =ᶠ[nhds x] t) :
    localStableCoordinateDerivative S t' x = localStableCoordinateDerivative S t x := by
  unfold localStableCoordinateDerivative
  have hd := h.mfderiv_eq (I := complexModel d) (I' := 𝓘(ℂ, ℂ))
  ext v
  have hv := congrArg (fun A ↦ (tangentSpaceCastModel 𝓘(ℂ, ℂ) (t' x))
    (A (v : TangentSpace (complexModel d) x))) hd
  exact hv
end HolomorphicAnosov
