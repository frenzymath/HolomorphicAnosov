import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import HolomorphicAnosov.Geometry.LocalStableCoordinateDerivativeAffine

/-! The normalized local stable coordinate is invariant under nonzero affine changes of transverse
coordinate. (Zhang, Eqs. (14)–(15) and Lemma 2.5, pp. 7–8) -/

open scoped Manifold
namespace HolomorphicAnosov
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- A nonzero affine change of transverse coordinate leaves the normalized stable-coordinate value
unchanged. (Zhang, Lemma 2.5, p. 8) -/
theorem normalizedLocalStableCoordinate_affine (S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (t : X → ℂ) (x p : X) (a : ℂˣ) (b : ℂ)
    (ht : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) t x) :
    normalizedLocalStableCoordinate S (fun y ↦ (a : ℂ) * t y + b) x p =
      normalizedLocalStableCoordinate S t x p := by
  unfold normalizedLocalStableCoordinate
  rw [localStableCoordinateDerivative_affine S t x a b ht]
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ a
  have he : (a : ℂ) • localStableCoordinateDerivative S t x =
      e.toContinuousLinearMap.comp (localStableCoordinateDerivative S t x) := by
    ext v
    simp [e, mul_comm]
  rw [he, ContinuousLinearMap.inverse_equiv_comp]
  change (localStableCoordinateDerivative S t x).inverse
    (e.symm ((a : ℂ) * t p + b - ((a : ℂ) * t x + b))) = _
  have hdiff : (a : ℂ) * t p + b - ((a : ℂ) * t x + b) = e (t p - t x) := by
    simp [e, mul_sub, mul_comm]
  rw [hdiff, e.symm_apply_apply]
end HolomorphicAnosov
