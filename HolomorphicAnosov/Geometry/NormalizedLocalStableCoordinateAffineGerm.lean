import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinateAffine
import HolomorphicAnosov.Geometry.LocalStableCoordinateDerivativeCongrGerm

/-! Normalized local stable-coordinate germs agree under locally affine changes of transverse
function. (Zhang, Lemma 2.5 and Eq. (15), p. 8) -/

open scoped Manifold
namespace HolomorphicAnosov
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- A locally affine change of transverse function preserves the normalized stable-coordinate germ
at the marked point. (Zhang, Lemma 2.5 and Eqs. (14)–(15), pp. 7–8) -/
theorem normalizedLocalStableCoordinate_affine_germ (S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (t t' : X → ℂ) (x : X) (a : ℂˣ) (b : ℂ)
    (ht : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) t x)
    (h : t' =ᶠ[nhds x] fun y ↦ (a : ℂ) * t y + b) :
    normalizedLocalStableCoordinate S t' x =ᶠ[nhds x]
      normalizedLocalStableCoordinate S t x := by
  have hd := localStableCoordinateDerivative_congr_germ S
    (fun y ↦ (a : ℂ) * t y + b) t' x h
  have hx := h.self_of_nhds
  filter_upwards [h] with p hp
  calc
    normalizedLocalStableCoordinate S t' x p =
        normalizedLocalStableCoordinate S (fun y ↦ (a : ℂ) * t y + b) x p := by
      simp only [normalizedLocalStableCoordinate, hd, hx, hp]
    _ = normalizedLocalStableCoordinate S t x p :=
      normalizedLocalStableCoordinate_affine S t x p a b ht
end HolomorphicAnosov
