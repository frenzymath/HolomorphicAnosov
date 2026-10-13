import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open scoped Manifold ContDiff
namespace HolomorphicAnosov
universe u v

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the normalized stable coordinate along an immersed stable plaque recovers its
tangent inclusion. (Zhang, Eq. (14), p. 7, and Lemma 2.5, p. 8) -/
theorem normalizedLocalStableCoordinate_derivative
    {d k : ℕ} {X : Type u} {P : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace P] [ChartedSpace (ComplexModel k) P]
    (S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (j : P → X) (t : X → ℂ) (z : P)
    (hj : MDifferentiableAt (complexModel k) (complexModel d) j z)
    (ht : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) t (j z))
    (himage : (mfderiv (complexModel k) (complexModel d) j z).range ≤ S (j z))
    (hB : (localStableCoordinateDerivative S t (j z)).IsInvertible)
    (c : S (j z) ≃L[ℂ] ℂ) :
    (S (j z)).subtypeL.comp (c.symm.toContinuousLinearMap.comp
      (mvfderiv (complexModel k)
        (fun p ↦ c (normalizedLocalStableCoordinate S t (j z) (j p))) z)) =
      mfderiv (complexModel k) (complexModel d) j z := by
  let B := localStableCoordinateDerivative S t (j z)
  let A : ℂ →L[ℂ] ℂ := c.toContinuousLinearMap.comp B.inverse
  have hdt : MDifferentiableAt (complexModel k) 𝓘(ℂ, ℂ) (t ∘ j) z := ht.comp z hj
  have hsub : MDifferentiableAt (complexModel k) 𝓘(ℂ, ℂ)
      (fun p ↦ t (j p) - t (j z)) z := hdt.sub mdifferentiableAt_const
  have hd : mvfderiv (complexModel k)
      (fun p ↦ c (normalizedLocalStableCoordinate S t (j z) (j p))) z =
      A.comp ((mvfderiv (complexModel d) t (j z)).comp
        (mfderiv (complexModel k) (complexModel d) j z)) := by
    change mvfderiv (complexModel k) (A ∘ (fun p ↦ t (j p) - t (j z))) z = _
    rw [mvfderiv_comp z A.differentiableAt.mdifferentiableAt hsub,
      mvfderiv_eq_fderiv, A.fderiv]
    change A.comp (mvfderiv (complexModel k)
      (fun p ↦ t (j p) - t (j z)) z) = _
    rw [mvfderiv_fun_sub (g := fun p ↦ t (j p)) (g' := fun _ ↦ t (j z))
      hdt mdifferentiableAt_const, mvfderiv_const, sub_zero]
    exact congrArg A.comp (mvfderiv_comp z ht hj)
  rw [hd]
  ext v
  let w : S (j z) := ⟨mfderiv (complexModel k) (complexModel d) j z v,
    himage ⟨v, rfl⟩⟩
  change (c.symm (c (B.inverse (B w)))).val = w.val
  rw [c.symm_apply_apply]
  have hw := congrArg (fun L ↦ L w) hB.inverse_comp_self
  exact congrArg Subtype.val hw
end HolomorphicAnosov
