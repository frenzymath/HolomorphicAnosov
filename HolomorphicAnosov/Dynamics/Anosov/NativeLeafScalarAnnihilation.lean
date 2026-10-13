import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility

open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.HPS

universe u

attribute [local instance] complex_isManifold_real

/-- A holomorphic scalar function locally constant on a native real leaf kills
the original real tangent distribution, expressed in the canonical complex
tangent fibre.

Source: the pinned Mathlib manifold chain rule `mfderiv_comp`, its germ
congruence `Filter.EventuallyEq.mfderiv_eq`, and scalar restriction of
`HasFDerivWithinAt`; HPS, *Invariant Manifolds* (1977), pp.68–72 and 115–116,
for the native leaf immersion and its actual tangent range.

Proof: restrict the complex differential to the reals in the same preferred
charts. The scalar composite with the native inclusion has the germ of a
constant, hence zero differential. The chain rule makes the ambient real
differential vanish on the range of the inclusion differential. The native
leaf's tangent identity identifies this range with the original distribution.
Scalar restriction and the canonical same-chart tangent identification give
the asserted complex differential identity. No embedded-leaf topology or
complex structure on the intrinsic leaf is assumed. -/
theorem NativeLeaf.scalar_annihilates_of_eventually_constant
    {d r : ℕ} {X L : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    {D : RealTangentDistribution (realModel d) X}
    (leaf : NativeLeaf (r := r) D L) (q : X → ℂ) (z : L)
    (hq : MDifferentiableAt (complexModel d) 𝓘(ℂ) q (leaf.inclusion z))
    (hconst : (q ∘ leaf.inclusion) =ᶠ[𝓝 z] fun _ ↦ q (leaf.inclusion z)) :
    ∀ v ∈ D (leaf.inclusion z),
      mfderiv (complexModel d) 𝓘(ℂ) q (leaf.inclusion z)
        ((complexTangentToReal d (leaf.inclusion z)).symm v) = 0 := by
  have hreal : HasMFDerivAt (realModel d) 𝓘(ℝ, ℂ) q (leaf.inclusion z)
      ((mfderiv (complexModel d) 𝓘(ℂ) q (leaf.inclusion z)).restrictScalars ℝ) :=
    ⟨hq.continuousAt, hq.hasMFDerivAt.2.restrictScalars ℝ⟩
  have hzero := hconst.mfderiv_eq (I := 𝓘(ℝ, Fin r → ℝ)) (I' := 𝓘(ℝ, ℂ))
  rw [mfderiv_const, mfderiv_comp z hreal.mdifferentiableAt
    (leaf.immersion.contMDiff.mdifferentiable (by simp) z), hreal.mfderiv] at hzero
  simp only [ContinuousLinearMap.comp_zero] at hzero
  intro v hv
  rw [← leaf.tangent z] at hv
  obtain ⟨w, rfl⟩ := hv
  exact DFunLike.congr_fun hzero w

end HolomorphicAnosov.HPS

