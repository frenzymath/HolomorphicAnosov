import HolomorphicAnosov.Analysis.BoundedContinuousInvariantSections
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularity
import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle

import HolomorphicAnosov.Analysis.Complex.ComplexDerivativeOfRealSplitting

namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- Once the source's ambient real differentiability has been established, its
leafwise derivative identities imply ambient holomorphy on the SAME open domain.
Source: step 7 below, Demailly I §3.B (3.8)–(3.9), pp.22–23. Apply the preceding
pointwise real-to-complex derivative proof everywhere, then the complex Cauchy
regularity theorem gives all orders of complex differentiability. Kernel and
nonvanishing statements retain the actual Fréchet derivative of q. This does
not assert that the required ambient real derivative follows from separate
leafwise regularity; that remains the named Journé provider's application. -/
theorem holomorphicSubmersionOfRealSplitting
    {d : ℕ} {O : Set (ComplexModel d)} (hO : IsOpen O)
    (q : ComplexModel d → ℂ) (L : ComplexModel d → ComplexModel d →L[ℝ] ℂ)
    (hreal : ∀ x ∈ O, HasFDerivAt q (L x) x)
    (S U : ComplexModel d → Submodule ℂ (ComplexModel d))
    (hsplit : ∀ x ∈ O, IsCompl (S x) (U x))
    (hU : ∀ x ∈ O, ∀ v ∈ U x, L x v = 0)
    (hS : ∀ x ∈ O, ∀ c : ℂ, ∀ v ∈ S x, L x (c • v) = c • L x v)
    (hSinj : ∀ x ∈ O, ∀ v ∈ S x, L x v = 0 → v = 0)
    (hSnonzero : ∀ x ∈ O, ∃ v ∈ S x, L x v ≠ 0) :
    ContDiffOn ℂ ∞ q O ∧
      ∀ x ∈ O, LinearMap.ker (fderiv ℂ q x).toLinearMap = U x ∧
        fderiv ℂ q x ≠ 0 := by
  have hd (x : ComplexModel d) (hx : x ∈ O) :=
    complexDerivativeOfRealSplitting (L x) (hreal x hx) (S x) (U x)
      (hsplit x hx) (hU x hx) (hS x hx) (hSinj x hx) (hSnonzero x hx)
  have hc : DifferentiableOn ℂ q O :=
    fun x hx ↦ (hd x hx).1.differentiableAt.differentiableWithinAt
  have hpi : DifferentiableOn ℂ (fun x (_ : Fin 1) ↦ q x) O :=
    differentiableOn_pi.mpr (fun _ ↦ hc)
  have hsmooth : ContDiffOn ℂ ∞ (fun x (_ : Fin 1) ↦ q x) O :=
    (complex_contDiffOn_iff_differentiableOn hO).mpr hpi
  exact ⟨contDiffOn_pi.mp hsmooth (0 : Fin 1), fun x hx ↦ (hd x hx).2⟩




end HolomorphicAnosov
