import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.SmoothNormalizedSection
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.DolbeaultPullbackSquareBound
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.EventualConormBound
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NormalizedStableSpans
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NormalizedPullbackTestSequence
import HolomorphicAnosov.Analysis.Distribution.FramePairingConvergence
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NormalizedPullbackConvergence
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.JacobianDominatedSquareDecay
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.VolumeJacobianDominatedSquareDecay
import HolomorphicAnosov.Analysis.Distribution.L2DbarPairing
import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import HolomorphicAnosov.Analysis.InnerProductSpace.JacobianSingularValues
import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Paper.Zhang.NormalizedHermitianJacobian
import HolomorphicAnosov.Paper.Zhang.NormalizedVectorDolbeaultPullback
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HermitianTangentFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! The normalized continuous stable section is a global holomorphic frame for the stable line
bundle. (Zhang, Lemmas 4.1, 4.3, pp.13–16, (24)–(31); Demailly, I, Lemma 3.29(a), p.28) -/

open scoped ContDiff

attribute [local instance] HolomorphicAnosov.complex_isManifold_real

namespace HolomorphicAnosov

noncomputable section

universe u

open Bundle Filter MeasureTheory DistributionalSection in
open scoped Topology in
/-- The normalized continuous stable section is holomorphic and spans each stable fibre, giving a
holomorphic trivialization of the stable line bundle. (Zhang, Lemma 4.3, pp.15–16) -/
theorem stable_vector_holomorphic
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hS_real : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x)
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hcompl : ∀ x, IsCompl (S x) (U x))
    (hrank : ∀ x, Module.finrank ℂ (S x) = 1)
    (hS_invariant : ∀ x, (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x))
    (hU_invariant : ∀ x, (U x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = U (f x))
    (θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ_holomorphic : ∀ c : OpenPartialHomeomorph X (ComplexModel d),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ∀ j : Fin d, DifferentiableOn ℂ
        (fun z ↦ θ (c.symm z) (hermitianTangentChartFrame c z j)) c.target)
    (hθ_nonzero : ∀ x, θ x ≠ 0)
    (hθ_kernel : ∀ x, LinearMap.ker (θ x).toLinearMap = U x)
    (μ : ℂ) (hμ_pos : 0 < ‖μ‖) (hμ_lt : ‖μ‖ < 1)
    (hθ_pullback : ∀ x (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (e : (x : X) → TangentSpace (complexModel d) x)
    (he_continuous : Continuous
      (fun x ↦ (⟨x, e x⟩ : TangentBundle (complexModel d) X)))
    (he_stable : ∀ x, e x ∈ S x)
    (he_normalized : ∀ x, θ x (e x) = 1) :
    ContMDiff (complexModel d) (complexModel d).tangent ∞
      (fun x ↦ (⟨x, e x⟩ : TangentBundle (complexModel d) X)) ∧
      (∀ x, e x ≠ 0) ∧
      (∀ x, S x = Submodule.span ℂ ({e x} : Set (TangentSpace (complexModel d) x))) := by
  have hframe := fun x ↦ normalized_stable_spans (S x) (θ x).toLinearMap (e x)
    (hrank x) (he_stable x) (he_normalized x)
  refine ⟨?_, fun x ↦ (hframe x).1, fun x ↦ (hframe x).2⟩
  have hθsmooth : IsHolomorphicComplexOneForm θ := by
    intro c hc j
    have hscalar : ContDiffOn ℂ ∞
        (fun z (_ : Fin 1) ↦ θ (c.symm z) (hermitianTangentChartFrame c z j)) c.target :=
      (complex_contDiffOn_iff_differentiableOn c.open_target).mpr
        (differentiableOn_pi.mpr (fun _ ↦ hθ_holomorphic c hc j))
    exact (contDiffOn_pi.mp hscalar) 0
  obtain ⟨e₀, he₀smooth, he₀normalized⟩ :=
    exists_smooth_normalized_tangent_section θ hθsmooth hθ_nonzero
  
  
  have happrox := normalized_stable_pullback_convergence f S U hcompl hS_invariant
    θ hθ_kernel μ hμ_lt hθ_pullback e e₀ he_stable he_normalized he₀normalized
  
  
  
  have happ := normalized_pullback_test_sequence hd f a S U hS_real hU_real hcompl hrank
    hS_invariant hU_invariant θ hθ_holomorphic hθ_nonzero hθ_kernel μ hμ_pos hμ_lt
    hθ_pullback e he_continuous he_stable he_normalized
  obtain ⟨sn, hcoeff⟩ := happ
  
  
  have hsn (n : ℕ) :
      Continuous (fun x ↦ (⟨x, sn n x⟩ : TangentBundle (complexModel d) X)) := by
    rw [continuous_iff_continuousAt]
    intro x
    let c := chartAt (ComplexModel d) x
    let fr := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
    have hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
      IsManifold.chart_mem_maximalAtlas x
    have hfr : IsHolomorphicFrame (d := d) fr :=
      ⟨inferInstance, fr.contMDiffOn, fr.contMDiffOn_symm⟩
    have hx : x ∈ c.source := mem_chart_source _ x
    have hxf : x ∈ fr.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ x
    have hcx : c x ∈ frameDomain c fr :=
      ⟨c.map_source hx, by change c.symm (c x) ∈ fr.baseSet; rwa [c.left_inv hx]⟩
    have hcoords : ContinuousAt
        (fun z ↦ fun k : Fin d ↦ coefficient (sn n) c fr k z) (c x) := by
      apply continuousAt_pi.mpr
      intro k
      exact ((hcoeff c hc fr hfr k).1 n).continuousOn.continuousAt
        ((frameDomain c fr).isOpen.mem_nhds hcx)
    rw [FiberBundle.continuousAt_section (ComplexModel d)]
    apply (hcoords.comp (c.continuousAt hx)).congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    change (fr ⟨y, sn n y⟩).2 = (fr ⟨c.symm (c y), sn n (c.symm (c y))⟩).2
    rw [c.left_inv hy]
  apply distributional_holomorphic_section_criterion e sn he_continuous hsn
  · intro c hc fr hfr k φ
    obtain ⟨ε, hε, hbound⟩ := (hcoeff c hc fr hfr k).2.1 φ
    exact DistributionalSection.frame_regular_pairing_tendsto sn e hsn he_continuous
      c fr k φ ε hε hbound
  · intro c hc fr hfr k j φ
    exact l2_dbar_pairing_tendsto_zero (frameDomain c fr)
      (fun n ↦ coefficient (sn n) c fr k) (hcoeff c hc fr hfr k).1 j φ
      ((hcoeff c hc fr hfr k).2.2 j φ)

end
end HolomorphicAnosov
