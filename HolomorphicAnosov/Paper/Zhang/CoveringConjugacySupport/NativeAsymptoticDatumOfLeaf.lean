import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeCarrierHomeomorph
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.CarrierTangentImage
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.ImmersionPrecomposeDiffeomorph
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.CarrierSmoothTransport

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- Reindex an actual source-selected HPS leaf on the literal asymptotic carrier. -/
theorem native_asymptotic_datum_of_leaf_g15 {r : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {L : Type u} [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (P : RealTangentDistribution 𝓘(ℝ, E) M) (ℓ : HPS.NativeLeaf (r := r) P L)
    (f : M ≃ₜ M) (x : M)
    (hrange : Set.range ℓ.inclusion = {y | ForwardAsymptotic f x y}) :
    ∃ N : NativeAsymptoticLeafDatum 𝓘(ℝ, E) f P x, N.rank = r ∧
      (letI := N.topology; letI := N.charts
       ∃ e : Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin N.rank → ℝ)
          L (StableAsymptoticLeaf f x) ∞, ∀ z : L, (e z).val = ℓ.inclusion z) := by
  let S : Set M := {y | ForwardAsymptotic f x y}
  obtain ⟨t, h, hh⟩ := native_carrier_homeomorph_g15 ℓ.inclusion ℓ.injective S hrange
  let := t
  let := ℓ.hausdorff
  let := ℓ.countable
  let := ℓ.connected
  obtain ⟨c, hm, e, he⟩ := carrier_smooth_transport_g15 (r := r) h.symm
  let := c
  let := hm
  have hval : (Subtype.val : S → M) = ℓ.inclusion ∘ e := by
    funext z
    rw [Function.comp_apply, he]
    simpa using (hh (h.symm z))
  have he' : ∀ z : L, (e.symm z).val = ℓ.inclusion z := by
    intro z
    have hz := congrFun hval (e.symm z)
    simpa using hz
  have hincl := carrier_tangent_image_g15 𝓘(ℝ, E) ℓ.inclusion ℓ.immersion.contMDiff S
    e.symm he' P ℓ.tangent
  have himm : ∀ z : S,
      Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) ∞ (Subtype.val : S → M) z := by
    intro z
    rw [hval]
    exact immersion_precompose_diffeomorph_g15 𝓘(ℝ, E) ℓ.inclusion e z
      (ℓ.immersion.isImmersionAt (e z))
  have hSC : @SecondCountableTopology S t := h.symm.secondCountableTopology
  let N : NativeAsymptoticLeafDatum 𝓘(ℝ, E) f P x :=
    { rank := r
      topology := t
      charts := c
      hausdorff := h.t2Space
      secondCountable := hSC
      connected := h.connectedSpace_iff.mp ℓ.connected
      smoothAtlas := hm
      inclusion_smooth := hincl.1
      inclusion_immersion := himm
      tangent_image := hincl.2 }
  exact ⟨N, rfl, e.symm, he'⟩


end HolomorphicAnosov
