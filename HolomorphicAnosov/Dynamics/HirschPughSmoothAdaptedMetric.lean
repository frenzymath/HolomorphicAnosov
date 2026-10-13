import HolomorphicAnosov.Dynamics.HirschPughFactOneData
import HolomorphicAnosov.Dynamics.HirschPughContractionParameters
import HolomorphicAnosov.Dynamics.HirschPughSplitEnergyTensor
import HolomorphicAnosov.Geometry.SmoothMetricQuadraticApproximation
import HolomorphicAnosov.Analysis.QuadraticContractionPerturbation

/-!
# Smooth adapted metric for the original hyperbolic datum

Sources: Hirsch–Pugh (1969), Theorem 3.1 p.148; Wockel (2009), Theorem 11
pp.99–102. The finite energy and smooth quadratic comparison helpers provide
the complete construction on the original manifold and invariant set.
-/

namespace HolomorphicAnosov

open Set
open scoped ContDiff Manifold Topology

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Smooth adapted metric estimates on the original compact hyperbolic datum.

Choose q>0 with C rate^q<1. The forward and backward finite squared-energy sums
contract on their respective invariant subspaces by
c=1-(1-(C rate^q)^2)/(q C^2), where 0<c<1. The split energy tensor makes these
subspaces orthogonal by composing each sum with its complementary projection.
Its continuity follows from continuity of those projections and the derivative
maps; positivity follows from the zero iterate and complementarity.

Choose sqrt(c)<a<1 and δ>0 small enough that
(1+δ)c ≤ a²(1-δ). Apply smooth quadratic approximation on the closed compact
set Λ to obtain a smooth positive metric h satisfying
(1-δ)Q(v,v) ≤ h(v,v) ≤ (1+δ)Q(v,v). The same comparison at a source and its
image yields h(Dv,Dv) ≤ a² h(v,v), hence the required norm inequality.
Forward stable invariance is given; backward unstable invariance follows from
forward invariance and the chain-rule identity D(f⁻¹)Df=id. The construction
also covers zero fibres and the zero tangent space. -/
theorem smooth_adapted_metric_of_hyperbolic_datum
    [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ) :
    ∃ (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
        (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
      (a : ℝ),
      a < 1 ∧
      (∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)), v ∈ H.stable.fibre x →
        hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤
          a * hyperbolicRiemannianNorm h v) ∧
      (∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)), v ∈ H.unstable.fibre x →
        hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤
          a * hyperbolicRiemannianNorm h v) := by
  obtain ⟨q, hqpos, hsmall, hc0, hc1⟩ :=
    hirsch_pugh_contraction_parameters H.one_le_C H.rate_pos H.rate_lt_one
  let c := 1 - (1 - (H.C * H.rate ^ q) ^ 2) / ((q : ℝ) * H.C ^ 2)
  have hθ : Real.sqrt c < 1 := by
    have hs := Real.sq_sqrt hc0.le
    have hn := Real.sqrt_nonneg c
    nlinarith
  obtain ⟨a, δ, hθa, ha1, hδ, hδ1, hpert⟩ :=
    FactOneFiniteEnergy.quadratic_contraction_perturbation (Real.sqrt c)
      (Real.sqrt_nonneg c) hθ
  let Q := hyperbolicSplitEnergyTensor H q
  obtain ⟨h, hh⟩ := exists_smooth_metric_quadratic_comparison Λ H.compact.isClosed Q
    (hyperbolicSplitEnergyTensor_continuous H q) (hyperbolicSplitEnergyTensor_pos H hqpos)
    H.originalMetric δ hδ
  have hQnonneg (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)) : 0 ≤ Q x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hyperbolicSplitEnergyTensor_pos H hqpos x v hv).le
  have hstable (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M))
      (hv : v ∈ H.stable.fibre x) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v ∈
        H.stable.fibre ⟨f x, H.forward_mem x.property⟩ := by
    rw [← H.stable_invariant x]
    exact ⟨v, hv, rfl⟩
  have hunstable (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M))
      (hv : v ∈ H.unstable.fibre x) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v ∈
        H.unstable.fibre ⟨f.symm x, H.backward_mem x.property⟩ := by
    obtain ⟨z, hz⟩ := f.surjective (x : M)
    change f z = (x : M) at hz
    have hzΛ : z ∈ Λ := by
      have hh := H.backward_mem x.property
      rw [← hz, f.symm_apply_apply] at hh
      exact hh
    have hxsub : (⟨f z, H.forward_mem hzΛ⟩ : Λ) = x := Subtype.ext hz
    revert v
    rw [← hxsub]
    intro v hv
    have hbacksub : (⟨f.symm (f z), H.backward_mem (H.forward_mem hzΛ)⟩ : Λ) =
        ⟨z, hzΛ⟩ := Subtype.ext (f.symm_apply_apply z)
    let T : TangentSpace 𝓘(ℝ, E) (f z) →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) z :=
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f z)).toLinearMap
    rw [hbacksub]
    change T v ∈ H.unstable.fibre ⟨z, hzΛ⟩
    have hpre : v ∈ (H.unstable.fibre ⟨z, hzΛ⟩).map
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f z).toLinearMap := by
      rw [H.unstable_invariant ⟨z, hzΛ⟩]
      exact hv
    obtain ⟨w, hw, hwv⟩ := hpre
    have hchain := mfderiv_comp z
      (f.symm.contMDiff.mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiableAt (by simp))
    have hid : (f.symm : M → M) ∘ f = id := by
      funext y
      exact f.symm_apply_apply y
    rw [hid, mfderiv_id] at hchain
    have he : T ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f z) w) = w :=
      (congrArg (fun L ↦ L w) hchain).symm
    rw [← hwv]
    change T ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f z) w) ∈ H.unstable.fibre ⟨z, hzΛ⟩
    rw [he]
    exact hw
  refine ⟨h, a, ha1, ?_, ?_⟩
  · intro x v hv
    let y : Λ := ⟨f x, H.forward_mem x.property⟩
    let w := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v
    have hw := hstable x v hv
    have hcontract : Q y w w ≤ (Real.sqrt c) ^ 2 * Q x v v := by
      rw [Real.sq_sqrt hc0.le]
      change hyperbolicSplitEnergyTensor H q y w w ≤ c * hyperbolicSplitEnergyTensor H q x v v
      rw [hyperbolicSplitEnergyTensor_stable H q y w hw,
        hyperbolicSplitEnergyTensor_stable H q x v hv]
      exact hyperbolicFiniteEnergy_contract H hqpos hsmall f x v
        (fun n ↦ H.stable_estimate n x v hv)
    exact hpert (Q x v v) (Q y w w) (h.inner x v v) (h.inner y w w)
      (hQnonneg x v) hcontract (hh x v).1 (hh y w).2
  · intro x v hv
    let y : Λ := ⟨f.symm x, H.backward_mem x.property⟩
    let w := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v
    have hw := hunstable x v hv
    have hcontract : Q y w w ≤ (Real.sqrt c) ^ 2 * Q x v v := by
      rw [Real.sq_sqrt hc0.le]
      change hyperbolicSplitEnergyTensor H q y w w ≤ c * hyperbolicSplitEnergyTensor H q x v v
      rw [hyperbolicSplitEnergyTensor_unstable H q y w hw,
        hyperbolicSplitEnergyTensor_unstable H q x v hv]
      exact hyperbolicFiniteEnergy_contract H hqpos hsmall f.symm x v
        (fun n ↦ H.unstable_estimate n x v hv)
    exact hpert (Q x v v) (Q y w w) (h.inner x v v) (h.inner y w w)
      (hQnonneg x v) hcontract (hh x v).1 (hh y w).2

end

end HolomorphicAnosov

