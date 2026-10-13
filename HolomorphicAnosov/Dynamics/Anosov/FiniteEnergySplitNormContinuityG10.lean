import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergySplitNorm
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds

open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open TopologicalSpace Set

universe u
namespace HolomorphicAnosov.HPS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuity of the finite-energy maximum gauge on the original tangent bundle.
The summand energies are continuous by the finite-energy construction; continuity of
both oblique complementary projections is supplied by the native local-frame theorem.
This is the remaining GL1 continuity step needed before applying the HPS cutoff interface.
-/
theorem continuous_anosov_finite_energy_split_norm
    [FiniteDimensional ℝ E] (X : Type u) [EMetricSpace X] [CompactSpace X]
    [SecondCountableTopology X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
      (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsRiemannianManifold 𝓘(ℝ, E) X]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X X ∞)
    (S : InvariantRealTangentSplitting f) (h : BundleAnosovBounds f S) :
    ∃ (θ K : ℝ) (νs νu ν : ∀ x : X, TangentSpace 𝓘(ℝ, E) x → ℝ),
      0 < θ ∧ θ < 1 ∧ 0 ≤ K ∧
      Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ νs p.proj p.2) ∧
      Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ νu p.proj p.2) ∧
      (∀ x (v : S.stable.toDistribution x), νs x v ≤ K * ‖v.val‖) ∧
      (∀ x (v : S.unstable.toDistribution x), νu x v ≤ K * ‖v.val‖) ∧
      (∀ x v, ν x v =
        let w := (Submodule.prodEquivOfIsCompl (S.stable.toDistribution x)
          (S.unstable.toDistribution x) (S.isCompl x)).symm v
        max (νs x w.1) (νu x w.2)) ∧
      (∀ x, ν x 0 = 0) ∧
      (∀ x v w, ν x (v + w) ≤ ν x v + ν x w) ∧
      (∀ x (c : ℝ) v, ν x (c • v) = ‖c‖ * ν x v) ∧
      (∀ x v, ‖v‖ ≤ 2 * ν x v) ∧
      (∀ x (v : S.stable.toDistribution x),
        ν (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤ θ * ν x v) ∧
      (∀ x (v : S.unstable.toDistribution x),
        ν (f.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤ θ * ν x v) ∧
      Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ ν p.proj p.2) := by
  obtain ⟨θ, K, νs, νu, ν, hθ, hθ1, hK, hνs, hνu, hνsu, hνuu,
    hsplit, hzero, hadd, hsmul, hlower, hscontract, hucontract⟩ :=
    anosov_finite_energy_split_norm X f S h
  let ps : TangentBundle 𝓘(ℝ, E) X → TangentBundle 𝓘(ℝ, E) X :=
    fun z ↦ ⟨z.proj, (S.stable.toDistribution z.proj).projection
      (S.unstable.toDistribution z.proj) (S.isCompl z.proj) z.snd⟩
  let pu : TangentBundle 𝓘(ℝ, E) X → TangentBundle 𝓘(ℝ, E) X :=
    fun z ↦ ⟨z.proj, (S.unstable.toDistribution z.proj).projection
      (S.stable.toDistribution z.proj) (S.isCompl z.proj).symm z.snd⟩
  have hps : Continuous ps :=
    NativeSplittingPreparation.continuous_native_projection
      (I := 𝓘(ℝ, E)) S.stable S.unstable S.isCompl
  have hpu : Continuous pu :=
    NativeSplittingPreparation.continuous_native_projection
      (I := 𝓘(ℝ, E)) S.unstable S.stable (fun x ↦ (S.isCompl x).symm)
  have hνcont : Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ ν p.proj p.2) := by
    have hs : Continuous (fun z : TangentBundle 𝓘(ℝ, E) X ↦ νs (ps z).proj (ps z).snd) :=
      hνs.comp hps
    have hu : Continuous (fun z : TangentBundle 𝓘(ℝ, E) X ↦ νu (pu z).proj (pu z).snd) :=
      hνu.comp hpu
    have hm := hs.max hu
    apply hm.congr
    intro z
    rw [hsplit z.proj z.snd]
    simp [ps, pu, Submodule.prodEquivOfIsCompl_symm_apply]
  refine ⟨θ, K, νs, νu, ν, hθ, hθ1, hK, hνs, hνu, hνsu, hνuu,
    hsplit, hzero, hadd, hsmul, hlower, hscontract, hucontract, hνcont⟩

end HolomorphicAnosov.HPS
