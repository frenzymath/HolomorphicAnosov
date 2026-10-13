import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealMetric
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalIteratePairingJ
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingJ
import HolomorphicAnosov.Paper.Zhang.StableFoliationsStableInvariantOfEqualGrowth
import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeInverseForward

/-! The stable real tangent distribution is invariant under the complex structure. (Ghys, Lemma 2.1,
p.589; HPS, Lemma 2.7, p.9) -/

noncomputable section
open scoped ContDiff Manifold Topology _root_.Topology Bundle
universe u
namespace HolomorphicAnosov.StableFoliationsSupport
attribute [local instance] complex_isManifold_real

/-- Transported multiplication by `i` preserves the stable real tangent subspace under the Hermitian
Anosov estimates. (Ghys, Lemma 2.1, p.589; HPS, Lemma 2.7, p.9) -/
theorem original_stable_J_invariant
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M)
    (h : HermitianTangentMetricCore d M)
    (P : InvariantRealTangentSplitting f.toReal)
    (C rate : ℝ) (hC : 0 < C) (hrate : 0 < rate ∧ rate < 1)
    (hs : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.stable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v))
    (hu : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.unstable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f.symm : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v)) :
    ∀ x (v : TangentSpace (realModel d) x), v ∈ P.stable.toDistribution x →
      complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v) ∈
        P.stable.toDistribution x := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨originalRealMetric h⟩
  have hnorm (x : M) (v : TangentSpace (realModel d) x) :
      ‖v‖ = Real.sqrt (hermitianTangentRealPairing h x v v) := by
    rw [norm_eq_sqrt_real_inner]
    change Real.sqrt (originalRealBilinear h x v v) = _
    rw [originalRealBilinear_apply]
  intro x
  apply stable_invariant_of_equal_growth
    (F := fun n ↦ TangentSpace (realModel d) ((f : M → M)^[n] x))
    (P.stable.toDistribution x)
    (P.unstable.toDistribution x) (P.isCompl x)
    (fun n ↦ (mfderiv (realModel d) (realModel d)
      (realIterate (realModel d) f.toReal n) x).toLinearMap)
    C rate hC.le hrate.1.le hrate.2
  · intro n v hv
    simp only [hnorm]
    convert hs n x v hv using 1
  · intro n v hv
    let e := realIterate (realModel d) f.toReal n
    have hmem : mfderiv (realModel d) (realModel d) e x v ∈
        P.unstable.toDistribution (e x) := by
      change mfderiv (realModel d) (realModel d) ((f.toReal : M → M)^[n]) x v ∈
        P.unstable.toDistribution ((f.toReal : M → M)^[n] x)
      rw [← real_distribution_iterate_invariant f.toReal P.unstable.toDistribution
        P.unstable_map n x]
      exact ⟨v, hv, rfl⟩
    have hu' := hu n (e x) (mfderiv (realModel d) (realModel d) e x v) hmem
    have hinv := derivative_inverse_forward e x v
    have hpoint : (f.symm : M → M)^[n] (e x) = x := e.symm_apply_apply x
    change Real.sqrt (hermitianTangentRealPairing h ((f.symm : M → M)^[n] (e x))
      (mfderiv (realModel d) (realModel d) e.symm (e x)
        (mfderiv (realModel d) (realModel d) e x v))
      (mfderiv (realModel d) (realModel d) e.symm (e x)
        (mfderiv (realModel d) (realModel d) e x v))) ≤ _ at hu'
    rw [hinv, hpoint] at hu'
    simp only [hnorm]
    convert hu' using 1
    rfl
  · intro v
    simp only [hnorm, real_pairing_J]
  · intro n v
    simp only [hnorm]
    convert congrArg Real.sqrt (original_iterate_pairing_J f h n x v) using 1

end HolomorphicAnosov.StableFoliationsSupport
