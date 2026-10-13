import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import HolomorphicAnosov.Geometry.ComplexToRealManifold




/-! This file relates injectivity of complex derivatives to compatible real coordinate atlases. (Demailly, I §3.C, p. 23).
-/
namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v
attribute [local instance] complex_isManifold_real

/-- Injectivity of a holomorphic derivative is preserved when computed in a compatible real atlas. (Demailly, I §3.C, p. 23). -/
theorem complexDerivative_injective_of_compatible_real_charts
    {r k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [ChartedSpace (ComplexModel k) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L] [IsManifold (complexModel k) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : L → M} {x : L}
    (hforward : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) (realModel k) (id : L → L) x)
    (hbackward : MDifferentiableAt (realModel k) 𝓘(ℝ, Fin r → ℝ) (id : L → L) x)
    (hf : MDifferentiableAt (complexModel k) (complexModel d) f x)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) f x)) :
    Function.Injective (mfderiv (complexModel k) (complexModel d) f x) := by
  let A := mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel k) (id : L → L) x
  let B := mfderiv (realModel k) 𝓘(ℝ, Fin r → ℝ) (id : L → L) x
  have hAB : A.comp B = ContinuousLinearMap.id ℝ (TangentSpace (realModel k) x) := by
    dsimp only [A, B]
    have h := mfderiv_comp (I := realModel k) (I' := 𝓘(ℝ, Fin r → ℝ))
      (I'' := realModel k) x hforward hbackward
    exact h.symm.trans (by simpa only [Function.id_comp] using
      (mfderiv_id (I := realModel k) (x := x)))
  have hB : Function.Injective B := by
    intro u v huv
    have h := congrArg A huv
    simpa only [← ContinuousLinearMap.comp_apply, hAB, ContinuousLinearMap.id_apply] using h
  have hreal : Function.Injective (mfderiv (realModel k) (realModel d) f x) := by
    have hchain := mfderiv_comp (I := realModel k) (I' := 𝓘(ℝ, Fin r → ℝ))
      (I'' := realModel d) x (mdifferentiableAt_of_mfderiv_injective hinj) hbackward
    simp only [Function.comp_id] at hchain
    rw [hchain]
    exact hinj.comp hB
  intro u v huv
  apply (complexTangentToReal k x).injective
  apply hreal
  rw [mfderiv_complex_to_real hf, mfderiv_complex_to_real hf, huv]

end HolomorphicAnosov

