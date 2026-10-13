import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import HolomorphicAnosov.Geometry.ComplexToRealManifold

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v
attribute [local instance] complex_isManifold_real

/-- The image of a complex derivative, viewed as a real tangent subspace, agrees with the image computed in any compatible real atlas. (Demailly, I §3.C, p. 23). -/
theorem complexDerivative_range_of_compatible_real_charts
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
    (hreal : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) (realModel d) f x) :
    ((mfderiv (complexModel k) (complexModel d) f x).range.restrictScalars ℝ).map
      (complexTangentToReal d (f x)).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) f x).range := by
  let A := mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel k) (id : L → L) x
  let B := mfderiv (realModel k) 𝓘(ℝ, Fin r → ℝ) (id : L → L) x
  have hBA : B.comp A = ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Fin r → ℝ) x) := by
    dsimp only [A, B]
    have h := mfderiv_comp (I := 𝓘(ℝ, Fin r → ℝ)) (I' := realModel k)
      (I'' := 𝓘(ℝ, Fin r → ℝ)) x hbackward hforward
    exact h.symm.trans (by simpa only [Function.id_comp] using
      (mfderiv_id (I := 𝓘(ℝ, Fin r → ℝ)) (x := x)))
  have hB : Function.Surjective B := by
    intro v
    exact ⟨A v, congrArg (fun D ↦ D v) hBA⟩
  have hchain := mfderiv_comp (I := realModel k) (I' := 𝓘(ℝ, Fin r → ℝ))
    (I'' := realModel d) x hreal hbackward
  simp only [Function.comp_id] at hchain
  change mfderiv (realModel k) (realModel d) f x =
    (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) f x).comp B at hchain
  ext w
  simp only [Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.mem_range]
  constructor
  · rintro ⟨v, ⟨z, rfl⟩, rfl⟩
    refine ⟨B (complexTangentToReal k x z), ?_⟩
    change ((mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) f x).comp B)
      (complexTangentToReal k x z) = _
    rw [← hchain]
    exact mfderiv_complex_to_real hf z
  · rintro ⟨v, rfl⟩
    obtain ⟨z, hz⟩ := hB v
    let q := (complexTangentToReal k x).symm z
    refine ⟨mfderiv (complexModel k) (complexModel d) f x q, ⟨q, rfl⟩, ?_⟩
    change complexTangentToReal d (f x) _ = _
    rw [← mfderiv_complex_to_real hf, ContinuousLinearEquiv.apply_symm_apply,
      hchain, ContinuousLinearMap.comp_apply]
    change (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) f x) (B z) =
      (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) f x) v
    rw [hz]

end HolomorphicAnosov
