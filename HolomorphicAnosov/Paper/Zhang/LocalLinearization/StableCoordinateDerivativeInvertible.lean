import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_stable_coordinate_derivative_invertible
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, ((S.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x)
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hU : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (t : M → ℂ) (x : M) (hrank : Module.finrank ℂ (S.toDistribution x) = 1)
    (hker : (transverseScalarDifferential t x).ker = U x) :
    (localStableCoordinateDerivative S.toDistribution t x).IsInvertible := by
  let B := localStableCoordinateDerivative S.toDistribution t x
  have hzero : ∀ v : S.toDistribution x, B v = 0 → v = 0 := by
    intro v hv
    have hvmem : v.val ∈ U x := by
      rw [← hker]
      exact hv
    have hsreal : complexTangentToReal d x v.val ∈ a.splitting.stable.toDistribution x := by
      rw [← hS x]
      exact Submodule.mem_map.mpr ⟨v.val, v.property, rfl⟩
    have hureal : complexTangentToReal d x v.val ∈ a.splitting.unstable.toDistribution x := by
      rw [← hU x]
      exact Submodule.mem_map.mpr ⟨v.val, hvmem, rfl⟩
    have hvreal := Submodule.disjoint_def.mp (a.splitting.isCompl x).disjoint
      (complexTangentToReal d x v.val) hsreal hureal
    apply Subtype.ext
    exact (complexTangentToReal d x).injective (by simpa using hvreal)
  have hinj : Function.Injective B := LinearMap.ker_eq_bot.mp
    (LinearMap.ker_eq_bot'.mpr hzero)
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hrank) (f := B.toLinearMap)).mp hinj
  let e : S.toDistribution x ≃L[ℂ] ℂ :=
    (LinearEquiv.ofBijective B.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨e, rfl⟩


end
end HolomorphicAnosov.Paper.Zhang
