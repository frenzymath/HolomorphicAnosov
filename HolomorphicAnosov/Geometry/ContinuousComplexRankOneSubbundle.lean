import HolomorphicAnosov.Geometry.ComplexSubbundleChart
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne

/-!
Continuous real tangent distributions satisfying `HasComplexRankOne` are realifications of
continuous complex line subbundles.
-/

noncomputable section
namespace HolomorphicAnosov

open scoped ContDiff Manifold
attribute [local instance] complex_isManifold_real

universe u

/-- A continuous real tangent distribution satisfying `HasComplexRankOne` is the realification of a
continuous complex line subbundle. -/
theorem exists_continuous_complex_rank_one_subbundle
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (P : ContinuousRealTangentSubbundle (realModel d) M)
    (h : HasComplexRankOne P.toDistribution) :
    ∃ (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
      (T : ContinuousComplexTangentSubbundle (complexModel d) M),
      T.toDistribution = S ∧
      (∀ x, Module.finrank ℂ (S x) = 1) ∧
      (∀ x, ((S x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.toDistribution x) := by
  let S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x) :=
    fun x ↦ (h x).choose
  have hS : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.toDistribution x := by
    intro x
    exact (h x).choose_spec.2
  obtain ⟨T, hT⟩ := complex_subbundle_of_realification P S hS
  refine ⟨S, T, hT, ?_, hS⟩
  intro x
  exact (h x).choose_spec.1


end HolomorphicAnosov
