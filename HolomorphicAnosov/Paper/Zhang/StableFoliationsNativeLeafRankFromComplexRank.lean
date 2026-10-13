import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! A native immersed leaf tangent to the realification of a complex rank-`s` subbundle has real
dimension `2 * s`. (Ghys, Lemma 2.1, pp.588–589) -/

noncomputable section
open scoped ContDiff Manifold Topology _root_.Topology
open Set
universe u
namespace HolomorphicAnosov

/-- A native leaf tangent to the realification of a complex rank-`s` subbundle has real dimension `2
* s`. -/
theorem native_leaf_rank_eq_of_realification
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (P : ∀ x : M, Submodule ℝ (TangentSpace (realModel d) x))
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, ((S.toDistribution x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap = P x)
    (s : ℕ) (hrank : ∀ x, Module.finrank ℂ (S.toDistribution x) = s)
    (F : HPS.LeafPartition P ι L r) :
    ∀ i, r i = 2 * s := by
  have hP : ∀ x, Module.finrank ℝ (P x) = 2 * s := by
    intro x
    rw [← hS x]
    rw [LinearEquiv.finrank_map_eq (complexTangentToReal d x).toLinearEquiv]
    change Module.finrank ℝ (S.toDistribution x) = 2 * s
    rw [finrank_real_of_complex, hrank x]
  intro i
  have hi := F.leaf i
  let := hi.connected
  let z : L i := Classical.choice (inferInstance : Nonempty (L i))
  have hinj : Function.Injective
      ((mfderiv 𝓘(ℝ, Fin (r i) → ℝ) (realModel d) hi.inclusion z).toLinearMap) :=
    (hi.immersion.isImmersionAt z).mfderiv_injective (by simp)
  have hleaf : Module.finrank ℝ (P (hi.inclusion z)) = r i := by
    rw [← hi.tangent z]
    rw [LinearMap.finrank_range_of_inj hinj]
    change Module.finrank ℝ (Fin (r i) → ℝ) = r i
    exact Module.finrank_fin_fun ℝ
  exact hleaf.symm.trans (hP (hi.inclusion z))

end HolomorphicAnosov
