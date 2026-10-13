import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Paper.Zhang.StableFoliationsComplexRankLocallyConstant
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Complementary realifications on a connected compact complex manifold give constant complex
subbundle ranks whose sum is the ambient dimension. (Ghys, Lemma 2.1, p.589) -/

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u
namespace HolomorphicAnosov

/-- On a connected compact complex manifold, complex subbundles whose realifications form a
complementary splitting have constant complex ranks summing to the ambient dimension. (Ghys,
Lemma 2.1, p.589) -/
theorem complex_rank_split_from_realification
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (Ps Pu : ∀ x : M, Submodule ℝ (TangentSpace (realModel d) x))
    (hCompl : ∀ x, IsCompl (Ps x) (Pu x))
    (S U : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, ((S.toDistribution x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap = Ps x)
    (hU : ∀ x, ((U.toDistribution x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap = Pu x) :
    ∃ s t : ℕ, s + t = d ∧
      (∀ x, Module.finrank ℂ (S.toDistribution x) = s ∧
        Module.finrank ℂ (U.toDistribution x) = t) := by
  have hComplexSplit (x : M) : IsCompl (S.toDistribution x) (U.toDistribution x) := by
    apply (Submodule.isCompl_restrictScalars_iff ℝ).mp
    apply (Submodule.orderIsoMapComap (complexTangentToReal d x).toLinearEquiv).isCompl_iff.mpr
    change IsCompl (((S.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap)
      (((U.toDistribution x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap)
    rw [hS x, hU x]
    exact hCompl x
  have hlocS := StableFoliationsSupport.complex_subbundle_finrank_isLocallyConstant
    (complexModel d) S
  have hlocU := StableFoliationsSupport.complex_subbundle_finrank_isLocallyConstant
    (complexModel d) U
  let x0 : M := Classical.choice (inferInstance : Nonempty M)
  let s := Module.finrank ℂ (S.toDistribution x0)
  let t := Module.finrank ℂ (U.toDistribution x0)
  have hsum := Submodule.finrank_add_eq_of_isCompl (hComplexSplit x0)
  have htangent : Module.finrank ℂ (TangentSpace (complexModel d) x0) = d := by
    change Module.finrank ℂ (ComplexModel d) = d
    simp [ComplexModel]
  refine ⟨s, t, hsum.trans htangent, ?_⟩
  intro x
  constructor
  · simpa [s] using (hlocS.apply_eq_of_preconnectedSpace x0 x).symm
  · simpa [t] using (hlocU.apply_eq_of_preconnectedSpace x0 x).symm

end HolomorphicAnosov
