import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.SupportedChartSmulSmooth

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [IsManifold (complexModel d) ∞ X] [T2Space X] [SecondCountableTopology X]
  [CompactSpace X] in
/-- The partition-of-unity sum of locally smooth connection forms is smooth in inverse-chart tangent
coordinates. (Zhang, after (4)) -/
theorem finite_local_forms_coordinate_smooth
    {ι : Type*} [Fintype ι] (O : ι → Opens X) (V : Opens X)
    (ρ : ι → X → ℂ) (hρsupport : ∀ i, tsupport (ρ i) ⊆ O i)
    (B : ι → (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hρ : ∀ i, ContDiffOn ℝ ∞ (fun z ↦ ρ i (c.symm z)) c.target)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun z ↦ (B i (c.symm z)).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap))
      (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ (O i : Set X)))) :
    ContDiffOn ℝ ∞ (fun z ↦ (∑ i, ρ i (c.symm z) • B i (c.symm z)).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap))
      (c.target ∩ c.symm ⁻¹' (V : Set X)) := by
  have hs := ContDiffOn.sum (s := (Finset.univ : Finset ι))
    (fun i _ ↦ supported_chart_smul_smooth (O i) V (ρ i) (hρsupport i) c
      (fun z ↦ (B i (c.symm z)).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)) (hρ i) (hB i))
  apply hs.congr
  intro z hz
  ext v
  simp only [ContinuousLinearMap.comp_apply, sum_apply, smul_apply]



end ConnectionCalculus
end HolomorphicAnosov
