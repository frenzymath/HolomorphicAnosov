import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.EuclideanInverse
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
Reusable ManifoldInverse declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07ManifoldInverseFunction

noncomputable section

/-- On boundaryless finite-dimensional real manifolds, a smooth map whose actual differential is invertible has a smooth partial inverse through the given point. Its source lies in the prescribed original open smoothness domain and its forward map agrees with the original map. Source: Mathlib's inverse-function theorem, applied in the original extended charts. -/
theorem exists_partialDiffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {K : Type*} [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
    [I.Boundaryless] [J.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    {f : M → N} {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hf : ContMDiffOn I J ∞ f U)
    (a : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (ha : mfderiv I J f x = a.toContinuousLinearMap) :
    ∃ p : PartialDiffeomorph I J M N ∞,
      x ∈ p.source ∧ p.source ⊆ U ∧ EqOn f p p.source := by
  let A : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := extChartAt I x
      open_source := isOpen_extChartAt_source x
      open_target := isOpen_extChartAt_target x
      contMDiffOn_toFun := by simpa only [extChartAt_source] using
        (contMDiffOn_extChartAt (I := I) (x := x) (n := ∞))
      contMDiffOn_invFun := contMDiffOn_extChartAt_symm x }
  let B : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞ :=
    { toPartialEquiv := extChartAt J (f x)
      open_source := isOpen_extChartAt_source (f x)
      open_target := isOpen_extChartAt_target (f x)
      contMDiffOn_toFun := by simpa only [extChartAt_source] using
        (contMDiffOn_extChartAt (I := J) (x := f x) (n := ∞))
      contMDiffOn_invFun := contMDiffOn_extChartAt_symm (f x) }
  let W := U ∩ f ⁻¹' B.source
  have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage hU B.open_source
  have hxW : x ∈ W := ⟨hx, mem_extChartAt_source (f x)⟩
  let S := A.target ∩ A.symm ⁻¹' W
  have hS : IsOpen S := A.toOpenPartialHomeomorph.symm.isOpen_inter_preimage hW
  have hc : A x ∈ S := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change (extChartAt I x).symm ((extChartAt I x) x) ∈ W
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact hxW
  let g : E → F := B ∘ f ∘ A.symm
  have hAS : MapsTo A.symm S U := fun _ hz ↦ hz.2.1
  have hBf : MapsTo (f ∘ A.symm) S B.source := fun _ hz ↦ hz.2.2
  have hg : ContDiffOn ℝ ∞ g S := by
    apply ContMDiffOn.contDiffOn
    exact B.contMDiffOn_toFun.comp
      (hf.comp (A.contMDiffOn_invFun.mono inter_subset_left) hAS) hBf
  have hfx := hf.contMDiffAt (hU.mem_nhds hx)
  let c := (tangentSpaceCastModel I x).symm.trans (a.trans (tangentSpaceCastModel J (f x)))
  have hcder : HasFDerivAt g c.toContinuousLinearMap (A x) := by
    have hder := (hfx.mdifferentiableAt (by simp)).hasMFDerivAt
    rw [ha] at hder
    have hh := hder.2
    rw [I.range_eq_univ] at hh
    exact hh.hasFDerivAt (by simp)
  obtain ⟨P, hxP, hPS, hPg⟩ := euclidean_inverse hS hc hg c hcder
  let Q := (A.trans P).trans B.symm
  refine ⟨Q, ?_, ?_, ?_⟩
  · change (x ∈ A.source ∧ A x ∈ P.source) ∧ P (A x) ∈ B.target
    refine ⟨⟨mem_extChartAt_source x, hxP⟩, ?_⟩
    rw [hPg]
    change (extChartAt J (f x)) (f ((extChartAt I x).symm ((extChartAt I x) x))) ∈
      (extChartAt J (f x)).target
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_target (f x)
  · intro z hz
    change (z ∈ A.source ∧ A z ∈ P.source) ∧ P (A z) ∈ B.target at hz
    have h := (hPS hz.1.2).2.1
    change (extChartAt I x).symm ((extChartAt I x) z) ∈ U at h
    rwa [(extChartAt I x).left_inv hz.1.1] at h
  · intro z hz
    change (z ∈ A.source ∧ A z ∈ P.source) ∧ P (A z) ∈ B.target at hz
    change f z = B.symm (P (A z))
    rw [hPg]
    change f z = (extChartAt J (f x)).symm
      ((extChartAt J (f x)) (f ((extChartAt I x).symm ((extChartAt I x) z))))
    rw [(extChartAt I x).left_inv hz.1.1]
    have h := (hPS hz.1.2).2.2
    change f ((extChartAt I x).symm ((extChartAt I x) z)) ∈ B.source at h
    rw [(extChartAt I x).left_inv hz.1.1] at h
    exact ((extChartAt J (f x)).left_inv h).symm

end
end HolomorphicAnosov.W07ManifoldInverseFunction
