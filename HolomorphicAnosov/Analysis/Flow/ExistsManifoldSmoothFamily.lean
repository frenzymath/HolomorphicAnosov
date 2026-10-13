import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import HolomorphicAnosov.Analysis.Flow.ExistsRealSmoothFlow
import HolomorphicAnosov.Analysis.Flow.CoordinateFieldSmooth

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.W07ManifoldFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

omit [T2Space N] in
set_option backward.isDefEq.respectTransparency false in
/-- Joint smoothness and the actual manifold differential equation, before adding uniqueness,
group law and local inverses. Source: Andrews6.1.1–2, coordinate transport of the proved
fixed-domain real smooth flow. -/
theorem exists_manifold_smooth_family
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N))) (z : N) :
    ∃ (U : Set N) (δ : ℝ) (Ψ : N × ℝ → N), IsOpen U ∧ z ∈ U ∧ 0 < δ ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Ψ (U ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ U, Ψ (y, 0) = y) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (I := I) (fun t ↦ Ψ (y, t)) V (Ioo (-δ) δ)) := by
  let e := extChartAt I z
  let Ω := interior e.target
  let F : E → E := fun q ↦ tangentCoordChange I (e.symm q) z (e.symm q) (V (e.symm q))
  have hF : ContDiffOn ℝ ∞ F Ω := coordinate_field_smooth hV z
  have hc : e z ∈ Ω := I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint
  obtain ⟨A, δ, Φ, hA, hcA, hδ, hΦ, hΦzero, hΦcurve, hΦΩ⟩ :=
    W07FiniteFlowBootstrap.exists_real_smooth_flow F Ω isOpen_interior hF (e z) hc
  let U := e.source ∩ e ⁻¹' A
  have hU : IsOpen U := (continuousOn_extChartAt z).isOpen_inter_preimage
    (isOpen_extChartAt_source z) hA
  have hzU : z ∈ U := ⟨mem_extChartAt_source z, hcA⟩
  let Ψ : N × ℝ → N := fun p ↦ e.symm (Φ (e p.1, p.2))
  have hφ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞
      (fun p : N × ℝ ↦ (e p.1, p.2)) (U ×ˢ Ioo (-δ) δ) := by
    have he : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : N × ℝ ↦ e p.1) (U ×ˢ Ioo (-δ) δ) :=
      (contMDiffOn_extChartAt (I := I) (x := z)).comp contMDiffOn_fst
        (fun p hp ↦ by
          have hh := hp.1.1
          change p.1 ∈ (extChartAt I z).source at hh
          rwa [extChartAt_source] at hh)
    convert he.prodMk (contMDiffOn_snd (I := I) (J := 𝓘(ℝ, ℝ)) (n := ∞)
      (s := U ×ˢ Ioo (-δ) δ)) using 1
    all_goals first | rfl | exact modelWithCornersSelf_prod | exact chartedSpaceSelf_prod.symm
  have hΨ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Ψ (U ×ˢ Ioo (-δ) δ) :=
    (contMDiffOn_extChartAt_symm (I := I) z).comp
      (hΦ.contMDiffOn.comp hφ (fun p hp ↦ ⟨hp.1.2, hp.2⟩))
      (fun p hp ↦ show Φ (e p.1, p.2) ∈ e.target from
        interior_subset (hΦΩ (e p.1) hp.1.2 p.2 hp.2))
  refine ⟨U, δ, Ψ, hU, hzU, hδ, hΨ, ?_, ?_⟩
  · intro y hy
    change e.symm (Φ (e y, 0)) = y
    rw [hΦzero (e y) hy.2]
    exact e.left_inv hy.1
  · intro y hy t ht
    have h := hΦcurve (e y) hy.2 t ht
    have hft : Φ (e y, t) ∈ Ω := hΦΩ (e y) hy.2 t ht
    let q := e.symm (Φ (e y, t))
    have hqsrc : q ∈ e.source := e.map_target (interior_subset hft)
    have hqown : q ∈ (extChartAt I q).source := mem_extChartAt_source q
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨?_, HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    · change ContinuousAt (e.symm ∘ fun r ↦ Φ (e y, r)) t
      have hh : ContinuousAt e.symm (Φ (e y, t)) :=
        continuousAt_extChartAt_symm'' (interior_subset hft)
      exact ContinuousAt.comp (f := fun r ↦ Φ (e y, r)) hh h.continuousAt
    simp only [chartAt_self_eq, mfld_simps]
    rw [hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I q ∘ e.symm) ∘ fun r ↦ Φ (e y, r)) (V q) t
    have h0 : Φ (e y, t) = e q := (e.right_inv (interior_subset hft)).symm
    rw [← tangentCoordChange_self (I := I) (x := q) (z := q) (v := V q) hqown,
      ← tangentCoordChange_comp (x := z) ⟨⟨hqown, hqsrc⟩, hqown⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
      (mem_nhds_iff.mpr ⟨Ω, interior_subset.trans (extChartAt_target_subset_range z),
        isOpen_interior, hft⟩)
    rw [h0]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hqsrc, hqown⟩

end HolomorphicAnosov.W07ManifoldFlow
