import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- An injective moving exponential map that is a local diffeomorphism on an open set
is a diffeomorphism onto its open image. (Hirsch–Pugh–Shub, p. 62) -/
theorem glue_inverse_tube
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (O : Opens (TangentBundle 𝓘(ℝ, E) M))
    (hinj : InjOn (riemannianExponentialAddition g) O)
    (hloc : IsLocalDiffeomorphOn (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) ∞
      (riemannianExponentialAddition g) O) :
    ∃ (B : Opens (M × M))
      (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞),
      (B : Set (M × M)) = riemannianExponentialAddition g '' O ∧
      ∀ z : O, (Φ z : M × M) = riemannianExponentialAddition g z := by
  classical
  let F := riemannianExponentialAddition g
  have himage : IsOpen (F '' (O : Set _)) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨e, hze, he⟩ := hloc ⟨z, hz⟩
    have hC := e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (O.isOpen.inter e.open_source) inter_subset_right
    have hFC : e '' ((O : Set _) ∩ e.source) ⊆ F '' (O : Set _) := by
      rintro y ⟨z, hz, rfl⟩
      exact ⟨z, hz.1, he hz.2⟩
    exact Filter.mem_of_superset (hC.mem_nhds ⟨z, ⟨hz, hze⟩, (he hze).symm⟩) hFC
  let B : Opens (M × M) := ⟨F '' (O : Set _), himage⟩
  let φ : O → B := fun z ↦ ⟨F z, ⟨z, z.property, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro z z' h
      exact Subtype.ext (hinj z.property z'.property (congrArg Subtype.val h))
    · rintro ⟨y, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let equiv := Equiv.ofBijective φ hφ
  have hforward : ContMDiff (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) ∞ φ := by
    apply (ContMDiff.subtypeVal_comp_iff B φ).mp
    intro z
    change ContMDiffAt (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) ∞
      (fun z : O ↦ F z) z
    apply contMDiffAt_subtype_iff.mpr
    exact (hloc z).contMDiffAt
  have hinverse : ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞ equiv.symm := by
    apply (ContMDiff.subtypeVal_comp_iff O equiv.symm).mp
    intro y
    let z : O := equiv.symm y
    have hFz : F z = y := congrArg Subtype.val (equiv.apply_symm_apply y)
    obtain ⟨e, hze, he⟩ := hloc z
    have hy : (y : M × M) ∈ e.target := by
      rw [← hFz]
      change riemannianExponentialAddition g z ∈ e.target
      rw [he hze]
      exact e.toPartialEquiv.map_source hze
    have hC := e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (O.isOpen.inter e.open_source) inter_subset_right
    have hyC : (y : M × M) ∈ e '' ((O : Set _) ∩ e.source) :=
      ⟨z, ⟨z.property, hze⟩, (he hze).symm.trans hFz⟩
    have heq : (fun w : B ↦ (equiv.symm w : TangentBundle 𝓘(ℝ, E) M))
        =ᶠ[𝓝 y] (fun w : B ↦ e.symm w) := by
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (hC.mem_nhds hyC)]
        with w hw
      obtain ⟨v, hv, hev⟩ := hw
      have hFv : F v = w := (he hv.2).trans hev
      have hFw : F (equiv.symm w) = w :=
        congrArg Subtype.val (equiv.apply_symm_apply w)
      have hsame : (equiv.symm w : TangentBundle 𝓘(ℝ, E) M) = v :=
        hinj (equiv.symm w).property hv.1 (hFw.trans hFv.symm)
      rw [hsame, ← hev]
      exact (e.toPartialEquiv.left_inv hv.2).symm
    apply (contMDiffAt_subtype_iff.mpr
      (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hy))).congr_of_eventuallyEq heq
  exact ⟨B, ⟨equiv, hforward, hinverse⟩, rfl, fun z ↦ rfl⟩


end ExponentialLift
end HolomorphicAnosov
