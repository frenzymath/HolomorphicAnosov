import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.SmoothOpenInclusionDifferentialInvertible
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- A smooth tangent field on an open subset has a smooth ambient extension with the same transported germ at a chosen point. -/
theorem exists_smooth_vectorField_extension_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (U : Opens M) (p : U)
    (X : LocalSmoothVectorField E M U) :
    ∃ Z : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : M → Type _),
      ∀ᶠ q in 𝓝 p, Z q.1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (X q) := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨p⟩
  have he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target := by
    intro q hq
    have hid : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val ∘ e.symm) q :=
      contMDiffAt_id.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
        (e.open_target.mem_nhds hq) fun z hz ↦ e.right_inv hz)
    exact ((ContMDiffAt.subtypeVal_comp_iff U e.symm q).mp hid).contMDiffWithinAt
  have hmd : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(show ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun q : U ↦ (q : M)) from
      contMDiff_subtype_val).contMDiffOn.mdifferentiableOn
      (by simp), he.mdifferentiableOn (by simp)⟩
  have hinv (q : M) (hq : q ∈ e.target) :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm q).IsInvertible :=
    ⟨hmd.symm.mfderiv hq, rfl⟩
  let W := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (fun q ↦ X q)
  have hW : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ (⟨q, W q⟩ : TangentBundle 𝓘(ℝ, E) M)) e.target := by
    intro q hq
    exact ((X.contMDiff (e.symm q)).mpullback_vectorField_preimage
      ((he q hq).contMDiffAt (e.open_target.mem_nhds hq)) (hinv q hq)
      (by simp)).contMDiffWithinAt
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
    (I := 𝓘(ℝ, E)) p.1).mem_iff.mp (e.open_target.mem_nhds (e.map_source (by simp [e])))
  refine ⟨⟨fun q ↦ β q • W q, β.contMDiff.contMDiffOn.smul_section_of_tsupport
    e.open_target hβ hW⟩, ?_⟩
  have hb := (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) p).continuousAt
    |>.eventually β.eventuallyEq_one
  filter_upwards [hb] with q hq
  change β q.1 • W q.1 = _
  simp only [hq, Pi.one_apply, one_smul]
  have htarget : q.1 ∈ e.target := by simp [e]
  have heq : e.symm q.1 = q := e.left_inv (by simp [e])
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm q.1).inverse (X (e.symm q.1)) = _
  apply (hmd.symm.mfderiv_injective htarget)
  rw [(hinv q.1 htarget).self_apply_inverse]
  have hd := congrArg (fun d ↦ d (X q)) (hmd.symm_comp_deriv
    (by simp [e] : q ∈ e.source))
  rw [heq]
  exact hd.symm


end
end HolomorphicAnosov
