import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.BumpFunction

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- A smooth function on an open subset has a smooth ambient extension with the same germ at a chosen point. -/
theorem exists_smooth_scalar_extension_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (U : Opens M) (p : U) (f : U → ℝ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    ∃ F : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ F ∧
      ∀ᶠ q in 𝓝 p, F q.1 = f q := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨p⟩
  have he (q : M) (hq : q ∈ e.target) :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm q := by
    have hid : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val ∘ e.symm) q :=
      contMDiffAt_id.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
        (e.open_target.mem_nhds hq) fun z hz ↦ e.right_inv hz)
    exact (ContMDiffAt.subtypeVal_comp_iff U e.symm q).mp hid
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
    (I := 𝓘(ℝ, E)) p.1).mem_iff.mp (e.open_target.mem_nhds (e.map_source (by simp [e])))
  refine ⟨fun q ↦ β q * f (e.symm q), ?_, ?_⟩
  · intro q
    by_cases hq : q ∈ e.target
    · have hs := (β.contMDiff q).smul ((hf (e.symm q)).comp q (he q hq))
      exact hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r ↦ by
        rfl)
    · have hqs : q ∉ tsupport β := fun h ↦ hq (hβ h)
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hqs] with r hr
      have hzero : β r = 0 := by
        by_contra h
        exact hr (subset_tsupport β h)
      simp [hzero]
  · have hb := (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) p).continuousAt
      |>.eventually β.eventuallyEq_one
    filter_upwards [hb] with q hq
    have heq : e.symm q.1 = q := e.left_inv (by simp [e])
    simp only [hq, Pi.one_apply, one_mul, heq]


end
end HolomorphicAnosov
