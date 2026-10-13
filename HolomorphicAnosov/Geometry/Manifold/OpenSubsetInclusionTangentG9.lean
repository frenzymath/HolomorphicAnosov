import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
The differential of an open submanifold inclusion is a tangent-space isomorphism at every point.
(Michor, §1.1)
-/

noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov

/-- The inclusion of an open submanifold has a bijective differential at each point. (Michor, §1.1) -/
theorem openSubsetInclusion_mfderiv_bijective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (x : U) :
    Function.Bijective (mfderiv I I (Subtype.val : U → M) x) := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨x⟩
  have he : ContMDiff I I ∞ (e : U → M) := contMDiff_subtype_val
  have hei : ContMDiffOn I I ∞ (e.symm : M → U) e.target := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.subtypeVal_comp_iff U e.symm y).mp
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hd : e.MDifferentiable I I :=
    ⟨(he.mdifferentiable (by simp)).mdifferentiableOn,
      hei.mdifferentiableOn (by simp)⟩
  exact hd.mfderiv_bijective (by simp [e])

end HolomorphicAnosov
