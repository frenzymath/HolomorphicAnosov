import HolomorphicAnosov.Paper.Zhang.DifferenceEvalLeC0
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealContMDiffOnMap
import Mathlib.Topology.UniformSpace.UniformApproximation

open Set Filter TopologicalSpace Bundle
open scoped Manifold ContDiff Topology _root_.Topology Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- Global C⁰ convergence with bounded difference values preserves continuity of quotient-line
connections. (Zhang, Lemma 2.2, p.5) -/
theorem isContinuous_of_c0_limit
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (Ds : ι → Connection U) (D : Connection U)
    (hb : ∀ n, BddAbove (differenceValues g (Ds n) D))
    (hc : Tendsto (fun n ↦ c0Distance g (Ds n) D) l (𝓝 0))
    (hcontinuous : ∀ n, IsContinuous (Ds n)) : IsContinuous D := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  intro V e c hcat
  apply continuousOn_clm_apply.mpr
  intro v
  let w (z : ComplexModel d) : TangentSpace (realModel d) (c.symm z) :=
    mfderiv (realModel d) (realModel d) c.symm z v
  have hs : ContMDiffOn (realModel d) (realModel d) ∞ c.symm c.target :=
    OneFormBundle.real_contMDiffOn_map (contMDiffOn_symm_of_mem_maximalAtlas hcat)
  have htm := hs.continuousOn_tangentMapWithin (by simp)
    c.open_target.uniqueMDiffOn
  have hinput : Continuous (fun z : c.target ↦
      (tangentBundleModelSpaceHomeomorph (realModel d)).symm (z.val, v)) :=
    (tangentBundleModelSpaceHomeomorph (realModel d)).symm.continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hv : Continuous (fun z : c.target ↦
      (⟨c.symm z.val, w z.val⟩ : TangentBundle (realModel d) X)) := by
    apply (htm.comp_continuous hinput (fun z ↦ z.property)).congr
    intro z
    change (⟨c.symm z.val,
      mfderivWithin (realModel d) (realModel d) c.symm c.target z.val v⟩ :
        TangentBundle (realModel d) X) = _
    rw [mfderivWithin_eq_mfderiv
      (c.open_target.uniqueMDiffOn _ z.property)
      (((hs _ z.property).contMDiffAt (c.open_target.mem_nhds z.property)).mdifferentiableAt
        (by simp))]
  have hnorm : ContinuousOn (fun z ↦ ‖w z‖) c.target :=
    continuousOn_iff_continuous_domRestrict.mpr
      (FixedBlockEstimates.Native.continuous_original_norm g _ _ hv)
  have hlu : TendstoLocallyUniformlyOn
      (fun n z ↦ coordinateForm (Ds n) e c z v)
      (fun z ↦ coordinateForm D e c z v) l
      (c.target ∩ c.symm ⁻¹' (V : Set X)) := by
    apply tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
    intro z hz
    apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
    have hupper : Tendsto
        (fun p : ι × ComplexModel d ↦ c0Distance g (Ds p.1) D * ‖w p.2‖)
        (l ×ˢ 𝓝[c.target ∩ c.symm ⁻¹' (V : Set X)] z) (𝓝 (0 * ‖w z‖)) :=
      Filter.Tendsto.mul (f := fun p : ι × ComplexModel d ↦ c0Distance g (Ds p.1) D)
        (g := fun p : ι × ComplexModel d ↦ ‖w p.2‖)
        (hc.comp tendsto_fst)
        (Filter.Tendsto.comp (f := Prod.snd) (g := fun z ↦ ‖w z‖)
          ((hnorm z hz.1).mono inter_subset_left) tendsto_snd)
    simp only [zero_mul] at hupper
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ hupper
    filter_upwards [tendsto_snd.eventually self_mem_nhdsWithin] with p hp
    rw [dist_comm, dist_eq_norm]
    exact difference_eval_le_c0 g (Ds p.1) D (hb p.1) V e (c.symm p.2) hp.2 (w p.2)
  exact hlu.continuousOn (Eventually.of_forall (fun n ↦
    (hcontinuous n V e c hcat).clm_apply continuousOn_const)).frequently

end HolomorphicAnosov
