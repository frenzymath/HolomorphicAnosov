import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveFrameCoverG7
import HolomorphicAnosov.SurfaceTorusSupport.ProjectiveActionHolomorphic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Evaluation of ordered projective frames on projective product coordinates and its compatibility
with local trivializations. -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v
attribute [local instance] complex_isManifold_real

/-- Evaluation of an ordered PSL×PSL frame is continuous and agrees with each local trivialization
on its chart source. -/
theorem ordered_projective_frame_evaluation
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    (Z : FiberBundleCore A.index S OrderedProjectiveFrameGroup)
    (hbase : Z.baseSet = fun i ↦ (A.chart i).source)
    (hindex : Z.indexAt = fun x ↦ Classical.choose (A.cover x))
    (hchange : Z.coordChange =
      fun i j x g ↦ g * (A.transition i j x)⁻¹) :
    let ev : Z.TotalSpace → ComplexProjectiveLine × ComplexProjectiveLine :=
      fun p ↦ ((p.2.1 • (A.chart (Z.indexAt p.1) p.1).1),
        (p.2.2 • (A.chart (Z.indexAt p.1) p.1).2))
    Continuous ev ∧
      ∀ (i : A.index) (p : Z.TotalSpace),
        p.1 ∈ (A.chart i).source →
        ev p = ((Z.localTriv i p).2.1 • (A.chart i p.1).1,
          (Z.localTriv i p).2.2 • (A.chart i p.1).2) := by
  let ev : Z.TotalSpace → ComplexProjectiveLine × ComplexProjectiveLine :=
    fun p ↦ ((p.2.1 • (A.chart (Z.indexAt p.1) p.1).1),
      (p.2.2 • (A.chart (Z.indexAt p.1) p.1).2))
  have hform : ∀ (i : A.index) (p : Z.TotalSpace),
      p.1 ∈ (A.chart i).source →
      ev p = ((Z.localTriv i p).2.1 • (A.chart i p.1).1,
        (Z.localTriv i p).2.2 • (A.chart i p.1).2) := by
    intro i p hp
    dsimp only [ev]
    rw [Z.localTriv_apply, hchange, hindex]
    have hpi : p.1 ∈ (A.chart (Z.indexAt p.1)).source := by
      have h := Z.mem_baseSet_at p.1
      rw [hbase] at h
      exact h
    rw [A.transition_agrees (Classical.choose (A.cover p.1)) i p.1
      ⟨by simpa [hindex] using hpi, hp⟩]
    apply Prod.ext
    · change p.2.1 • (A.chart (Classical.choose (A.cover p.1)) p.1).1 =
        (p.2.1 * (A.transition (Classical.choose (A.cover p.1)) i p.1).1⁻¹) •
          ((A.transition (Classical.choose (A.cover p.1)) i p.1).1 •
            (A.chart (Classical.choose (A.cover p.1)) p.1).1)
      simp [mul_smul]
    · change p.2.2 • (A.chart (Classical.choose (A.cover p.1)) p.1).2 =
        (p.2.2 * (A.transition (Classical.choose (A.cover p.1)) i p.1).2⁻¹) •
          ((A.transition (Classical.choose (A.cover p.1)) i p.1).2 •
            (A.chart (Classical.choose (A.cover p.1)) p.1).2)
      simp [mul_smul]
  refine ⟨continuous_iff_continuousAt.mpr ?_, hform⟩
  intro p
  let i := Z.indexAt p.1
  have hp : p.1 ∈ (A.chart i).source := by
    have h := Z.mem_baseSet_at p.1
    rw [hbase] at h
    exact h
  have hmem : p ∈ (Z.localTriv i).source := by
    rw [(Z.localTriv i).mem_source, ← Z.baseSet_at, hbase]
    exact hp
  have hlabel : ContinuousAt (fun w : Z.TotalSpace ↦ (Z.localTriv i w).2) p :=
    ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hmem).snd
  have hfixed : ∀ᶠ w in 𝓝 p, (Z.localTriv i w).2 = (Z.localTriv i p).2 := by
    exact hlabel.eventually ((isOpen_discrete {(Z.localTriv i p).2}).mem_nhds
      (mem_singleton _))
  have hsource : ∀ᶠ w : Z.TotalSpace in 𝓝 p,
      w.1 ∈ (A.chart i).source :=
    Z.continuous_proj.continuousAt ((A.chart i).open_source.mem_nhds hp)
  have hchart : ContinuousAt (fun w : Z.TotalSpace ↦ A.chart i w.1) p := by
    have hc : ContinuousAt (A.chart i) p.1 :=
      (A.holomorphic i).1.continuousOn.continuousAt
        ((A.chart i).open_source.mem_nhds hp)
    exact hc.comp Z.continuous_proj.continuousAt
  have hact : ∀ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
      Continuous (fun q : ComplexProjectiveLine ↦ g • q) := by
    intro g
    exact (projective_special_linear_action_contMDiff g).continuous
  have hleft : ContinuousAt
      (fun w : Z.TotalSpace ↦
        (Z.localTriv i p).2.1 • (A.chart i w.1).1) p := by
    exact (hact _).continuousAt.comp
      (continuousAt_fst.comp hchart)
  have hright : ContinuousAt
      (fun w : Z.TotalSpace ↦
        (Z.localTriv i p).2.2 • (A.chart i w.1).2) p := by
    exact (hact _).continuousAt.comp
      (continuousAt_snd.comp hchart)
  have hc : ContinuousAt
      (fun w : Z.TotalSpace ↦
        ((Z.localTriv i p).2.1 • (A.chart i w.1).1,
          (Z.localTriv i p).2.2 • (A.chart i w.1).2)) p :=
    hleft.prodMk hright
  apply hc.congr_of_eventuallyEq
  filter_upwards [hfixed, hsource] with w hw hs
  change ev w = _
  rw [hform i w hs, hw]

end HolomorphicAnosov.Ghys
