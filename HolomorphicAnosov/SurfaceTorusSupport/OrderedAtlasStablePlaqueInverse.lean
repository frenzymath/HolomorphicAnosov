import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import HolomorphicAnosov.SurfaceTorusSupport.ProjectiveActionHolomorphic
import HolomorphicAnosov.SurfaceTorusSupport.LocalPlaqueInverseOfCoordinateFormula

noncomputable section
open Set Filter Topology _root_.Topology
open scoped ContDiff
universe u v
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- Each intrinsic affine stable-leaf chart gives a continuous plaque inverse on an open horizontal
slice of the ordered product atlas, fixing the marked point. (Ghys, §5, pp. 598–599) -/
theorem ordered_atlas_stable_plaque_inverse
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a) (x : S) (i : A.index) :
    letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
    let L := A.stableLeaf x
    letI := L.native.topology
    ∀ y : StableAsymptoticLeaf f.toHomeomorph x, y.val ∈ (A.chart i).source →
      ∃ (V : Set ComplexProjectiveLine)
        (s : ComplexProjectiveLine → StableAsymptoticLeaf f.toHomeomorph x),
        IsOpen V ∧ (A.chart i y.val).1 ∈ V ∧ ContinuousOn s V ∧
        s (A.chart i y.val).1 = y ∧
        ∀ p ∈ V, (p, (A.chart i y.val).2) ∈ (A.chart i).target ∧
          (s p).val = (A.chart i).symm (p, (A.chart i y.val).2) := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  let L := A.stableLeaf x
  let := L.native.topology
  dsimp only
  intro y hy
  obtain ⟨c, hc, hyc, g, hg⟩ := A.stable_affine x i y hy
  let scalar : ℂ ≃ₜ ComplexModel 1 :=
    { toEquiv :=
        { toFun := fun z _ ↦ z
          invFun := fun z ↦ z 0
          left_inv := fun _ ↦ rfl
          right_inv := fun z ↦ by
            funext k
            exact congrArg z (Subsingleton.elim (0 : Fin 1) k) }
      continuous_toFun := continuous_pi (fun _ ↦ continuous_id)
      continuous_invFun := continuous_apply 0 }
  let action : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine :=
    { toEquiv := MulAction.toPerm g
      continuous_toFun := (projective_special_linear_action_contMDiff g).continuous
      continuous_invFun := (projective_special_linear_action_contMDiff g⁻¹).continuous }
  let k := ((c.trans scalar.toOpenPartialHomeomorph).trans
    (complexProjectiveLineChart 1).symm).trans action.toOpenPartialHomeomorph
  have hksource : k.source = c.source := by
    simp [k, complexProjectiveLineChart]
  have hkval (z) : k z = g • complexProjectiveLineFinite (c z) := rfl
  have hlocal : ∀ᶠ z in 𝓝 y, z ∈ k.source ∧ z.val ∈ (A.chart i).source ∧
      A.chart i z.val = (k z, (A.chart i y.val).2) := by
    filter_upwards [hg] with z hz
    exact ⟨hksource ▸ hz.1, hz.2.1, Prod.ext (hz.2.2.1.trans (hkval z).symm) hz.2.2.2⟩
  obtain ⟨V, hV, hyV, hVk, hs, hslice⟩ :=
    local_plaque_inverse_of_coordinate_formula Subtype.val (A.chart i) k y
      (A.chart i y.val).2 hlocal
  have hyval : (A.chart i y.val).1 = k y :=
    congrArg Prod.fst (Filter.Eventually.self_of_nhds hlocal).2.2
  refine ⟨V, k.symm, hV, hyval.symm ▸ hyV, hs, ?_, hslice⟩
  rw [hyval]
  exact k.left_inv (hksource ▸ hyc)

end HolomorphicAnosov.Ghys
