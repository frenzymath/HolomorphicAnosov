import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import Mathlib.Topology.Covering.Basic

/-! Construction of the discrete frame covering associated with a locally constant ordered PSL×PSL
transition cocycle. -/

noncomputable section
open Set
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v
attribute [local instance] complex_isManifold_real

/-- The ordered projective frame labels, equipped with the discrete topology. -/
abbrev OrderedProjectiveFrameGroup :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ×
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ

instance orderedProjectiveFrameGroupTopologicalSpace :
    TopologicalSpace OrderedProjectiveFrameGroup := ⊥

instance orderedProjectiveFrameGroupDiscreteTopology :
    DiscreteTopology OrderedProjectiveFrameGroup := ⟨rfl⟩

/-- The locally constant ordered PSL×PSL transition cocycle defines a covering frame bundle with
coordinate changes given by right multiplication by inverse transitions. -/
theorem ordered_projective_frame_cover
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a) :
    ∃ Z : FiberBundleCore A.index S OrderedProjectiveFrameGroup,
      Z.baseSet = (fun i ↦ (A.chart i).source) ∧
      Z.indexAt = (fun x ↦ Classical.choose (A.cover x)) ∧
      Z.coordChange = (fun i j x g ↦ g * (A.transition i j x)⁻¹) ∧
      IsCoveringMap Z.proj := by
  let Z : FiberBundleCore A.index S OrderedProjectiveFrameGroup := {
    baseSet := fun i ↦ (A.chart i).source
    isOpen_baseSet := fun i ↦ (A.chart i).open_source
    indexAt := fun x ↦ Classical.choose (A.cover x)
    mem_baseSet_at := fun x ↦ Classical.choose_spec (A.cover x)
    coordChange := fun i j x g ↦ g * (A.transition i j x)⁻¹
    coordChange_self := by
      intro i x hx g
      rw [A.transition_self i x hx, inv_one, mul_one]
    continuousOn_coordChange := by
      intro i j
      have hc : Continuous
          (fun x : ↥((A.chart i).source ∩ (A.chart j).source) ↦
            A.transition i j x) := (A.transition_locallyConstant i j).continuous
      have htrans : ContinuousOn (fun x : S ↦ A.transition i j x)
          ((A.chart i).source ∩ (A.chart j).source) := by
        apply (continuousOn_iff_continuous_domRestrict).2
        have heq : ((A.chart i).source ∩ (A.chart j).source).domRestrict
            (fun x : S ↦ A.transition i j x) =
            (fun x : ↥((A.chart i).source ∩ (A.chart j).source) ↦
              A.transition i j x) := by
          funext x
          rfl
        rw [heq]
        exact hc
      exact continuous_snd.continuousOn.mul
        ((htrans.comp continuous_fst.continuousOn (fun x hx ↦ hx.1)).inv)
    coordChange_comp := by
      intro i j k x hx g
      rw [A.transition_comp i j k x hx, mul_inv_rev, mul_assoc]
  }
  refine ⟨Z, rfl, rfl, rfl, IsFiberBundle.isCoveringMap (F := OrderedProjectiveFrameGroup) ?_⟩
  intro x
  exact ⟨Z.localTrivAt x, Z.mem_localTrivAt_baseSet x⟩

end HolomorphicAnosov.Ghys
