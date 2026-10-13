import HolomorphicAnosov.Paper.Ghys.NativeComplexLineVectorBundle
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineMetricRestriction
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExistsNoConnected
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds

/-! This file gives Hermitian metrics on native complex line fibres with a continuous total-space
norm in the topology induced by the tangent inclusion. (Ghys, Lemma 3.3, p. 592; Moroianu, §4.2,
pp. 24–25; Hatcher, Lemma 1.1, p. 8, Prop. 1.3, pp. 12–13) -/

noncomputable section
namespace HolomorphicAnosov

open Bundle Set _root_.Topology TopologicalSpace
open scoped ContDiff Manifold

universe u
attribute [local instance] complex_isManifold_real

/-- A continuous rank-one complex tangent subbundle over a compact manifold admits fibrewise
Hermitian cores whose norm is continuous in the induced total-space topology. -/
theorem exists_native_complex_line_metric
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (T : ContinuousComplexTangentSubbundle (complexModel d) M)
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hTS : T.toDistribution = S)
    (hRank : ∀ x, Module.finrank ℂ (S x) = 1) :
    let E := fun x : M ↦ ↥(S x)
    letI : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∃ core : ∀ x, InnerProductSpace.Core ℂ (S x),
      letI : ∀ x, NormedAddCommGroup (S x) := fun x ↦
        (core x).toNormedAddCommGroup
      Continuous (fun z : TotalSpace ℂ (fun x ↦ S x) ↦ ‖z.snd‖) := by
  subst S
  dsimp only
  let : TopologicalSpace (TotalSpace ℂ (fun x : M ↦ ↥(T.toDistribution x))) :=
    TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let : IsManifold (realModel d) ∞ M := complex_isManifold_real d M
  obtain ⟨g, hg⟩ := OneFormBundle.original_smooth_tangent_metric_exists_no_connected
    (d := d) (M := M)
  have hAmbient := Preparation.continuous_hermitian_tangent_norm g hg
  have hinc : Continuous (fun z : TotalSpace ℂ (fun x : M ↦ ↥(T.toDistribution x) ) ↦
      (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) :=
    continuous_induced_dom
  have hc : Continuous (fun z : TotalSpace ℂ (fun x : M ↦ ↥(T.toDistribution x)) ↦
      Real.sqrt ((g z.proj).inner z.snd.val z.snd.val).re) := by
    exact hAmbient.comp hinc
  exact exists_restricted_hermitian_metric g hc


end HolomorphicAnosov
