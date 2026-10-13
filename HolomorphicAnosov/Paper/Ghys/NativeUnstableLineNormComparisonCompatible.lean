import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineVectorBundle
import HolomorphicAnosov.Analysis.CompactComplexLineNormComparison
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExistsNoConnected
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds

open Bundle Set
open scoped ContDiff Bundle Manifold Topology _root_.Topology

noncomputable section
namespace HolomorphicAnosov

universe u
attribute [local instance] complex_isManifold_real

/-- A continuous Hermitian norm on the native complex unstable line is uniformly comparable with the restriction of a smooth ambient Hermitian metric. (Ghys, Lemma 3.3) -/
theorem exists_native_unstable_line_norm_comparison_compatible
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (T : ContinuousComplexTangentSubbundle (complexModel d) M)
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hTS : T.toDistribution = S)
    (hRank : ∀ x, Module.finrank ℂ (S x) = 1)
    (core : ∀ x, InnerProductSpace.Core ℂ (S x))
    (hD : letI : ∀ x, NormedAddCommGroup (S x) := fun x ↦
        (core x).toNormedAddCommGroup
      letI : TopologicalSpace (Bundle.TotalSpace ℂ (fun x : M ↦ ↥(S x))) :=
        TopologicalSpace.induced
          (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
      Continuous (fun z : Bundle.TotalSpace ℂ (fun x : M ↦ ↥(S x)) ↦ ‖z.snd‖)) :
    letI : ∀ x, NormedAddCommGroup (S x) := fun x ↦
      (core x).toNormedAddCommGroup
    letI : TopologicalSpace (Bundle.TotalSpace ℂ (fun x : M ↦ ↥(S x))) :=
      TopologicalSpace.induced
        (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∃ h : HermitianTangentMetricCore d M, IsSmoothHermitianTangentMetric h ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ x (v : S x),
          c * hermitianBoundsNorm h x v.1 ≤ ‖v‖ ∧
            ‖v‖ ≤ C * hermitianBoundsNorm h x v.1 := by
  classical
  let : TopologicalSpace (TotalSpace ℂ (fun x : M ↦ ↥(S x))) :=
    TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  obtain ⟨fb, vb⟩ := exists_native_complex_line_vectorBundle T S hTS hRank
  let : FiberBundle ℂ (fun x : M ↦ ↥(S x)) := fb
  let : VectorBundle ℂ ℂ (fun x : M ↦ ↥(S x)) := vb
  obtain ⟨h, hh⟩ := OneFormBundle.original_smooth_tangent_metric_exists_no_connected
    (d := d) (M := M)
  have hinc : Continuous (fun v : TotalSpace ℂ (fun x : M ↦ ↥(S x)) ↦
      (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) :=
    continuous_induced_dom
  have hq := (Preparation.continuous_hermitian_tangent_norm h hh).comp hinc
  have hp : Continuous (fun v : TotalSpace ℂ (fun x : M ↦ ↥(S x)) ↦
      HermitianFibreAlgebra.coreLength (core v.proj) v.snd) := hD
  obtain ⟨c, C, hc, hcC, hcomp⟩ := compact_complex_line_norm_comparison
    (trivializationAt ℂ (fun x : M ↦ ↥(S x)))
    (fun x ↦ ⟨x, FiberBundle.mem_baseSet_trivializationAt ℂ (fun x : M ↦ ↥(S x)) x⟩)
    (fun x v ↦ HermitianFibreAlgebra.coreLength (core x) v)
    (fun x v ↦ HermitianFibreAlgebra.coreLength (h x) v.val)
    hp hq
    (fun x _ hv ↦ HermitianFibreAlgebra.coreLength_pos (core x) hv)
    (fun x v hv ↦ HermitianFibreAlgebra.coreLength_pos (h x)
      (fun hzero ↦ hv (Subtype.ext hzero)))
    (fun x a v ↦ HermitianFibreAlgebra.coreLength_complex_smul (core x) a v)
    (fun x a v ↦ HermitianFibreAlgebra.coreLength_complex_smul (h x) a v.val)
  exact ⟨h, hh, c, C, hc, hcC, hcomp⟩


end HolomorphicAnosov
