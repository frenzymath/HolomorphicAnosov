import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGenerator
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold

universe u v
namespace HolomorphicAnosov.Paper.Zhang
open scoped ContDiff Topology _root_.Topology
open Set Filter

/-- Each one-parameter subgroup `t ↦ t • e` of a continuous vector action by biholomorphisms has a
smooth real generator field. (Bochner–Montgomery, Lemmas 2 and 5, pp. 687–691) -/
theorem actual_one_parameter_generator
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (act : V → Biholomorph d d M M)
    (hzero : ∀ x : M, act 0 x = x)
    (hadd : ∀ v w : V, ∀ x : M, act (v + w) x = act v (act w x))
    (hc : Continuous (fun p : V × M ↦ act p.1 p.2)) (e : V) :
    let := complex_isManifold_real d M
    ∃ X : (x : M) → TangentSpace (realModel d) x,
      ContMDiff (realModel d) (realModel d).tangent ∞
        (fun x ↦ (⟨x, X x⟩ : TangentBundle (realModel d) M)) ∧
      ∀ x, ∃ L : TangentSpace (modelWithCornersSelf ℝ ℝ) 0 →L[ℝ]
          TangentSpace (realModel d) (act ((0 : ℝ) • e) x),
        HasMFDerivAt (modelWithCornersSelf ℝ ℝ) (realModel d)
          (fun t : ℝ ↦ act (t • e) x) 0 L ∧
        X x = tangentSpaceCast (realModel d) (act ((0 : ℝ) • e) x) x
          (L ((tangentSpaceCastModel (modelWithCornersSelf ℝ ℝ) 0).symm 1)) := by
  let := complex_isManifold_real d M
  apply one_parameter_smooth_generator (fun t x ↦ act (t • e) x)
  · exact hc.comp ((continuous_fst.smul continuous_const).prodMk continuous_snd)
  · simpa only [zero_smul] using hzero
  · intro s t x
    simpa only [add_smul] using (hadd (s • e) (t • e) x).symm
  · intro t
    exact ⟨(act (t • e)).toReal, fun _ ↦ rfl⟩


end HolomorphicAnosov.Paper.Zhang
