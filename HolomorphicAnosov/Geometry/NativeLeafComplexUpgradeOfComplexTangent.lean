import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.InvariantRange
import HolomorphicAnosov.Geometry.LocalProjectionGraph
import HolomorphicAnosov.Geometry.GraphAtlasGluing
import HolomorphicAnosov.Geometry.GraphAtlasToUpgrade
import HolomorphicAnosov.Geometry.NativeLeafGraphInclusionProperties
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle

/-! This file equips a smooth real immersed leaf with complex tangent images with a compatible
complex manifold structure on its source topology. (Demailly, I Lemma 7.15, p. 60) -/

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v
attribute [local instance] complex_isManifold_real

/-- A smooth real immersion with complex tangent images induces a compatible complex manifold
structure on its source carrier and topology. (Demailly, I Lemma 7.15, p. 60) -/
theorem nativeLeafComplexUpgrade_of_complex_tangent
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin (2*k) → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (P : ContinuousRealTangentSubbundle (realModel d) M)
    (hinc : Manifold.IsImmersion 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) ∞ inc)
    (hP : ∀ x : L, (mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc x).range =
      P.toDistribution (inc x))
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x : L, ((S.toDistribution (inc x)).restrictScalars ℝ).map
      (complexTangentToReal d (inc x)).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc x).range) :
    Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2*k) k inc) := by
  have hlocal : ∀ z : L, Nonempty (NativeLeafLocalProjectionGraph (k := k) (d := d) inc z) := by
    intro z
    exact native_leaf_local_projection_graph inc z P hinc hP S hS
  have hatlas : Nonempty (NativeLeafGraphAtlas (k := k) (d := d) inc) := by
    exact native_leaf_graph_atlas_gluing inc hlocal
  rcases hatlas with ⟨hatlas⟩
  have hprops := native_leaf_graph_inclusion_properties inc hatlas hlocal
  have hhol : (letI := hatlas.charts
      ContMDiff (complexModel k) (complexModel d) ∞ inc) := hprops.1
  have himm : (letI := hatlas.charts
      ∀ z : L, Manifold.IsImmersionAt (complexModel k) (complexModel d) ∞ inc z) := hprops.2
  have hupgrade := native_leaf_graph_atlas_to_complex_upgrade inc hatlas hhol himm
  exact hupgrade

end HolomorphicAnosov
