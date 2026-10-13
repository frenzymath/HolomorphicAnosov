import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Filter Metric
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- A holomorphic bijection on an open complex set defines a homeomorphism of its source
and target subtypes, with the original forward map. This is an agent-written expansion of
the interior-homeomorphism step omitted by the Carathéodory parent source. Tao, 246C Notes 2, Theorem 20 proof,
lines 249–255, starts from this interior conformal homeomorphism. The topology conversion
uses Mathlib's local open-mapping dichotomy: injectivity excludes a constant germ because
no singleton is a neighborhood in ℂ. Thus open subsets of the source have open image.
The continuous open partial equivalence then restricts to the claimed homeomorphism. -/
theorem exists_homeomorph_eq_holomorphic_bijOn
    {D Q : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ φ D) (hbij : BijOn φ D Q) :
    ∃ e : D ≃ₜ Q, ∀ z : D, (e z : ℂ) = φ z := by
  classical
  let p := hbij.toPartialEquiv φ D Q
  have hop : IsOpenMap (p.source.domRestrict p) := by
    intro W hW
    have hs : IsOpen ((Subtype.val : D → ℂ) '' W) :=
      hD.isOpenEmbedding_subtypeVal.isOpenMap W hW
    have heq : p.source.domRestrict p '' W = φ '' ((Subtype.val : D → ℂ) '' W) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
    rw [heq]
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hz, rfl⟩
    have hzD : z ∈ D := Subtype.coe_image_subset _ _ hz
    have ha := hhol.analyticOnNhd hD z hzD
    have hnot : ¬ ∀ᶠ a in 𝓝 z, φ a = φ z := by
      intro hc
      have hsingle : ({z} : Set ℂ) ∈ 𝓝 z := by
        filter_upwards [hc, hD.mem_nhds hzD] with a hfa haD
        exact hbij.injOn haD hzD hfa
      exact not_isOpen_singleton z
        (isOpen_singleton_of_finite_mem_nhds z hsingle (Set.finite_singleton z))
    exact ha.eventually_constant_or_nhds_le_map_nhds.resolve_left hnot
      (image_mem_map (hs.mem_nhds hz))
  let e0 := OpenPartialHomeomorph.ofContinuousOpenRestrict p hhol.continuousOn hop hD
  refine ⟨e0.toHomeomorphSourceTarget, ?_⟩
  intro z
  rfl
end HolomorphicAnosov.Analysis
