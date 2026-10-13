import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact

/-!
# Compact radial restrictions are homeomorphisms onto their images

This is the compact-to-Hausdorff interface used in Cairns' §4(C2) front
construction.  Once the geometric argument has supplied compactness,
continuity, and injectivity of a radial normalization on a front, the map is
a homeomorphism onto its actual image.  The geometric injectivity and the
specific radial formula remain hypotheses of the parent construction; this
lemma does not assert them.
-/

namespace HolomorphicAnosov

open Set

/-- A continuous injective map on a compact set is a homeomorphism from that
set (with its subtype topology) onto its actual image.  This is the
compact-to-Hausdorff step in the radial front argument of Cairns §4(C2). -/
theorem halfSector_compact_radial_homeomorph
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] [T2Space F]
    (L : Set E) (f : E → F) (hL : IsCompact L)
    (hf : ContinuousOn f L) (hinj : Set.InjOn f L) :
    ∃ h : L ≃ₜ f '' L, ∀ x : L, (h x : F) = f x := by
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let g : L → f '' L := fun x => ⟨f x, ⟨x.1, x.2, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hinj x.2 y.2
      exact congrArg Subtype.val hxy
    · intro y
      rcases y.2 with ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : L ≃ f '' L := Equiv.ofBijective g hg
  have hge : Continuous g := by
    exact (hf.comp_continuous continuous_subtype_val (fun x ↦ x.2)).subtype_mk
      (fun x ↦ ⟨x.1, x.2, rfl⟩)
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := e) hge, ?_⟩
  intro x
  rfl

end HolomorphicAnosov
