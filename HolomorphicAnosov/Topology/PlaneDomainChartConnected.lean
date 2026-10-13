import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic

namespace HolomorphicAnosov.Topology

/-- The finite chart preimage of a connected sphere set avoiding infinity is connected.
This is the direct topological transport through the open embedding `OnePoint.some`.
Source: Conway I, VIII.2.2 chart reduction; Mathlib open embedding API. -/
theorem isConnected_onePoint_some_preimage
    {G : Set (OnePoint ℂ)} (hG : IsConnected G)
    (hinfty : (OnePoint.infty : OnePoint ℂ) ∉ G) :
    IsConnected (OnePoint.some ⁻¹' G) := by
  have hGimage : OnePoint.some '' (OnePoint.some ⁻¹' G) = G := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · intro z hz
      obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp
        (show z ≠ OnePoint.infty from fun he ↦ hinfty (he ▸ hz))
      exact ⟨w, hz, rfl⟩
  have hi : IsConnected (OnePoint.some '' (OnePoint.some ⁻¹' G)) := by
    rwa [hGimage]
  exact ⟨Set.image_nonempty.mp hi.nonempty,
    OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp hi.isPreconnected⟩

end HolomorphicAnosov.Topology
