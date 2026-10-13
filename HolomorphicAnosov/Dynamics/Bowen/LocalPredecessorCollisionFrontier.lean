import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Constructions

/-!
# Local predecessor collisions force a factor frontier

Bowen, Markov Partitions and Minimal Sets for Axiom A Diffeomorphisms (1970),
Lemma 6(b), p.911. The regular-closed inverse target slice supplies a common
open unstable core. Disjoint rectangle interiors then force a common stable
coordinate into a stable-factor frontier. Both maps below are partial charts,
with all source and target containments retained. No global collar is used.
-/

namespace HolomorphicAnosov.Dynamics.Bowen
open Set

/-- Local geometric collision obstruction. A regular-closed target core is
transported into both predecessor unstable factors by a partial chart. The
predecessor products lie in one local ambient product chart and map into
rectangles with disjoint interiors. Their common stable coordinates therefore
lie in the first stable-factor frontier.

The second stable factor is regular closed, including singleton factors.
The target core is nonempty but need not contain its base in its interior.
The product-chart and inverse-slice chart guards are explicit hypotheses to
be instantiated from the native plaque construction. -/
theorem localPredecessorCollisionFrontier
    {X U S T : Type*} [TopologicalSpace X] [TopologicalSpace U]
    [TopologicalSpace S] [TopologicalSpace T]
    (e : OpenPartialHomeomorph X (U × S))
    (h : OpenPartialHomeomorph T U)
    (C : Set T) (hC : C = closure (interior C)) (hCne : C.Nonempty)
    (hCsource : C ⊆ h.source)
    (C₁ C₂ : Set U) (D₁ D₂ : Set S) (R₁ R₂ : Set X)
    (hcover₁ : h '' C ⊆ C₁) (hcover₂ : h '' C ⊆ C₂)
    (hD₂ : D₂ = closure (interior D₂))
    (hguard₁ : C₁ ×ˢ D₁ ⊆ e.target) (hguard₂ : C₂ ×ˢ D₂ ⊆ e.target)
    (hrect₁ : e.symm '' (C₁ ×ˢ D₁) ⊆ R₁)
    (hrect₂ : e.symm '' (C₂ ×ˢ D₂) ⊆ R₂)
    (hdisj : Disjoint (interior R₁) (interior R₂)) :
    D₁ ∩ D₂ ⊆ frontier D₁ := by
  have hcore : (interior C).Nonempty := by
    by_contra hn
    have he : interior C = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [hC, he, closure_empty] at hCne
    exact hCne.ne_empty rfl
  let V : Set U := h '' interior C
  have hV : IsOpen V := h.isOpen_image_of_subset_source isOpen_interior
    (interior_subset.trans hCsource)
  have hVne : V.Nonempty := hcore.image h
  have hV₁ : V ⊆ C₁ := (image_mono interior_subset).trans hcover₁
  have hV₂ : V ⊆ C₂ := (image_mono interior_subset).trans hcover₂
  have hprodDisj : Disjoint (interior (C₁ ×ˢ D₁)) (interior (C₂ ×ˢ D₂)) := by
    apply Set.disjoint_left.mpr
    intro w hw₁ hw₂
    have hopen₁ := e.isOpen_image_symm_of_subset_target isOpen_interior
      (interior_subset.trans hguard₁)
    have hopen₂ := e.isOpen_image_symm_of_subset_target isOpen_interior
      (interior_subset.trans hguard₂)
    have hsub₁ : e.symm '' interior (C₁ ×ˢ D₁) ⊆ interior R₁ :=
      hopen₁.subset_interior_iff.mpr ((image_mono interior_subset).trans hrect₁)
    have hsub₂ : e.symm '' interior (C₂ ×ˢ D₂) ⊆ interior R₂ :=
      hopen₂.subset_interior_iff.mpr ((image_mono interior_subset).trans hrect₂)
    exact Set.disjoint_left.mp hdisj
      (hsub₁ ⟨w, hw₁, rfl⟩) (hsub₂ ⟨w, hw₂, rfl⟩)
  intro s hs
  apply (mem_frontier_iff_notMem_interior hs.1).mpr
  intro hsint
  have hscl : s ∈ closure (interior D₂) := hD₂ ▸ hs.2
  obtain ⟨t, ht₁, ht₂⟩ := mem_closure_iff.mp hscl (interior D₁)
    isOpen_interior hsint
  obtain ⟨u, hu⟩ := hVne
  have hu₁ : u ∈ interior C₁ := hV.subset_interior_iff.mpr hV₁ hu
  have hu₂ : u ∈ interior C₂ := hV.subset_interior_iff.mpr hV₂ hu
  have hp₁ : (u, t) ∈ interior (C₁ ×ˢ D₁) := by
    simpa only [interior_prod_eq, mem_prod] using And.intro hu₁ ht₁
  have hp₂ : (u, t) ∈ interior (C₂ ×ˢ D₂) := by
    simpa only [interior_prod_eq, mem_prod] using And.intro hu₂ ht₂
  exact Set.disjoint_left.mp hprodDisj hp₁ hp₂

end HolomorphicAnosov.Dynamics.Bowen

