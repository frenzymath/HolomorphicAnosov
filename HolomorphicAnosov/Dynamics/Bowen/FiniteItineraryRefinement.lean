import HolomorphicAnosov.Topology.RegularOpenBooleanAtoms
import HolomorphicAnosov.Dynamics.Bowen.ExistsGoodOrbitInOpen

namespace HolomorphicAnosov.Dynamics.Bowen
open Set

/-- The topological part of Bowen's original-map refinement, Lemma 23, p.738.

For a finite regular-closed cover with disjoint interiors, the closures of
finite itinerary interiors again cover the space and have disjoint interiors.
Their interiors are the literal itinerary intersections. Empty words and empty
itinerary sets are included; a partition discards the latter afterwards.

Proof: each inverse image of an original rectangle is regular closed because
homeomorphisms preserve closure and interior. Bowen Lemma 19 makes the finite
intersection of their interiors regular open, giving the two closure identities.
Different words differ at a time, so the corresponding itinerary interiors are
disjoint by the original disjointness. The union of the original interiors is
dense, since closure commutes with its finite union and the rectangles cover.
Every nonempty open set meets an orbit segment in this dense open union; choosing
a label at each time yields an itinerary interior meeting that open set. Thus
the union of itinerary interiors is dense. Taking closure commutes with the
finite union of words and proves coverage. Finally each itinerary closure is
contained in every closed inverse-image rectangle constraining it.
DAG node: `dynamics.bowen_finite_itinerary_refinement_g17`. -/
theorem finiteItineraryRefinement
    {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (N m : ℕ)
    (P : Fin N → Set X)
    (hreg : ∀ i, P i = closure (interior (P i)))
    (hcover : (⋃ i, P i) = univ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (interior (P i)) (interior (P j))) :
    let V : (Fin m → Fin N) → Set X := fun w ↦
      ⋂ k : Fin m, (⇑(f ^ k.val) : X → X) ⁻¹' interior (P (w k))
    let E : (Fin m → Fin N) → Set X := fun w ↦ closure (V w)
    (∀ w, interior (E w) = V w ∧ E w = closure (interior (E w))) ∧
      (∀ w v, w ≠ v → Disjoint (interior (E w)) (interior (E v))) ∧
      (⋃ w, E w) = univ ∧
      (∀ w (k : Fin m), E w ⊆ (⇑(f ^ k.val) : X → X) ⁻¹' P (w k)) := by
  classical
  dsimp only
  let V : (Fin m → Fin N) → Set X := fun w ↦
    ⋂ k : Fin m, (⇑(f ^ k.val) : X → X) ⁻¹' interior (P (w k))
  have hclosed (i : Fin N) : IsClosed (P i) := hreg i ▸ isClosed_closure
  have hV (w : Fin m → Fin N) : interior (closure (V w)) = V w := by
    let Q : Fin m → Set X := fun k ↦ (⇑(f ^ k.val) : X → X) ⁻¹' P (w k)
    have hQ (k : Fin m) : Q k = closure (interior (Q k)) := by
      dsimp only [Q]
      rw [← (f ^ k.val).preimage_interior, ← (f ^ k.val).preimage_closure, ← hreg]
    have hh := (HolomorphicAnosov.Topology.manningBowen_regularOpen_booleanAtoms
      Q (fun _ : Fin 0 ↦ (∅ : Set X)) hQ (by simp)).2.2.2.1
    simpa only [V, Q, ← Homeomorph.preimage_interior] using hh
  have hZ : Dense (⋃ i, interior (P i)) := by
    rw [dense_iff_closure_eq, closure_iUnion_of_finite]
    simpa only [← hreg] using hcover
  have hVdense : Dense (⋃ w, V w) := by
    apply dense_iff_inter_open.mpr
    intro W hW hWne
    obtain ⟨x, hxW, hx⟩ := exists_good_orbit_in_open f (isOpen_iUnion fun _ ↦ isOpen_interior)
      hZ hW hWne m
    have hxk (k : Fin m) : ∃ i, (f ^ k.val) x ∈ interior (P i) :=
      mem_iUnion.mp (hx k.val (Nat.le_of_lt k.isLt))
    choose w hw using hxk
    exact ⟨x, hxW, mem_iUnion.mpr ⟨w, mem_iInter.mpr hw⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    exact ⟨hV w, congrArg closure (hV w).symm⟩
  · intro w v hwv
    rw [hV w, hV v]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hwv
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hdisj (w k) (v k) hk)
      (mem_iInter.mp hx k) (mem_iInter.mp hy k)
  · simpa only [closure_iUnion_of_finite] using hVdense.closure_eq
  · intro w k
    apply closure_minimal _ ((hclosed (w k)).preimage (f ^ k.val).continuous)
    intro x hx
    exact (interior_subset (s := P (w k))) (mem_iInter.mp hx k)

end HolomorphicAnosov.Dynamics.Bowen
