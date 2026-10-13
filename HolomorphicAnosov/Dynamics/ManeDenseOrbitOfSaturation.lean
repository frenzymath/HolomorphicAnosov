import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.Continuous

namespace HolomorphicAnosov

open Set

/-- Mañé, *Ergodic Theory and Differentiable Dynamics*, I§11 Proposition 11.4,
pp.69–70, the countable-basis/Baire argument in (c)⇒(b). If every nonempty open
set has dense backward saturation, a continuous map of a nonempty second-countable
Baire space has a dense forward orbit. Choose a countable basis omitting the empty
set. Each basis element's backward saturation is open and dense; Baire gives a
point in their intersection. Its orbit meets every basis element and hence every
nonempty open set. This conclusion only needs the zero-tail case of the source's
stronger argument that every orbit tail is dense. -/
theorem mane_exists_dense_forward_orbit_of_dense_saturation
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [BaireSpace X] [Nonempty X] (f : X → X) (hf : Continuous f)
    (hsat : ∀ U : Set X, IsOpen U → U.Nonempty →
      Dense (⋃ n : ℕ, f^[n] ⁻¹' U)) :
    ∃ x : X, Dense (Set.range (fun n : ℕ ↦ f^[n] x)) := by
  let B := TopologicalSpace.countableBasis X
  let S : B → Set X := fun U ↦ ⋃ n : ℕ, f^[n] ⁻¹' (U : Set X)
  have hB := TopologicalSpace.isBasis_countableBasis X
  have hSopen : ∀ U, IsOpen (S U) := by
    intro U
    exact isOpen_iUnion fun n ↦ (hB.isOpen U.property).preimage (hf.iterate n)
  have hSdense : ∀ U, Dense (S U) := by
    intro U
    apply hsat _ (hB.isOpen U.property)
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    exact TopologicalSpace.empty_notMem_countableBasis X (he ▸ U.property)
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen hSopen hSdense).nonempty
  refine ⟨x, dense_iff_inter_open.mpr ?_⟩
  intro U hU ⟨y, hy⟩
  obtain ⟨V, hV, hyV, hVU⟩ := hB.exists_subset_of_mem_open hy hU
  have hxV : x ∈ S ⟨V, hV⟩ := mem_iInter.mp hx ⟨V, hV⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp hxV
  exact ⟨f^[n] x, hVU hn, ⟨n, rfl⟩⟩

end HolomorphicAnosov
