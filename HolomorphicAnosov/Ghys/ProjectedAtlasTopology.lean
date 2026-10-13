import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Separation.Hausdorff

/-! Separation and countability for charts over a base (Lee) -/
open Set Filter TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u v w z

/-- A continuous projection over a second-countable Hausdorff base, with local charts on the inverse images of an open base cover, has Hausdorff and second-countable total space if its coordinate model does. (Lee, Lemma 1.23) -/
theorem projected_atlas_topology
    {L : Type u} {J : Type v} {H : Type w} {C : Type z}
    [TopologicalSpace L] [TopologicalSpace J] [TopologicalSpace H]
    [T2Space L] [SecondCountableTopology L]
    [T2Space H] [SecondCountableTopology H]
    (p : J → L) (hp : Continuous p)
    (U : C → Set L) (hopen : ∀ c, IsOpen (U c))
    (hcover : ∀ x : L, ∃ c, x ∈ U c)
    (E : C → OpenPartialHomeomorph J H)
    (hsource : ∀ c, (E c).source = p ⁻¹' U c) :
    T2Space J ∧ SecondCountableTopology J := by
  classical
  constructor
  · apply t2Space_iff_disjoint_nhds.mpr
    intro j k hjk
    by_cases hb : p j = p k
    · obtain ⟨c, hc⟩ := hcover (p j)
      have hj : j ∈ (E c).source := by rw [hsource]; exact hc
      have hk : k ∈ (E c).source := by
        rw [hsource]
        change p k ∈ U c
        exact hb ▸ hc
      have hne : E c j ≠ E c k := fun he ↦ hjk ((E c).injOn hj hk he)
      exact ((E c).continuousAt hj).disjoint (disjoint_nhds_nhds.mpr hne)
        ((E c).continuousAt hk)
    · exact (hp.continuousAt (x := j)).disjoint (disjoint_nhds_nhds.mpr hb)
        (hp.continuousAt (x := k))
  · obtain ⟨S, hS, hU⟩ := isOpen_iUnion_countable U hopen
    have hUall : ⋃ c, U c = univ := by
      ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      exact hcover x
    rw [hUall] at hU
    let : Countable S := hS.to_subtype
    let (c : S) : SecondCountableTopology (E c.1).source :=
      (E c.1).secondCountableTopology_source
    apply secondCountableTopology_of_countable_cover (fun c : S ↦ (E c.1).open_source)
    ext j
    simp only [mem_iUnion, mem_univ, iff_true]
    have hj : p j ∈ ⋃ c ∈ S, U c := hU ▸ mem_univ _
    obtain ⟨c, hc⟩ := mem_iUnion.1 hj
    obtain ⟨hcS, hc⟩ := mem_iUnion.1 hc
    refine ⟨⟨c, hcS⟩, ?_⟩
    rw [hsource]
    exact hc

end HolomorphicAnosov.Ghys
