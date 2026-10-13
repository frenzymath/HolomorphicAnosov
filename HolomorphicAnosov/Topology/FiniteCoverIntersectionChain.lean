import Mathlib.Topology.Connected.Clopen

open Set

namespace HolomorphicAnosov

/-- A finite closed cover of a preconnected core has connected intersection graph among
all members that meet the core. -/
theorem finite_cover_intersection_chain
    {ι α : Type*} [Finite ι] [DecidableEq ι] [TopologicalSpace α]
    (K : Set α) (s : ι → Set α) (hclosed : ∀ i, IsClosed (s i))
    (hmeets : ∀ i, (K ∩ s i).Nonempty) (hpre : IsPreconnected K)
    (hcover : K ⊆ ⋃ i, s i) :
    ∀ i j, Relation.ReflTransGen (fun i j => (s i ∩ s j).Nonempty) i j := by
  intro i j
  by_contra hnot
  let R : ι → ι → Prop := fun i j => (s i ∩ s j).Nonempty
  let T : Set ι := {k | Relation.ReflTransGen R i k}
  have hiT : i ∈ T := Relation.ReflTransGen.refl
  have hjT : j ∉ T := hnot
  let U : Set α := ⋃ k ∈ T, s k
  let V : Set α := ⋃ k ∈ Tᶜ, s k
  have hUclosed : IsClosed U := isClosed_iUnion_of_finite (fun k =>
    isClosed_iUnion_of_finite (fun hk => hclosed k))
  have hVclosed : IsClosed V := isClosed_iUnion_of_finite (fun k =>
    isClosed_iUnion_of_finite (fun hk => hclosed k))
  have hKV : K ⊆ U ∪ V := fun x hx => by
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover hx)
    by_cases hTk : k ∈ T
    · exact mem_union_left V (mem_iUnion₂.mpr ⟨k, hTk, hk⟩)
    · exact mem_union_right U (mem_iUnion₂.mpr ⟨k, hTk, hk⟩)
  have hdisj : Disjoint U V := by
    rw [disjoint_left]
    intro x hxU hxV
    obtain ⟨k, hkT, hxk⟩ := mem_iUnion₂.mp hxU
    obtain ⟨l, hlT, hxl⟩ := mem_iUnion₂.mp hxV
    have hreach : Relation.ReflTransGen R i l :=
      (show Relation.ReflTransGen R i k from hkT).tail ⟨x, hxk, hxl⟩
    exact hlT hreach
  have hKU : (K ∩ U).Nonempty := by
    obtain ⟨x, hxK, hxi⟩ := hmeets i
    exact ⟨x, hxK, mem_iUnion₂.mpr ⟨i, hiT, hxi⟩⟩
  have hKV' : (K ∩ V).Nonempty := by
    obtain ⟨x, hxK, hxj⟩ := hmeets j
    exact ⟨x, hxK, mem_iUnion₂.mpr ⟨j, hjT, hxj⟩⟩
  have hdisj' : K ∩ (U ∩ V) = ∅ := by rw [hdisj.inter_eq, inter_empty]
  have hor := (isPreconnected_iff_subset_of_disjoint_closed.mp hpre)
    U V hUclosed hVclosed hKV hdisj'
  rcases hor with hor | hor
  · obtain ⟨x, hxK, hxV⟩ := hKV'
    exact (Set.disjoint_left.mp hdisj) (hor hxK) hxV
  · obtain ⟨x, hxK, hxU⟩ := hKU
    exact (Set.disjoint_left.mp hdisj) hxU (hor hxK)

end HolomorphicAnosov
