import HolomorphicAnosov.Topology.FiniteFixedPointDisjointDomains

noncomputable section
open TopologicalSpace
open scoped BigOperators
namespace HolomorphicAnosov.FixedPointIndexInterface
universe u

/-- Finite localization of the ENR index in the canonical fixed-point domains.

Source: Dold (1.5), pp.1–2, and (2.3), p.3. Choose disjoint open neighborhoods
of the finite fixed set inside the corresponding canonical domains. Disjoint
additivity expresses the global index as the sum of the selected neighborhood
indices. Each canonical domain contains no other fixed point, so restriction
identifies its index with that neighborhood index. Finally the injective
finite enumeration reindexes the sum over the fixed-point finset.
The construction also handles the empty fixed set via the empty finite sum. -/
theorem enr_local_fixed_point_index_eq_target_sum
    {X : Type u} [TopologicalSpace X] [MetrizableSpace X] [CompactSpace X]
    (e : ENRRepresentation X) (f : C(X, X))
    (hfinite : {x : X | f x = x}.Finite) :
    let F : C((⊤ : Opens X), X) :=
      f.comp ⟨Subtype.val, continuous_subtype_val⟩
    enrLocalFixedPointIndex e (⊤ : Opens X) F (by
      change IsCompact ((Subtype.val : (⊤ : Opens X) → X) ⁻¹' {y : X | f y = y})
      exact (hfinite.preimage Subtype.val_injective.injOn).isCompact) =
      ∑ x ∈ hfinite.toFinset, finiteFixedPointLocalIndex e f hfinite x := by
  dsimp only
  let F : C((⊤ : Opens X), X) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨k, V, x₀, hmarked, hinj, hrange, hfix, htop, hdom, hpair, hcover⟩ :=
    finite_fixed_set_disjoint_canonical_domains f hfinite
  have hK : IsCompact (enrLocalFixedSet F) := by
    change IsCompact ((Subtype.val : (⊤ : Opens X) → X) ⁻¹' {y : X | f y = y})
    exact (hfinite.preimage Subtype.val_injective.injOn).isCompact
  obtain ⟨hVi, hadd⟩ :=
    (enr_local_fixed_point_index_conjugacy.{u, u} X e).2.2.2.2.1 (⊤ : Opens X) F hK k V
      (fun _ _ _ ↦ trivial) hpair hcover
  have hlocal : ∀ i, finiteFixedPointLocalIndex e f hfinite (x₀ i) =
      enrLocalFixedPointIndex e (V i)
        (enrRestrictLocalMap F (V i) (le_top : V i ≤ (⊤ : Opens X))) (hVi i) := by
    intro i
    let U := finiteFixedPointOpenDomain f hfinite (x₀ i)
    let g := finiteFixedPointLocalMap f hfinite (x₀ i)
    have hKU : IsCompact (enrLocalFixedSet g) := by
      change IsCompact ((Subtype.val : U → X) ⁻¹' {y : X | f y = y})
      exact (hfinite.preimage Subtype.val_injective.injOn).isCompact
    have hcover_i : ∀ x : U, g x = x.1 → x.1 ∈ (V i) := by
      intro x hx
      have hxfix : f x.1 = x.1 := by simpa [g, finiteFixedPointLocalMap] using hx
      have hxU : x.1 ∈ finiteFixedPointOpenDomain f hfinite (x₀ i) := x.property
      have hxeq : x.1 = x₀ i := by
        by_contra hne
        exact hxU (by
          simp [hxfix, hne])
      simpa [hxeq] using hmarked i
    obtain ⟨hVi', hidx⟩ :=
      (enr_local_fixed_point_index_conjugacy.{u, u} X e).2.2.1 U (V i) (hdom i) g hKU hcover_i
    unfold finiteFixedPointLocalIndex
    dsimp [g, U, F, enrRestrictLocalMap, finiteFixedPointLocalMap]
    convert hidx using 1 <;> rfl
  rw [hadd]
  trans ∑ i, finiteFixedPointLocalIndex e f hfinite (x₀ i)
  · exact Finset.sum_congr rfl (fun i _ ↦ (hlocal i).symm)
  · apply Finset.sum_bij (s := Finset.univ) (t := hfinite.toFinset)
        (fun i _ ↦ x₀ i)
    · intro i hi
      rw [hfinite.mem_toFinset]
      rw [← hrange]
      exact ⟨i, rfl⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      exact hinj heq
    · intro x hx
      have hxf : x ∈ {y : X | f y = y} := hfinite.mem_toFinset.mp hx
      have hxf' : x ∈ Set.range x₀ := by
        rw [hrange]
        exact hxf
      rcases Set.mem_range.mp hxf' with ⟨i, hi⟩
      exact ⟨i, Finset.mem_univ _, hi⟩
    · intro i hi
      rfl

end HolomorphicAnosov.FixedPointIndexInterface
