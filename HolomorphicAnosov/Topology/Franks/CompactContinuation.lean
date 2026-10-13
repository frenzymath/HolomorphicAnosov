import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection

open Set Filter
open scoped Topology
namespace HolomorphicAnosov.FranksOriginalCover

/-- The compact bound in Franks (1969), Lemma 1.6, pp.121–122. On an arbitrary
partial continuation domain, the two complementary coordinates of `H θ` equal
the coordinates of two fixed compact parameter families. Their sum has compact
range. Properness of H gives one compact set containing every continuation value.
No continuity of θ at a missing boundary point, injectivity of H, or global
intersection is assumed. Empty parameter spaces and empty domains are allowed. -/
theorem compact_continuation_of_projected_sides
    {P V X Y : Type*} [TopologicalSpace P] [TopologicalSpace V]
    [AddCommGroup V] [ContinuousAdd V]
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (H : P → V) (hproper : IsProperMap H)
    (πu πs : V → V) (hsplit : ∀ v, πu v + πs v = v)
    (a : X → V) (b : Y → V) (ha : Continuous a) (hb : Continuous b)
    (D : Set (X × Y)) (θ : X × Y → P)
    (hu : ∀ z ∈ D, πu (H (θ z)) = a z.1)
    (hs : ∀ z ∈ D, πs (H (θ z)) = b z.2) :
    ∃ K : Set P, IsCompact K ∧ MapsTo θ D K := by
  let c : X × Y → V := fun z ↦ a z.1 + b z.2
  have hc : Continuous c := (ha.comp continuous_fst).add (hb.comp continuous_snd)
  refine ⟨H ⁻¹' range c, hproper.isCompact_preimage (isCompact_range hc), ?_⟩
  intro z hz
  change H (θ z) ∈ range c
  refine ⟨z, ?_⟩
  change a z.1 + b z.2 = H (θ z)
  rw [← hu z hz, ← hs z hz, hsplit]

/-- The preceding bound gives the convergent continuation subsequence used at
a missing corner. The same strictly increasing subsequence preserves the
original parameter limit. No boundary value of θ is assumed. -/
theorem continuation_subsequence_of_projected_sides
    {P V X Y : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace V] [AddCommGroup V] [ContinuousAdd V]
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (H : P → V) (hproper : IsProperMap H)
    (πu πs : V → V) (hsplit : ∀ v, πu v + πs v = v)
    (a : X → V) (b : Y → V) (ha : Continuous a) (hb : Continuous b)
    (D : Set (X × Y)) (θ : X × Y → P)
    (hu : ∀ z ∈ D, πu (H (θ z)) = a z.1)
    (hs : ∀ z ∈ D, πs (H (θ z)) = b z.2)
    (z : ℕ → X × Y) (hz : ∀ n, z n ∈ D) (z₀ : X × Y)
    (hlim : Tendsto z atTop (𝓝 z₀)) :
    ∃ (v : P) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (z ∘ φ) atTop (𝓝 z₀) ∧ Tendsto (θ ∘ z ∘ φ) atTop (𝓝 v) := by
  obtain ⟨K, hK, hmap⟩ := compact_continuation_of_projected_sides
    H hproper πu πs hsplit a b ha hb D θ hu hs
  obtain ⟨v, _, φ, hφ, hconv⟩ := hK.tendsto_subseq (fun n ↦ hmap (hz n))
  exact ⟨v, φ, hφ, hlim.comp hφ.tendsto_atTop, hconv⟩

/-- Relational form of the compact side bound, suitable for constructing the
partial intersection selector internally. Complementary coordinates are
constant on the respective leaf relations. Hence every possible intersection
of two compact continuous side families belongs to the proper preimage of
the compact range of the sum of the two side coordinates. -/
theorem compact_intersections_of_projected_sides
    {P V X Y : Type*} [TopologicalSpace P] [TopologicalSpace V]
    [AddCommGroup V] [ContinuousAdd V]
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (Lu Ls : P → P → Prop) (H : P → V) (hproper : IsProperMap H)
    (πu πs : V → V) (hπu : Continuous πu) (hπs : Continuous πs)
    (hsplit : ∀ v, πu v + πs v = v)
    (hu : ∀ x y, Lu x y → πu (H x) = πu (H y))
    (hs : ∀ x y, Ls x y → πs (H x) = πs (H y))
    (γ : X → P) (ρ : Y → P) (hγ : Continuous γ) (hρ : Continuous ρ) :
    ∃ K : Set P, IsCompact K ∧ ∀ r t p, Lu (γ r) p → Ls (ρ t) p → p ∈ K := by
  let c : X × Y → V := fun z ↦ πu (H (γ z.1)) + πs (H (ρ z.2))
  have hc : Continuous c :=
    (hπu.comp (hproper.continuous.comp (hγ.comp continuous_fst))).add
      (hπs.comp (hproper.continuous.comp (hρ.comp continuous_snd)))
  refine ⟨H ⁻¹' range c, hproper.isCompact_preimage (isCompact_range hc), ?_⟩
  intro r t p hr ht
  refine ⟨(r,t), ?_⟩
  change πu (H (γ r)) + πs (H (ρ t)) = H p
  rw [hu _ _ hr, hs _ _ ht, hsplit]

/-- Franks' projected-side compactness bound directly from affine leaf-image
inclusions. In finite dimension the algebraic projections associated with the
complementary stable and unstable subspaces are continuous. The projection
onto S annihilates U-displacements and the projection onto U annihilates
S-displacements. Their sum is the identity, so the preceding relational
compactness theorem applies. Surjectivity onto either affine leaf is not used. -/
theorem compact_intersections_of_complementary_affine_images
    {P V X Y : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (Lu Ls : P → P → Prop) (H : P → V) (hproper : IsProperMap H)
    (S U : Submodule ℝ V) (hSU : IsCompl S U)
    (hu : ∀ x y, Lu x y → H y - H x ∈ U)
    (hs : ∀ x y, Ls x y → H y - H x ∈ S)
    (γ : X → P) (ρ : Y → P) (hγ : Continuous γ) (hρ : Continuous ρ) :
    ∃ K : Set P, IsCompact K ∧ ∀ r t p, Lu (γ r) p → Ls (ρ t) p → p ∈ K := by
  apply compact_intersections_of_projected_sides Lu Ls H hproper
    (S.projection U hSU) (U.projection S hSU.symm)
    (S.projection U hSU).continuous_of_finiteDimensional
    (U.projection S hSU.symm).continuous_of_finiteDimensional
    (Submodule.projection_add_projection_eq_self hSU) _ _ γ ρ hγ hρ
  · intro x y hxy
    have hz := Submodule.projection_apply_of_mem_right hSU (hu x y hxy)
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm
  · intro x y hxy
    have hz := Submodule.projection_apply_of_mem_right hSU.symm (hs x y hxy)
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm

end HolomorphicAnosov.FranksOriginalCover
