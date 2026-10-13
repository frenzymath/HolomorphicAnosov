import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Dynamics.AsymptoticLeaf

/-! Leaf ranges equal to asymptotic classes identify the native partition relation with forward
asymptoticity. (Hirsch–Pugh–Shub, §6B–7, pp.114–116; Shub, Def. 2.1, pp.8–9) -/

noncomputable section
open scoped ContDiff Manifold Topology _root_.Topology
open Set

universe u
namespace HolomorphicAnosov

/-- A covered native partition whose leaf ranges are asymptotic classes induces the corresponding
partition-level asymptotic equivalence. -/
theorem native_partition_asymptotic_relation_g10 {r : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin r → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ (L i)]
    (P : RealTangentDistribution 𝓘(ℝ, E) M)
    (F : HPS.LeafPartition P ι L (fun _ ↦ r)) (f : M ≃ₜ M)
    (hrange : ∀ i z, Set.range (F.leaf i).inclusion =
      {y | ForwardAsymptotic f ((F.leaf i).inclusion z) y}) (x y : M) :
    (∃ i a b, (F.leaf i).inclusion a = x ∧ (F.leaf i).inclusion b = y) ↔
      ForwardAsymptotic f x y := by
  constructor
  · rintro ⟨i, a, b, rfl, rfl⟩
    have hy : (F.leaf i).inclusion b ∈ Set.range (F.leaf i).inclusion := ⟨b, rfl⟩
    rw [hrange i a] at hy
    exact hy
  · intro hy
    obtain ⟨i, a, ha⟩ := F.cover x
    have hb : y ∈ Set.range (F.leaf i).inclusion := by
      rw [hrange i a, ha]
      exact hy
    obtain ⟨b, hb⟩ := hb
    exact ⟨i, a, b, ha, hb⟩


end HolomorphicAnosov
