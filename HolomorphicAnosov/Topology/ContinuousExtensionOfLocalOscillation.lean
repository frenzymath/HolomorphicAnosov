import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.DenseEmbedding

/-!
# Continuous extension from locally vanishing oscillation

This is an explicit proof of the continuous-extension step omitted in Tao,
246C Notes 2 (12 April 2018), Theorem 20, first paragraph of the proof.
The local small-image criterion applies to the shrinking disk caps there.
-/

open Set Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.Topology

/-- A function on a dense metric subspace extends uniquely and continuously to
its ambient space if its oscillation tends to zero near every ambient point.
The target is a complete metric space; compactness and a uniform choice of
radii over the source are unnecessary.

Agent-written expansion of the extension step in Tao, 246C Notes 2, Theorem 20.
Proof: the image of the dense-subspace neighborhood filter at each point is
nontrivial. The small-oscillation hypothesis gives a set of arbitrarily small
diameter in this filter, making it Cauchy. Completeness supplies a limit.
Mathlib's dense extension theorem makes these pointwise limits jointly
continuous. The same hypothesis gives continuity on the original subspace,
so the extension agrees with the original function. Two continuous extensions
agree on a dense set and hence everywhere, since the target is Hausdorff. -/
theorem exists_unique_continuous_extension_of_local_oscillation
    {X Y : Type*} [PseudoMetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    (s : Set X) (hs : Dense s) (f : s → Y)
    (hosc : ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ a b : s,
      dist (a : X) x < δ → dist (b : X) x < δ → dist (f a) (f b) < ε) :
    ∃! F : X → Y, Continuous F ∧ ∀ a : s, F a = f a := by
  have hf : Continuous f := by
    apply Metric.continuous_iff.mpr
    intro b ε hε
    obtain ⟨δ, hδ, hh⟩ := hosc b ε hε
    refine ⟨δ, hδ, ?_⟩
    intro a ha
    exact hh a b ha (by simpa using hδ)
  have hlimit (x : X) : ∃ y, Tendsto f (comap Subtype.val (𝓝 x)) (𝓝 y) := by
    have : NeBot (comap (Subtype.val : s → X) (𝓝 x)) := hs.comap_val_nhds_neBot x
    apply cauchy_map_iff_exists_tendsto.mp
    apply Metric.uniformity_basis_dist.cauchy_iff.mpr
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := hosc x ε hε
    let A : Set s := {a | dist (a : X) x < δ}
    have hA : A ∈ comap (Subtype.val : s → X) (𝓝 x) :=
      mem_comap.mpr ⟨Metric.ball x δ, Metric.ball_mem_nhds x hδ, fun _ ha ↦ ha⟩
    refine ⟨f '' A, image_mem_map hA, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hh a b ha hb
  refine ⟨hs.extend f, ⟨hs.continuous_extend hlimit, hs.extend_eq hf⟩, ?_⟩
  intro F hF
  exact (hs.extend_unique hF.2 hF.1).symm

end HolomorphicAnosov.Topology

