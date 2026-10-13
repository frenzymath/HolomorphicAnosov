import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

namespace HolomorphicAnosov

open Set

universe u

variable {X : Type u} [MetricSpace X] [CompactSpace X]

/-- A continuous map on the open ε-pair domain has a uniform modulus on the closed
half-radius pair core. The output is stated using the subtype of the original
pair domain, so no total extension outside the domain is introduced.

Source: the uniform-continuity step in Bowen (1970), Lemma 5, p.728.
This agent-written compact-core expansion fills step B2 of
`topo.manning_bowen_initial_cover_uniform_saturation`: the closed core is compact,
its inclusion into the open pair domain is continuous, and Heine–Cantor applies.
Halve its modulus and bound it by ε/4 to cover non-strict input distances. -/
theorem compactPairCore_uniformModulus
    {ε : ℝ} (hε : 0 < ε)
    {f : {p : X × X | dist p.1 p.2 < ε} → X} (hf : Continuous f) :
    ∀ e : ℝ, 0 < e → ∃ d : ℝ, 0 < d ∧ d < ε / 2 ∧
      ∀ (p q : {p : X × X | dist p.1 p.2 < ε}),
        dist p.1.1 p.1.2 ≤ ε / 2 → dist q.1.1 q.1.2 ≤ ε / 2 →
        dist p.1 q.1 ≤ d → dist (f p) (f q) < e := by
  intro e he
  let K : Set (X × X) := {p | dist p.1 p.2 ≤ ε / 2}
  have hK : IsCompact K :=
    (isClosed_le (continuous_fst.dist continuous_snd) continuous_const).isCompact
  let core : K → {p : X × X | dist p.1 p.2 < ε} := fun p ↦
    ⟨p.val, lt_of_le_of_lt p.property (half_lt_self hε)⟩
  have hcore : Continuous core := continuous_subtype_val.subtype_mk _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have huc : UniformContinuous (f ∘ core) :=
    CompactSpace.uniformContinuous_of_continuous (hf.comp hcore)
  obtain ⟨d, hd, hdmod⟩ := Metric.uniformContinuous_iff.mp huc e he
  refine ⟨min (d / 2) (ε / 4), lt_min (half_pos hd) (by linarith),
    (min_le_right _ _).trans_lt (by linarith), ?_⟩
  intro p q hp hq hpq
  apply hdmod (a := ⟨p.1, hp⟩) (b := ⟨q.1, hq⟩)
  exact hpq.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hd))


end HolomorphicAnosov
