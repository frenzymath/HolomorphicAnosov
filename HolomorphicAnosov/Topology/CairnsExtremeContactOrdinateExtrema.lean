import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric

namespace HolomorphicAnosov

/--
An embedded parametrized circle has points attaining the maximum and minimum of
its imaginary coordinate.  This is the compactness part of Cairns's extreme
contact construction; the strict inequality of the extrema and the polygonal
notch construction are separate obligations.

Source: Cairns, *An Elementary Proof of the Jordan--Schoenflies Theorem*
(1951), §5, printed p.866.  The compactness/extremum extraction is a direct
Mathlib argument.
DAG node: `topo.cairns_extreme_contact_ordinate_extrema_g12`.
-/
theorem cairns_extreme_contact_ordinate_extrema
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ Set.range γ ∧ P₂ ∈ Set.range γ ∧
      (∀ z ∈ Set.range γ, z.im ≤ P₁.im) ∧
      (∀ z ∈ Set.range γ, P₂.im ≤ z.im) := by
  have hcompact : IsCompact (Set.range γ) := isCompact_range hγ.continuous
  have hnonempty : (Set.range γ).Nonempty := Set.range_nonempty γ
  obtain ⟨P₁, hP₁, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty Complex.continuous_im.continuousOn
  obtain ⟨P₂, hP₂, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty Complex.continuous_im.continuousOn
  refine ⟨P₁, P₂, hP₁, hP₂, ?_, ?_⟩
  · exact isMaxOn_iff.mp hmax
  · exact isMinOn_iff.mp hmin

end HolomorphicAnosov
