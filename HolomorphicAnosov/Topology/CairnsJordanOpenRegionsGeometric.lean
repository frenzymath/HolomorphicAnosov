import HolomorphicAnosov.Topology.CairnsExtremeContactPolygon
import HolomorphicAnosov.Topology.CairnsJordanCrosscutRecombination
import HolomorphicAnosov.Topology.CairnsRoundDiskCrosscutSeparation
import HolomorphicAnosov.Topology.ConnectedClosureAttachment
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric

namespace HolomorphicAnosov

/--
Named deferred geometric construction for Cairns's Jordan open-region theorem.

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§5, pp.866–867, using the extreme-contact polygon, two round-disk crosscut
applications, and the final recombination of the three bounded cells.  The
construction supplies the bounded and unbounded open regions, their common
frontier, and the exact complement decomposition.  Its proof is retained as a
named theorem so the source obligation is explicit and independently reusable.
DAG node: topo.cairns_jordan_open_regions_geometric_g20.
-/
theorem cairns_jordan_open_regions_geometric
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) :
    ∃ Q E : Set ℂ,
      Q.Nonempty ∧ E.Nonempty ∧
      IsConnected Q ∧ IsConnected E ∧ IsOpen Q ∧ IsOpen E ∧
      Bornology.IsBounded Q ∧ ¬ Bornology.IsBounded E ∧
      Q ∪ E = (Set.range γ)ᶜ ∧ Disjoint Q E ∧
      frontier Q = Set.range γ ∧ frontier E = Set.range γ := by
  obtain ⟨n, p, P₁, P₂, hp, hP₁, hP₂, hP₁₂, hP₁max, hP₂min, htail⟩ :=
    cairns_extreme_contact_polygon γ hγ
  have hB := htail.1
  have hcontact := htail.2
  exact cairns_jordan_crosscut_recombination γ hγ p P₁ P₂ hp hP₁ hP₂ hP₁₂
    hB hcontact

end HolomorphicAnosov
