import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Finiteness and eventual emptiness of face-indexed cells in a finite geometric
simplicial complex. Source: Hatcher, *Algebraic Topology*, §2.1 pp.103–104. -/

namespace HolomorphicAnosov
open Set

/-- Face-indexed simplicial cell types are finite in every degree and eventually empty.

The only input is finiteness of the face family. A degree-d cell is a subtype of
that finite family, and the image of face cardinality is bounded in `ℕ`; a face of
cardinality `d+1` cannot exist once `d` reaches that bound. The empty complex and
degree zero are included. -/
theorem finite_geometric_cell_index_properties (N : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (hP : P.faces.Finite) :
    (∀ d : ℕ, Finite {s : Finset (EuclideanSpace ℝ (Fin N)) //
      s ∈ P.faces ∧ s.card = d + 1}) ∧
    (∀ᶠ d in Filter.atTop, (IsEmpty {s : Finset (EuclideanSpace ℝ (Fin N)) //
      s ∈ P.faces ∧ s.card = d + 1})) := by
  constructor
  · intro d
    exact hP.subset (fun _ hs ↦ hs.1)
  · obtain ⟨M, hM⟩ := (hP.image Finset.card).bddAbove
    apply Filter.eventually_atTop.mpr
    refine ⟨M, fun d hd ↦ ⟨fun s ↦ ?_⟩⟩
    have hc : s.1.card ≤ M := hM ⟨s.1, s.2.1, rfl⟩
    have hs := s.2.2
    omega

end HolomorphicAnosov
