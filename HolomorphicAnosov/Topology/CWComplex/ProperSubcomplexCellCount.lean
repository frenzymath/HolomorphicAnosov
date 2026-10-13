import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

namespace HolomorphicAnosov

/-- Deleting any cell from a finite CW complex strictly decreases its
number of cells. Source: Hatcher Theorem 4.8, p.349, termination of successive
highest-cell removal. The cell-index inclusion is injective, and the
omitted cell is outside its range. Finite pigeonhole then gives strict
inequality of the total cell counts, not just a dimension decrease. -/
theorem cw_subcomplex_cell_count_lt_of_omitted
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (W : Topology.CWComplex.Subcomplex C)
    (k : ℕ) (i : Topology.RelCWComplex.cell C k) (hi : i ∉ W.I k) :
    Nat.card (Σ n, W.I n) < Nat.card (Σ n, Topology.RelCWComplex.cell C n) := by
  classical
  let := Topology.CWComplex.finite_cells_of_finite (C := C)
  let inc : (Σ n, W.I n) → (Σ n, Topology.RelCWComplex.cell C n) :=
    fun a ↦ ⟨a.1, a.2.val⟩
  have hinj : Function.Injective inc :=
    Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective)
  let : Finite (Σ n, W.I n) := Finite.of_injective inc hinj
  let := Fintype.ofFinite (Σ n, W.I n)
  let := Fintype.ofFinite (Σ n, Topology.RelCWComplex.cell C n)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_of_notMem inc hinj (b := ⟨k, i⟩)
  rintro ⟨⟨n, j⟩, he⟩
  have hn : n = k := congrArg Sigma.fst he
  subst n
  have hj : j.val = i := Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq
  exact hi (hj ▸ j.property)

end HolomorphicAnosov
