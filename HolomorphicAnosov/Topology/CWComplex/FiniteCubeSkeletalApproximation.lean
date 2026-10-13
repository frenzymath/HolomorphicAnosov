import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.TopCellElimination
import HolomorphicAnosov.Topology.CWComplex.SubcomplexSkeleton
import Mathlib.Data.Finset.Max

namespace HolomorphicAnosov

open HatcherAttachedCell

/-- A cube map into a finite CW complex can be homotoped into the skeleton
of its own dimension, relative to any source subset already mapping there.
Source: Hatcher Theorem 4.8, pp.349–351. Induct on the finite number of target
cells. If every cell has dimension at most the cube dimension, every point is
already in that skeleton. Otherwise select a cell of maximal dimension and
eliminate it by the missed-point and radial attachment deformations. The complement
is a subcomplex with strictly fewer cells. The prescribed fixed subset misses
the removed cell, so the first homotopy fixes it. Its image still belongs to
the new skeleton, because a subcomplex skeleton is the intersection with the
old skeleton. Recurse and concatenate; no uniform bound on source-cell
homotopies is involved. The local missed-point theorem uses Bredon relative smoothing and locally stationary chart extension.
-/
theorem finite_cw_cube_skeletal_approximation
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (n : ℕ) (A : Set (Cube n)) (f : C(Cube n, Y))
    (hf : Set.range f ⊆ C)
    (hA : Set.MapsTo f A (Topology.CWComplex.skeleton C (n : ℕ∞) : Set Y)) :
    ∃ g : C(Cube n, Y),
      Set.range g ⊆ (Topology.CWComplex.skeleton C (n : ℕ∞) : Set Y) ∧
      Nonempty (ContinuousMap.HomotopyRel f g A) := by
  classical
  by_cases hdim : ∀ (m : ℕ), Topology.RelCWComplex.cell C m → m ≤ n
  · refine ⟨f, ?_, ⟨ContinuousMap.HomotopyRel.refl f A⟩⟩
    rintro y ⟨x, rfl⟩
    have hx := hf ⟨x, rfl⟩
    rw [← Topology.CWComplex.iUnion_openCell_eq_complex (C := C)] at hx
    obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    exact Topology.CWComplex.mem_skeleton_iff.mpr
      ⟨m, by exact_mod_cast hdim m j, j, hx⟩
  push Not at hdim
  obtain ⟨m, j, hm⟩ := hdim
  let := Topology.CWComplex.finite_cells_of_finite (C := C)
  let := Fintype.ofFinite (Σ m, Topology.RelCWComplex.cell C m)
  obtain ⟨⟨k, i⟩, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Σ m, Topology.RelCWComplex.cell C m)) Sigma.fst
    ⟨⟨m, j⟩, Finset.mem_univ _⟩
  have htop (l : ℕ) (a : Topology.RelCWComplex.cell C l) : l ≤ k :=
    hmax ⟨l, a⟩ (Finset.mem_univ _)
  have hnk : n < k := hm.trans_le (htop m j)
  obtain ⟨W, q, hW, hcard, hq, ⟨H⟩⟩ := cw_top_cell_elimination C i htop hnk f hf
  have hAW : A ⊆ f ⁻¹' (W : Set Y) := by
    intro x hx
    rw [Set.mem_preimage, hW]
    refine ⟨hf ⟨x, rfl⟩, ?_⟩
    exact Set.disjoint_left.mp
      (Topology.CWComplex.disjoint_skeleton_openCell
        (C := C) (j := i) (by exact_mod_cast hnk)) (hA hx)
  let H' : ContinuousMap.HomotopyRel f q A := {
    toHomotopy := H.toHomotopy
    prop' := fun t x hx ↦ H.eq_fst t (hAW hx) }
  have hqA : Set.MapsTo q A
      (Topology.CWComplex.skeleton (W : Set Y) (n : ℕ∞) : Set Y) := by
    intro x hx
    rw [cw_subcomplex_skeleton]
    exact ⟨hq ⟨x, rfl⟩, by rw [← H'.fst_eq_snd hx]; exact hA hx⟩
  obtain ⟨g, hg, ⟨G⟩⟩ := finite_cw_cube_skeletal_approximation
    (W : Set Y) n A q hq hqA
  refine ⟨g, ?_, ⟨H'.trans G⟩⟩
  rw [cw_subcomplex_skeleton] at hg
  exact fun x hx ↦ (hg hx).2
termination_by Nat.card (Σ m, Topology.RelCWComplex.cell C m)
decreasing_by exact hcard

end HolomorphicAnosov
