import HolomorphicAnosov.Topology.CWComplex.DiskAdjunction

/-!
# Finite towers of disk attachments

Source: Hatcher, *Algebraic Topology*, Appendix p.519, the inductive
disk-attachment definition specialized to finitely many cells in each of
finitely many dimensions. This is the concrete data of DAG node
`topo.def_finite_cell_attachment_tower_g2`.
-/

noncomputable section

open scoped TopCat

universe u

namespace HolomorphicAnosov.FiniteCellAdjunction

/-- A finite tower starting with a finite discrete space and attaching disks
in successive positive dimensions.

Source: Hatcher, *Algebraic Topology*, Appendix p.519. Its endpoint is indexed
by the actual quotient constructed at the previous step. `points` retains
the given topology, with only finiteness and discreteness certificates.
`attach` supplies arbitrary continuous boundary maps into that endpoint;
the next endpoint is the literal finite disk adjunction. No CW, Hausdorff,
embedding, injectivity, nonemptiness or compactness condition is supplied.
A zero-length tower and empty attachment families are allowed.
-/
inductive Tower : ℕ → TopCat.{u} → Type (u + 1)
  | points (X : TopCat.{u}) (finite : Finite X) (discrete : DiscreteTopology X) : Tower 0 X
  | attach {n : ℕ} {X : TopCat.{u}} (T : Tower n X) (k : ℕ)
      (a : Fin k → C(∂𝔻 (n + 1), X)) :
      Tower (n + 1) (adjunction (n + 1) X k a)

end HolomorphicAnosov.FiniteCellAdjunction
