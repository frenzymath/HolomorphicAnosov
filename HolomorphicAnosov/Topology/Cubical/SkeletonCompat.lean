import HolomorphicAnosov.Topology.Cubical.OpenCellPartition
import HolomorphicAnosov.Topology.Cubical.FaceDimension
open Set
namespace HolomorphicAnosov.Cubical
open ClosedCoordinateCell
open scoped ENNReal
open _root_.Topology

/-- The native CW structure of the original subdivision has exactly the literal
cubical skeleta. Source: Hatcher, Algebraic Topology, Appendix A.2, p.521,
and the definition of the CW skeleton. Choose the finite CW structure indexed
by the original cells. Every native open cell of dimension at most q lies in
its original closed carrier, hence in the literal q-skeleton. Conversely, a
point of an original closed cell lies in the relative open box of one of its
faces; that face belongs to the subdivision and has no larger dimension.
The corresponding native open cell therefore places it in the native q-skeleton.
This includes q = 0 and subdivisions in dimension zero. -/
theorem finiteSubdivision_cw_skeleton_compat {N : ℕ} (K : FiniteRectilinearSubdivision N) :
    ∃ cw : CWComplex K.cube.carrier,
      let := cw
      ∀ q : ℕ, (CWComplex.skeleton K.cube.carrier (q : ℕ∞) : Set (Fin N → ℝ)) = K.skeleton q := by
  obtain ⟨cw, hfinite, index, hcells⟩ := finiteSubdivision_cwStructure K
  let := cw
  refine ⟨cw, fun q ↦ ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (CWComplex.skeleton K.cube.carrier (q : ℕ∞) : Set (Fin N → ℝ)) := hx
    obtain ⟨n, hnq, i, hxi⟩ := (CWComplex.mem_skeleton_iff (C := K.cube.carrier) (n := (q : ℕ∞)) (x := x)).mp hx'
    obtain ⟨csub, hi⟩ := (index n).surjective i
    rcases csub with ⟨c, hc, hdim⟩
    rw [← hi] at hxi
    have hbox := (hcells n ⟨c, hc, hdim⟩).2
    rw [hbox] at hxi
    rw [FiniteRectilinearSubdivision.skeleton]
    refine mem_iUnion.mpr ⟨c, ?_⟩
    refine mem_iUnion.mpr ⟨hc, ?_⟩
    exact mem_iUnion.mpr ⟨le_trans (le_of_eq hdim) (by exact_mod_cast hnq), hxi.1⟩
  · intro hx
    rw [FiniteRectilinearSubdivision.skeleton] at hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨c, hc, hdim, hxi⟩ := hx
    obtain ⟨a, haface, hxa⟩ := c.exists_face_mem_openCarrier hxi
    have hadim : a.dimension ≤ q := le_trans (ClosedCoordinateCell.IsFace.dimension_le haface) hdim
    let i : RelCWComplex.cell K.cube.carrier a.dimension :=
      (index a.dimension) ⟨a, K.faces c hc a haface, rfl⟩
    have hbox := (hcells a.dimension ⟨a, K.faces c hc a haface, rfl⟩).2
    have hopen : x ∈ CWComplex.openCell a.dimension i := by
      rw [hbox]
      exact hxa
    exact (CWComplex.mem_skeleton_iff (C := K.cube.carrier) (n := (q : ℕ∞)) (x := x)).mpr
      ⟨a.dimension, by exact_mod_cast hadim, i, hopen⟩
end HolomorphicAnosov.Cubical
