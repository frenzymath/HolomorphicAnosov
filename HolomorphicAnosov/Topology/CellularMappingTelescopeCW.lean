import HolomorphicAnosov.Topology.CellularMappingTelescopeCWCore
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeConnected

/-!
# The CW structure on a cellular mapping telescope

Source: Fritsch–Piccinini, Cellular Structures in Topology, Theorem 2.3.1,
pp.62–63, applied to the endpoint cellular adjunction; Hatcher, §3.F p.312
and Proposition A.11 p.528. The underlying telescope is the existing concrete
endpoint-generated quotient with its original quotient topology.
-/

namespace HolomorphicAnosov

open MappingTelescope.Sequence

/-- The original cellular mapping telescope is Hausdorff, has its level/prism
CW structure, and is connected and nonempty when every layer is.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Theorem 2.3.1,
pp.62–63; Hatcher, *Algebraic Topology*, §3.F p.312 and A.11 p.528.

Proof: `cellular_telescope_hausdorff` applies the closed endpoint-adjunction
separation theorem to the original quotient. The core construction builds the
characteristic maps, finite lower-frontier witnesses, cell partition, and
weak topology on this very quotient, with the exact level and prism labels.
Its full proof is recorded at `cellular_mapping_telescope_cw_core`. For
connectedness, every nonempty connected layer gives a connected cylinder
image; neighboring images meet along their seam. Finite initial unions are
connected and their increasing union is the telescope. The zero-level image
supplies nonemptiness. Combine these three conclusions. No local finiteness,
finite dimension, regular-cell condition, or bond injectivity is assumed.
-/
theorem cellular_mapping_telescope_cw_structure
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1)))
    (hc : ∀ n d : ℕ, Set.MapsTo (c n)
      (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d : Set (X n))
      (Topology.CWComplex.skeleton (Set.univ : Set (X (n + 1))) d : Set (X (n + 1)))) :
    T2Space (telescope c) ∧
    (∃ cw : Topology.CWComplex (Set.univ : Set (telescope c)),
      letI : Topology.CWComplex (Set.univ : Set (telescope c)) := cw
      ∃ labels : ∀ d : ℕ,
        Topology.CWComplex.cell (Set.univ : Set (telescope c)) d ≃
          ((Σ n, Topology.CWComplex.cell (Set.univ : Set (X n)) d) ⊕
            (Σ m : {m : ℕ // m + 1 = d},
              Σ n, Topology.CWComplex.cell (Set.univ : Set (X n)) m.val)),
        (∀ (d n : ℕ) (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d),
          Topology.CWComplex.openCell (C := (Set.univ : Set (telescope c))) d ((labels d).symm (Sum.inl ⟨n, e⟩)) =
            level c n '' Topology.CWComplex.openCell (C := (Set.univ : Set (X n))) d e) ∧
        (∀ (m d : ℕ) (h : m + 1 = d) (n : ℕ)
            (e : Topology.CWComplex.cell (Set.univ : Set (X n)) m),
          Topology.CWComplex.openCell (C := (Set.univ : Set (telescope c))) d ((labels d).symm (Sum.inr ⟨⟨m, h⟩, n, e⟩)) =
            cylinder c n ''
              ((Topology.CWComplex.openCell (C := (Set.univ : Set (X n))) m e).prod
                {t : unitInterval | (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1}))) ∧
    ((∀ n, Nonempty (X n) ∧ ConnectedSpace (X n)) →
      Nonempty (telescope c) ∧ ConnectedSpace (telescope c)) := by
  refine ⟨cellular_telescope_hausdorff c, ?_, cellular_telescope_connected_of_layers c⟩
  exact cellular_mapping_telescope_cw_core c hc

end HolomorphicAnosov
