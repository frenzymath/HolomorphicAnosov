import HolomorphicAnosov.Topology.Cubical.RationalSingularHomologyInclusion
import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision
import HolomorphicAnosov.Topology.Cubical.CWHighDegreeHomologyG15
import HolomorphicAnosov.Topology.Cubical.SubcomplexCWStructureG15

/-! High-degree rational singular homology vanishing for the original finite cubical
subcomplex carrier. Source: Hatcher, Algebraic Topology, Lemma 2.34(b), pp.137–138.
Select the original cells in their finite CW structure, transport it to the literal
carrier, and apply the finite CW bound proved using characteristic disk pairs. -/
noncomputable section
open CategoryTheory
namespace HolomorphicAnosov.Cubical

/-- Rational singular homology of a finite cubical subcomplex is subsingleton
above the ambient subdivision dimension. -/
theorem cubical_subcomplex_high_degree_homology_subsingleton
    {N : ℕ} (K : FiniteRectilinearSubdivision N)
    (M : CubicalSubcomplex K) (k : ℕ) (hk : N < k) :
    Subsingleton (rationalSingularHomology M.carrier k) := by
  /- Hatcher Lemma 2.34(b): the finite cellular chain complex has no cells
     above dimension N, so its singular homology vanishes in those degrees. -/
  classical
  by_cases hM : M.carrier = ∅
  · have : IsEmpty M.carrier := ⟨fun x ↦ by simpa [hM] using x.property⟩
    exact ModuleCat.subsingleton_of_isZero
      (singular_homology_isZero_of_isEmpty (TopCat.of M.carrier) (ModuleCat.of ℚ ℚ) k)
  obtain ⟨cw, hfinite, hdim, _⟩ := cubical_subcomplex_cw_structure K M
  let := cw
  let := hfinite
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hM
  let c0 : M.carrier := ⟨x, hx⟩
  let := cwCarrierStructureG6 M.carrier c0
  let := cwCarrier_finite M.carrier c0
  exact ModuleCat.subsingleton_of_isZero
    (CharacteristicCellComparison.finiteCW_high_degree M.carrier N k hdim hk)

end HolomorphicAnosov.Cubical

