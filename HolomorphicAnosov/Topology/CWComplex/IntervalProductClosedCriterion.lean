import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.Order

namespace HolomorphicAnosov.Topology
open Set _root_.Topology

/-- The ordinary product of a Hausdorff CW complex with the unit interval
has the closed-set criterion given by the original closed-cell products.

Source context: Hatcher, *Algebraic Topology*, Appendix A.6 p.524 and the
compact-open continuity argument of A.14–A.17 pp.530–533. This explicit
closed-set formulation is deduced from the existing characteristic-prism
continuity theorem. Apply that theorem to the characteristic predicate of
the complement, viewed as a map to the Sierpinski space of propositions.
Each characteristic prism lands in its original closed-cell product, so the
closed-intersection hypothesis makes the complementary predicate continuous
on the prism. Global continuity says precisely that the complement is open.
No product CW structure, local finiteness, or regularity is assumed. -/
theorem cw_interval_product_closed_of_closed_cells
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] (F : Set (X × unitInterval))
    (hF : ∀ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n),
      IsClosed (F ∩ (CWComplex.closedCell (C := univ) n i).prod univ)) :
    IsClosed F := by
  let H : unitInterval × X → Prop := fun p ↦ (p.2, p.1) ∉ F
  have hH : Continuous H := by
    apply HolomorphicAnosov.cw_prism_continuous_of_characteristic
    intro n i
    apply continuous_Prop.mpr
    let g : unitInterval × Metric.closedBall (0 : Fin n → ℝ) 1 → X × unitInterval :=
      fun p ↦ (RelCWComplex.map n i p.2.val, p.1)
    have hg : Continuous g :=
      (((RelCWComplex.continuousOn n i).domRestrict).comp continuous_snd).prodMk
        continuous_fst
    have heq : g ⁻¹' (F ∩ (CWComplex.closedCell (C := univ) n i).prod univ) =
        g ⁻¹' F := by
      ext p
      constructor
      · exact fun hp ↦ hp.1
      · exact fun hp ↦ ⟨hp, ⟨⟨p.2.val, p.2.property, rfl⟩, mem_univ _⟩⟩
    have hc := (hF n i).preimage hg
    rw [heq] at hc
    exact hc.isOpen_compl
  have hc : Continuous (fun p : X × unitInterval ↦ p ∉ F) :=
    hH.comp continuous_swap
  have hopen : IsOpen Fᶜ := continuous_Prop.mp hc
  exact isOpen_compl_iff.mp hopen

end HolomorphicAnosov.Topology
