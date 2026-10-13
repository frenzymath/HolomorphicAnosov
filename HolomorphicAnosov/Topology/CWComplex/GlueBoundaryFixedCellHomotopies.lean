import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.BoundaryFixedCharacteristicCompatibility
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity

namespace HolomorphicAnosov

/-- Cell homotopies stationary on a set containing all frontiers glue to
a continuous carrier homotopy, preserving the initial map, the fixed set,
and a prescribed endpoint-image condition. Source: Hatcher Theorem 4.8,
p.349, simultaneous skeletal deformation, with characteristic-product
quotient descent. Boundary-fixed compatibility identifies all equal
characteristic representatives. Apply characteristic-prism gluing, then
represent each carrier point by a characteristic disk point to verify the
initial, fixed-set and endpoint identities. -/
theorem cw_glue_boundary_fixed_cell_homotopies
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (C : Set X) [Topology.CWComplex C] (F S : Set X) (T : Set Y) (q : X → Y)
    (hfront : ∀ m (i : Topology.RelCWComplex.cell C m),
      Topology.CWComplex.cellFrontier m i ⊆ F)
    (P : ∀ m (_ : Topology.RelCWComplex.cell C m),
      C(unitInterval × Metric.closedBall (0 : Fin m → ℝ) 1, Y))
    (hzero : ∀ m i z, P m i (0, z) = q (Topology.RelCWComplex.map m i z.val))
    (hfix : ∀ m i t z, Topology.RelCWComplex.map m i z.val ∈ F →
      P m i (t, z) = q (Topology.RelCWComplex.map m i z.val))
    (hend : ∀ m i z, Topology.RelCWComplex.map m i z.val ∈ S → P m i (1, z) ∈ T) :
    ∃ H : C(unitInterval × C, Y),
      (∀ x : C, H (0, x) = q x.val) ∧
      (∀ t (x : C), x.val ∈ F → H (t, x) = q x.val) ∧
      ∀ x : C, x.val ∈ S → H (1, x) ∈ T := by
  obtain ⟨H, hH⟩ := cw_subtype_glue_characteristic_prisms C P
    (cw_boundary_fixed_characteristic_compatibility C F q hfront P hfix)
  have hall (x : C) : H (0, x) = q x.val ∧
      (∀ t, x.val ∈ F → H (t, x) = q x.val) ∧
      (x.val ∈ S → H (1, x) ∈ T) := by
    have hx : x.val ∈ ⋃ (m : ℕ) (i : Topology.RelCWComplex.cell C m),
        Topology.CWComplex.closedCell m i := by
      simpa only [Topology.CWComplex.union] using x.property
    obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, z, hz, heq⟩ := Set.mem_iUnion.mp hx
    let d : Metric.closedBall (0 : Fin m → ℝ) 1 := ⟨z, hz⟩
    have hd : (⟨Topology.RelCWComplex.map m i d.val,
      Topology.CWComplex.closedCell_subset_complex m i ⟨d.val, d.property, rfl⟩⟩ : C) = x :=
      Subtype.ext heq
    have hval (t : unitInterval) : H (t, x) = P m i (t, d) := by
      rw [← hd]
      exact hH m i t d
    refine ⟨?_, ?_, ?_⟩
    · rw [hval, hzero, heq]
    · intro t hxF
      rw [hval, hfix m i t d (heq.symm ▸ hxF), heq]
    · intro hxS
      rw [hval]
      exact hend m i d (heq.symm ▸ hxS)
  exact ⟨H, fun x ↦ (hall x).1, fun t x hx ↦ (hall x).2.1 t hx,
    fun x hx ↦ (hall x).2.2 hx⟩

end HolomorphicAnosov
