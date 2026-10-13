import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Homotopy.Basic

/-!
# Continuity on open CW subcomplex prisms

Source: Hatcher, *Algebraic Topology*, Appendix pp.519–523.
DAG node: `topo.cw_subcomplex_open_prism_continuity_g1`.
-/

namespace HolomorphicAnosov

/-- Continuity on an open subset of a CW subcomplex descends from the original
characteristic prisms, with the ordinary product and ambient subtype topologies.

Source: Hatcher, Algebraic Topology, Appendix, the characteristic weak topology
pp.519–521 and homotopy continuity discussion p.523. This is an agent-written
expansion of the open restriction needed by Proposition A.4, p.522.

Proof. The coproduct of compact characteristic disks maps quotiently onto C:
it is continuous and surjective, and a set with closed preimage intersects each
closed cell in the compact image of a closed disk subset. The CW closed-cell
criterion makes that set closed in C. Restrict this quotient to the open subset
W of C corresponding to V. Its source is homeomorphic to the coproduct of the
restricted disks: the coordinate identification is continuous and open, because
W is open. Each assumed characteristic prism is continuous. Redistribute the
product of the coproduct with the unit interval into a coproduct of products,
and use quotient function descent with the locally compact interval. Finally
the canonical continuous identification of V with W gives continuity on V.
No CW structure on V, compactness of the disk coproduct, local finiteness, or
separation hypothesis on Y is used. The argument includes empty V and C.
-/
theorem cw_subcomplex_open_prism_continuous_of_characteristic
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (C : Set X) [Topology.CWComplex C] (V : Set X) (hVC : V ⊆ C)
    (hV : IsOpen {y : C | y.val ∈ V}) (H : unitInterval × V → Y)
    (hc : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
      Continuous (fun p : unitInterval ×
          {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
            Topology.RelCWComplex.map n i z.val ∈ V} ↦
        H (p.1, ⟨Topology.RelCWComplex.map n i p.2.val.val, p.2.property⟩))) :
    Continuous H := by
  classical
  let J := Σ n : ℕ, Topology.RelCWComplex.cell C n
  let D (j : J) : Type := Metric.closedBall (0 : Fin j.1 → ℝ) 1
  let q : (Σ j : J, D j) → C := fun p ↦
    ⟨Topology.RelCWComplex.map p.1.1 p.1.2 p.2.val,
      Topology.RelCWComplex.closedCell_subset_complex _ _ ⟨p.2.val, p.2.property, rfl⟩⟩
  have hqcont : Continuous q := by
    apply continuous_sigma
    rintro ⟨n, i⟩
    exact (Topology.RelCWComplex.continuousOn n i).domRestrict.subtype_mk _
  have hq : Topology.IsQuotientMap q := by
    apply Topology.isQuotientMap_iff_isClosed.mpr
    constructor
    · intro y
      have hy : y.val ∈ ⋃ n : ℕ, ⋃ i : Topology.RelCWComplex.cell C n,
          Topology.CWComplex.closedCell n i := by
        rw [Topology.CWComplex.union]
        exact y.property
      obtain ⟨n, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨i, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
      exact ⟨⟨⟨n, i⟩, ⟨z, hz⟩⟩, Subtype.ext hzy⟩
    · intro A
      constructor
      · exact fun hA ↦ hA.preimage hqcont
      · intro hA
        have himage : IsClosed (Subtype.val '' A : Set X) := by
          apply (Topology.CWComplex.closed C _
            (by rintro _ ⟨y, _, rfl⟩; exact y.property)).mpr
          intro n i
          let : CompactSpace (D ⟨n, i⟩) :=
            isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
          let χ : D ⟨n, i⟩ → X := fun z ↦ Topology.RelCWComplex.map n i z.val
          have hχ : Continuous χ := (Topology.RelCWComplex.continuousOn n i).domRestrict
          have hpre : IsClosed ((fun z : D ⟨n, i⟩ ↦ q ⟨⟨n, i⟩, z⟩) ⁻¹' A) :=
            hA.preimage (@continuous_sigmaMk J D _ ⟨n, i⟩)
          have heq : (Subtype.val '' A : Set X) ∩ Topology.CWComplex.closedCell n i =
              χ '' ((fun z : D ⟨n, i⟩ ↦ q ⟨⟨n, i⟩, z⟩) ⁻¹' A) := by
            ext y
            constructor
            · rintro ⟨⟨y, hy, rfl⟩, z, hz, hzy⟩
              refine ⟨⟨z, hz⟩, ?_, hzy⟩
              have he : q ⟨⟨n, i⟩, ⟨z, hz⟩⟩ = y := Subtype.ext hzy
              change q ⟨⟨n, i⟩, ⟨z, hz⟩⟩ ∈ A
              rwa [he]
            · rintro ⟨z, hz, rfl⟩
              exact ⟨⟨q ⟨⟨n, i⟩, z⟩, hz, rfl⟩, ⟨z.val, z.property, rfl⟩⟩
          rw [heq]
          exact (hpre.isCompact.image hχ).isClosed
        convert himage.preimage continuous_subtype_val using 1
        exact (Set.preimage_image_eq _ Subtype.val_injective).symm
  let W : Set C := {y | y.val ∈ V}
  let P := q ⁻¹' W
  have hP : IsOpen P := hV.preimage hqcont
  let E (j : J) := {z : D j // q ⟨j, z⟩ ∈ W}
  let e : (Σ j : J, E j) ≃ₜ P := by
    let ee : (Σ j : J, E j) ≃ P :=
      { toFun := fun p ↦ ⟨⟨p.1, p.2.val⟩, p.2.property⟩
        invFun := fun p ↦ ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
        left_inv := fun p ↦ by cases p; rfl
        right_inv := fun p ↦ by cases p; rfl }
    apply ee.toHomeomorphOfContinuousOpen
    · apply continuous_sigma
      intro j
      exact ((@continuous_sigmaMk J D _ j).comp
        (continuous_subtype_val : Continuous (Subtype.val : E j → D j))).subtype_mk _
    · apply isOpenMap_sigma.mpr
      intro j
      have hj : IsOpen {z : D j | q ⟨j, z⟩ ∈ W} := hP.preimage continuous_sigmaMk
      exact ((@isOpenMap_sigmaMk J D _ j).comp hj.isOpenMap_subtype_val).subtype_mk _
  let qW : P → W := W.restrictPreimage q
  have hqW : Topology.IsQuotientMap qW := hq.restrictPreimage_isOpen hV
  let H' : unitInterval × W → Y := fun p ↦ H (p.1, ⟨p.2.val.val, p.2.property⟩)
  have hH' : Continuous H' := by
    apply (hqW.comp e.isQuotientMap).continuous_lift_prod_right
    let F : unitInterval × (Σ j : J, E j) → Y :=
      fun p ↦ H' (p.1, qW (e p.2))
    let G : (Σ j : J, E j × unitInterval) → Y :=
      fun p ↦ F (p.2.2, ⟨p.1, p.2.1⟩)
    have hG : Continuous G := by
      apply continuous_sigma
      rintro ⟨n, i⟩
      exact (hc n i).comp (continuous_snd.prodMk continuous_fst)
    let rearrange : ((Σ j : J, E j) × unitInterval) ≃ₜ
        (Σ j : J, E j × unitInterval) := Homeomorph.sigmaProdDistrib
    have hp : Continuous (fun p : (Σ j : J, E j) × unitInterval ↦ F (p.2, p.1)) := by
      convert hG.comp rearrange.continuous using 1
      funext p
      rfl
    exact hp.comp continuous_swap
  let lift : V → W := fun y ↦ ⟨⟨y.val, hVC y.property⟩, y.property⟩
  have hlift : Continuous lift := (continuous_subtype_val.subtype_mk _).subtype_mk _
  exact hH'.comp (continuous_fst.prodMk (hlift.comp continuous_snd))


end HolomorphicAnosov
