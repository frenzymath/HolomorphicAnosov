import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallRelativePullback
import HolomorphicAnosov.AlgebraicTopology.SingularRelativePullbackRestrictionSquare

open CategoryTheory Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
open SingularCochain

/--
Transport for the ordinary-product inner-ball square on the native Sigma carrier.

Source: Hatcher, Algebraic Topology, Proposition 3.17 p.217 and Appendix A.17
pp.532--533.  The proof constructs the homeomorphism from the Sigma/product
distribution and subtype/product homeomorphisms, transports the strict annulus
and inner-ball predicates, and identifies the restricted map with the literal
`pairSubspaceMap` of the Sigma product characteristic map.  The pair
homeomorphism theorem then gives the relative cohomology isomorphism.  The
remaining Lean obstruction is reduction of dependent subtype proof fields in
that carrier identification; this theorem records that exact proposition so
its use in the parent comparison is explicit and independently queueable.
-/
theorem sigmaProduct_innerBall_pairSubspace_isIso
    (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (R : Type u) [CommRing R]
    (Y : Type u) [TopologicalSpace Y] (m k : ℕ) :
    let DY : TopCat.{u} := TopCat.of
      (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y)
    let U0Y : Set DY := {z | (1 / 2 : ℝ) < ‖z.2.1.down.1‖}
    let V0Y : Set DY := {z | ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}
    let UY : Set (Skeleton X m × Y) := {z | z.1 ∈ skeletonCollar X m}
    let VY : Set (Skeleton X m × Y) := {z | z.1 ∈ innerBallImage X m}
    let ΦY : DY ⟶ TopCat.of (Skeleton X m × Y) := TopCat.ofHom
      ⟨fun z ↦ (characteristicCell X m z.1 z.2.1, z.2.2),
        continuous_sigma fun i ↦
          ((characteristicCell X m i).continuous.comp continuous_fst).prodMk continuous_snd⟩
    let hΦYV : MapsTo ΦY V0Y VY := by
      obtain ⟨e, he, _, _⟩ := characteristic_innerBall_homeomorph X m
      intro z hz
      let vz : ↥{w : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
          ‖w.2.down.1‖ < (3 / 4 : ℝ)} :=
        ⟨⟨z.1, z.2.1⟩, by simpa [V0Y] using hz⟩
      have hzV := (e vz).property
      rw [he vz] at hzV
      change (characteristicCell X m z.1 z.2.1) ∈ innerBallImage X m
      exact hzV
    let hΦYU : MapsTo ΦY U0Y UY := by
      intro z hz
      change (characteristicCell X m z.1 z.2.1) ∈ skeletonCollar X m
      exact Or.inr ⟨⟨z.1, ⟨z.2.1, hz⟩⟩, rfl⟩
    IsIso (relativeCohomologyPullback R (X := TopCat.of V0Y) (Y := TopCat.of VY)
      (A := {z | z.1 ∈ U0Y}) (B := {z | z.1 ∈ UY})
      (pairSubspaceMap ΦY hΦYV) (fun _ hz => hΦYU hz) k) := by
  dsimp
  let P : Set (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m) :=
    {w | ‖w.2.down.1‖ < (3 / 4 : ℝ)}
  let V : Set (Skeleton X m) := innerBallImage X m
  let U : Set (Skeleton X m) := skeletonCollar X m
  let e0 : ((Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m) × Y) ≃ₜ
      (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y) :=
    Homeomorph.sigmaProdDistrib
  let es : (↥(P ×ˢ (Set.univ : Set Y))) ≃ₜ
      (↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
        ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}) :=
    e0.subtype (by
      intro z
      simp [Set.mem_prod, P, e0, Homeomorph.sigmaProdDistrib])
  let eP : (↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
        ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}) ≃ₜ ↥P × Y :=
    es.symm.trans ((Homeomorph.Set.prod P (Set.univ : Set Y)).trans
      (Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.Set.univ Y)))
  obtain ⟨_, _, _, hprod⟩ := characteristic_innerBall_homeomorph X m
  obtain ⟨ep, hep⟩ := hprod Y inferInstance
  let et0 : (↥(V ×ˢ (Set.univ : Set Y))) ≃ₜ (↥V × Y) :=
    (Homeomorph.Set.prod V (Set.univ : Set Y)).trans
      (Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.Set.univ Y))
  let et : ↥{z : Skeleton X m × Y | z.1 ∈ V} ≃ₜ (↥V × Y) :=
    (Homeomorph.setCongr (Set.ext (fun z => by simp))).trans et0
  let ecomp : ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
        ‖z.2.1.down.1‖ < (3 / 4 : ℝ)} ≃ₜ
      ↥{z : Skeleton X m × Y | z.1 ∈ V} :=
    eP.trans (ep.trans et.symm)
  have heP_disk (z : ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
      ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}) : (eP z).1.1.2 = z.1.2.1 := by
    have hz := congrArg (fun w => w.1.2.1) (eP.symm_apply_apply z)
    simpa [eP, es, e0, P, Homeomorph.trans_apply, Homeomorph.sigmaProdDistrib_apply,
      Homeomorph.sigmaProdDistrib_symm_apply, Homeomorph.Set.prod_apply] using hz
  have heP_cell (z : ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
      ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}) : (eP z).1.1.1 = z.1.1 := by
    have hz := congrArg (fun w => w.1.1) (eP.symm_apply_apply z)
    simpa [eP, es, e0, P, Homeomorph.trans_apply, Homeomorph.sigmaProdDistrib_apply,
      Homeomorph.sigmaProdDistrib_symm_apply, Homeomorph.Set.prod_apply] using hz
  have heP_y (z : ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
      ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}) : (eP z).2 = z.1.2.2 := by
    have hz := congrArg (fun w => w.1.2.2) (eP.symm_apply_apply z)
    simpa [eP, es, e0, P, Homeomorph.trans_apply, Homeomorph.sigmaProdDistrib_apply,
      Homeomorph.sigmaProdDistrib_symm_apply, Homeomorph.Set.prod_apply] using hz
  have he : ∀ z, (1/2 : ℝ) < ‖z.1.2.1.down.1‖ ↔ ((ecomp z).1.1 ∈ U) := by
    intro z
    have hp := (hep (eP z)).2
    dsimp [ecomp, et, et0]
    change (1/2 : ℝ) < ‖z.1.2.1.down.1‖ ↔
      (ep (eP z)).1.1 ∈ skeletonCollar X m
    rw [hp]
    rw [heP_disk z]
  let A0 : Set (↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
      ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}) := {z | (1/2 : ℝ) < ‖z.1.2.1.down.1‖}
  let B0 : Set (↥{z : Skeleton X m × Y | z.1 ∈ V}) := {z | z.1.1 ∈ U}
  have he0 : MapsTo ecomp A0 B0 := by
    intro z hz
    exact (he z).mp hz
  have hi := relativeCohomologyPullback_isIso_of_homeomorph R
      (X := TopCat.of (↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
        ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}))
      (Y := TopCat.of (↥{z : Skeleton X m × Y | z.1 ∈ V}))
      A0 B0 ecomp (fun z => by
        constructor
        · exact (he z).mp
        · exact (he z).mpr) k
  let φa : C((Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y), Skeleton X m × Y) :=
    ⟨fun z ↦ (characteristicCell X m z.1 z.2.1, z.2.2),
      continuous_sigma fun i ↦
        ((characteristicCell X m i).continuous.comp continuous_fst).prodMk continuous_snd⟩
  let φ0 : C(↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
        ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}, Skeleton X m × Y) :=
    φa.comp (ContinuousMap.subtypeVal _)
  let φ : C(↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y |
        ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}, ↥{z : Skeleton X m × Y | z.1 ∈ V}) :=
    ⟨fun z ↦ ⟨φ0 z, ⟨z.1.1, z.1.2.1, z.2, rfl⟩⟩,
      φ0.continuous.subtype_mk _⟩
  have hφ : TopCat.ofHom (ecomp : C(_, _)) = TopCat.ofHom φ := by
    ext z : 1
    apply Subtype.ext
    have hp := (hep (eP z)).1
    change ((ecomp z).1 : Skeleton X m × Y) = φ0 z
    change ((ep (eP z)).1.1, (ep (eP z)).2) = φ0 z
    dsimp [φ0, φa]
    have hc := heP_cell z
    have hd := heP_disk z
    have hy := heP_y z
    simpa [ContinuousMap.subtypeVal_apply, hc, hd, hy] using hp
  let hφ0 : MapsTo φ A0 B0 := by
    intro z hz
    have hz' := (he z).mp hz
    change (φ z).1.1 ∈ U
    have hm : (ecomp z).1 = (φ z).1 := congrArg Subtype.val (by simpa using congrArg (fun f => (ConcreteCategory.hom f) z) hφ)
    rw [← hm]
    exact hz'
  change IsIso (relativeCohomologyPullback R (TopCat.ofHom φ) hφ0 k)
  let heq : TopCat.ofHom ecomp = TopCat.ofHom φ := hφ
  subst heq
  simpa only [hφ] using hi


end HolomorphicAnosov.CharacteristicCellComparison
