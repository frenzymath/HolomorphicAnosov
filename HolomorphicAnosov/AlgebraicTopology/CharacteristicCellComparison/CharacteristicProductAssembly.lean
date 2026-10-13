import HolomorphicAnosov.AlgebraicTopology.SingularCohomologyProductDeformationRetraction
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceCollarDeformationLaws
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceCollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceBoundaryRetraction
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceInnerBallExcision
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarStrongDeformationRetraction
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.IsOpenSkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallGeometry
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallRelativePullback
import HolomorphicAnosov.AlgebraicTopology.SingularRelativePullbackRestrictionSquare
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyComparison
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyExcision
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCellComparison.SigmaProductInnerBallTransport

open CategoryTheory CategoryTheory.Limits Opposite Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
open SingularCochain
set_option backward.isDefEq.respectTransparency false

/-- Composition bridge for the explicit quotient maps used by relative pullback
assembly.  The transparency setting is needed because `relativeComplex` is an
abbreviation of a kernel while the quotient map exposes its homology iso. -/
theorem quotientMap_comp_bridge (R : Type u) [CommRing R]
    {Q Q' Q'' : CochainComplex (ModuleCat.{u} R) ℕ}
    (a : Q ⟶ Q') (b : Q' ⟶ Q'') (n : ℕ) :
    quotientMap R (a ≫ b) n = quotientMap R a n ≫ quotientMap R b n := by
  dsimp [quotientMap]
  rw [HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/--
Source: Hatcher, Algebraic Topology, Proposition 3.17 p.217 and Appendix A.17
pp.532--533.  This child isolates the final ordinary-product assembly after
inner-ball transport, product excision, and the source/target collar
retractions have been established.  The intended proof composes the two
relative excision squares, the restriction square, and the product collar
homotopy isomorphisms, then applies the five-lemma comparison and finite
sum restriction.  The remaining Lean obstruction is the naturality equality
between the raw-target `pairSubspaceMap` square and its dependent subtype
restriction maps; this theorem records that exact proposition as a named
DAG node rather than leaving an anonymous parent gap.
-/
theorem characteristic_product_relative_pullback_core
    (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (R : Type u) [CommRing R]
    (Y : Type u) [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
    [CWComplex.Finite (univ : Set Y)] (m k : ℕ) :
    let DY : TopCat.{u} := TopCat.of
      (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y)
    let SY : Set DY := {z | z.2.1 ∈ cellBoundary m}
    let ΦY : DY ⟶ TopCat.of (Skeleton X m × Y) := TopCat.ofHom
      ⟨fun z ↦ (characteristicCell X m z.1 z.2.1, z.2.2),
        continuous_sigma fun i ↦
          ((characteristicCell X m i).continuous.comp continuous_fst).prodMk continuous_snd⟩
    let hΦY : MapsTo ΦY SY {z : Skeleton X m × Y | z.1 ∈ lowerSkeleton X m} := by
      intro z hz
      exact characteristicCell_mapsTo X m z.1 hz
    Function.Bijective (relativeCohomologyPullback R ΦY hΦY k) := by
  classical
  dsimp
  let DY : TopCat.{u} := TopCat.of
    (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y)
  let SY : Set DY := {z | z.2.1 ∈ cellBoundary m}
  let ΦY : DY ⟶ TopCat.of (Skeleton X m × Y) := TopCat.ofHom
    ⟨fun z ↦ (characteristicCell X m z.1 z.2.1, z.2.2),
      continuous_sigma fun i ↦
        ((characteristicCell X m i).continuous.comp continuous_fst).prodMk continuous_snd⟩
  let hΦY : MapsTo ΦY SY
      {z : Skeleton X m × Y | z.1 ∈ lowerSkeleton X m} := by
    intro z hz
    exact characteristicCell_mapsTo X m z.1 hz
  change Function.Bijective (relativeCohomologyPullback R ΦY hΦY k)
  let U0Y : Set DY := {z | (1 / 2 : ℝ) < ‖z.2.1.down.1‖}
  let V0Y : Set DY := {z | ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}
  let UY : Set (Skeleton X m × Y) :=
    {z | z.1 ∈ skeletonCollar X m}
  let VY : Set (Skeleton X m × Y) :=
    {z | z.1 ∈ innerBallImage X m}
  have hU0Y : IsOpen U0Y := by
    rw [isOpen_sigma_iff]
    intro i
    change IsOpen {p : CellDisk.{u} m × Y |
      (1 / 2 : ℝ) < ‖p.1.down.1‖}
    exact (isOpen_lt continuous_const
      ((continuous_subtype_val.comp continuous_uliftDown).norm)).preimage continuous_fst
  have hV0Y : IsOpen V0Y := by
    rw [isOpen_sigma_iff]
    intro i
    change IsOpen {p : CellDisk.{u} m × Y |
      ‖p.1.down.1‖ < (3 / 4 : ℝ)}
    exact (isOpen_lt
      ((continuous_subtype_val.comp continuous_uliftDown).norm)
      continuous_const).preimage continuous_fst
  have hUY : IsOpen UY := (isOpen_skeletonCollar X m).preimage continuous_fst
  have hVY : IsOpen VY :=
    (innerBallImage_geometry X m).2.2.1.preimage continuous_fst
  have hcover0Y : interior U0Y ∪ interior V0Y = (Set.univ : Set DY) := by
    rw [hU0Y.interior_eq, hV0Y.interior_eq]
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : (1 / 2 : ℝ) < ‖z.2.1.down.1‖
    · exact Or.inl hz
    · exact Or.inr (by dsimp [V0Y]; linarith)
  have hcoverY : interior UY ∪ interior VY =
      (Set.univ : Set (Skeleton X m × Y)) := by
    rw [hUY.interior_eq, hVY.interior_eq]
    apply Set.eq_univ_of_forall
    intro z
    have hz := Set.mem_univ z.1
    rw [← (innerBallImage_geometry X m).2.2.2] at hz
    exact hz
  have hΦYU : MapsTo ΦY U0Y UY := by
    intro z hz
    change (characteristicCell X m z.1 z.2.1) ∈ skeletonCollar X m
    exact Or.inr ⟨⟨z.1, ⟨z.2.1, hz⟩⟩, rfl⟩
  have hΦYV : MapsTo ΦY V0Y VY := by
    intro z hz
    obtain ⟨e, he, _, _⟩ := characteristic_innerBall_homeomorph X m
    let vz : ↥{w : Σ _i : RelCWComplex.cell (univ : Set X) m,
        CellDisk.{u} m | ‖w.2.down.1‖ < (3 / 4 : ℝ)} :=
      ⟨⟨z.1, z.2.1⟩, by simpa [V0Y] using hz⟩
    have hzV := (e vz).property
    rw [he vz] at hzV
    change (characteristicCell X m z.1 z.2.1) ∈ innerBallImage X m
    exact hzV
  have hsourceNative (n : ℕ) : IsIso (cohomologyPullback R
      (TopCat.ofHom (ContinuousMap.inclusion (show
        ({z : DY | z.2.1 ∈ cellBoundary m} : Set DY) ⊆ U0Y by
          intro z hz
          have hn : ‖z.2.1.down.1‖ = 1 := by
            simpa [cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere,
              dist_zero_right] using hz
          dsimp [U0Y]
          rw [hn]
          norm_num))) n) := by
    let U0 : Set (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m) := {z | (1 / 2 : ℝ) < ‖z.2.down.1‖}
    let S0 : Set (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m) := {z | z.2 ∈ cellBoundary m}
    have hSU : S0 ⊆ U0 := by
      intro z hz
      have hn : ‖z.2.down.1‖ = 1 := by simpa [S0, cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using hz
      dsimp [U0]; rw [hn]; norm_num
    let i : C(↥S0, ↥U0) := ContinuousMap.inclusion hSU
    let r : C(↥U0, ↥S0) := sourceBoundaryRetraction X m
    have hr : TopCat.ofHom i ≫ TopCat.ofHom r = 𝟙 _ := by
      ext a : 1; apply Subtype.ext
      have h := (sourceCollarDeformation_laws X m (i a)).2.2 1 a.2
      exact (sourceCollarDeformation_laws X m (i a)).2.1.symm.trans (congrArg Subtype.val h)
    let H : TopCat.Homotopy (𝟙 _) (TopCat.ofHom r ≫ TopCat.ofHom i) :=
      { toFun := sourceCollarDeformation X m
        continuous_toFun := (sourceCollarDeformation X m).continuous
        map_zero_left := fun z ↦ (sourceCollarDeformation_laws X m z).1
        map_one_left := fun z ↦ Subtype.ext (sourceCollarDeformation_laws X m z).2.1 }
    let e0 : ((Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m) × Y) ≃ₜ
        (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y) := Homeomorph.sigmaProdDistrib
    let eS : (↥(S0 ×ˢ (Set.univ : Set Y))) ≃ₜ ↥SY := e0.subtype (by intro z; simp [Set.mem_prod, S0, SY, e0, Homeomorph.sigmaProdDistrib])
    let eU : (↥(U0 ×ˢ (Set.univ : Set Y))) ≃ₜ ↥U0Y := e0.subtype (by intro z; simp [Set.mem_prod, U0, U0Y, e0, Homeomorph.sigmaProdDistrib])
    let dS : (↥(S0 ×ˢ (Set.univ : Set Y))) ≃ₜ (↥S0 × Y) :=
      (Homeomorph.Set.prod S0 (Set.univ : Set Y)).trans (Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.Set.univ Y))
    let dU : (↥(U0 ×ˢ (Set.univ : Set Y))) ≃ₜ (↥U0 × Y) :=
      (Homeomorph.Set.prod U0 (Set.univ : Set Y)).trans (Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.Set.univ Y))
    let eSc : (↥S0 × Y) ≃ₜ ↥SY := dS.symm.trans eS
    let eUc : (↥U0 × Y) ≃ₜ ↥U0Y := dU.symm.trans eU
    let ip : C(↥S0 × Y, ↥U0 × Y) := i.prodMap (ContinuousMap.id Y)
    let rp : C(↥U0 × Y, ↥S0 × Y) := r.prodMap (ContinuousMap.id Y)
    have hpr : TopCat.ofHom ip ≫ TopCat.ofHom rp = 𝟙 _ := by
      ext z : 1; apply Prod.ext
      · exact congrArg (fun f : TopCat.of ↥S0 ⟶ TopCat.of ↥S0 ↦ f z.1) hr
      · rfl
    let Hp : TopCat.Homotopy (𝟙 (TopCat.of (↥U0 × Y))) (TopCat.ofHom rp ≫ TopCat.ofHom ip) := {
      toFun := fun z ↦ (H (z.1, z.2.1), z.2.2)
      continuous_toFun := (H.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd
      map_zero_left := by intro z; exact Prod.ext (H.map_zero_left z.1) rfl
      map_one_left := by intro z; exact Prod.ext (H.map_one_left z.1) rfl }
    let iY : C(↥SY, ↥U0Y) :=
      { toFun := fun z ↦ eUc (ip (eSc.symm z))
        continuous_toFun := eUc.continuous.comp (ip.continuous.comp eSc.symm.continuous) }
    let rY : C(↥U0Y, ↥SY) :=
      { toFun := fun z ↦ eSc (rp (eUc.symm z))
        continuous_toFun := eSc.continuous.comp (rp.continuous.comp eUc.symm.continuous) }
    have hiY : TopCat.ofHom iY ≫ TopCat.ofHom rY = 𝟙 _ := by
      ext z : 1
      apply Subtype.ext
      have hpr' (x : ↥S0 × Y) : rp (ip x) = x :=
        congrArg (fun f : TopCat.of (↥S0 × Y) ⟶ TopCat.of (↥S0 × Y) ↦ f x) hpr
      simp [iY, rY, eSc, eUc, hpr']
    have hiY_eq : iY = ContinuousMap.inclusion (show SY ⊆ U0Y by
      intro z hz
      dsimp [SY, U0Y] at hz ⊢
      have hn : ‖z.2.1.down.1‖ = 1 := by
        simpa [cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using hz
      rw [hn]
      norm_num) := by
      ext z
      · rfl
      · apply heq_of_eq
        rfl
    let HY : TopCat.Homotopy (𝟙 (TopCat.of ↥U0Y)) (TopCat.ofHom rY ≫ TopCat.ofHom iY) := {
      toFun := fun tz ↦ eUc (Hp (tz.1, eUc.symm tz.2))
      continuous_toFun := eUc.continuous.comp (Hp.continuous.comp
        (continuous_fst.prodMk (eUc.symm.continuous.comp continuous_snd)))
      map_zero_left := by intro z; simp [eUc]
      map_one_left := by intro z; simp [iY, rY, eUc, eSc] }
    have hi : IsIso (cohomologyPullback R (TopCat.ofHom iY) n) :=
      cohomologyPullback_isIso_of_deformationRetraction R (TopCat.ofHom iY) (TopCat.ofHom rY) hiY HY n
    rw [← hiY_eq]
    exact hi
  let r0Y := relativeCohomologyPullback R (X := TopCat.of V0Y) (Y := DY)
    (A := {z | z.1 ∈ U0Y}) (B := U0Y) (subspaceInclusion DY V0Y)
    (fun _ hz ↦ hz) k
  let rZY := relativeCohomologyPullback R (X := TopCat.of VY)
    (Y := TopCat.of (Skeleton X m × Y)) (A := {z | z.1 ∈ UY}) (B := UY)
    (subspaceInclusion (TopCat.of (Skeleton X m × Y)) VY)
    (fun _ hz ↦ hz) k
  let innerY := relativeCohomologyPullback R (X := TopCat.of V0Y)
    (Y := TopCat.of VY) (A := {z | z.1 ∈ U0Y}) (B := {z | z.1 ∈ UY})
    (pairSubspaceMap ΦY hΦYV) (fun _ hz ↦ hΦYU hz) k
  have : IsIso r0Y := relative_cohomology_excision R DY U0Y V0Y hcover0Y k
  have : IsIso rZY := relative_cohomology_excision R
    (TopCat.of (Skeleton X m × Y)) UY VY hcoverY k
  have : IsIso innerY := by
    simpa only [innerY] using
      (sigmaProduct_innerBall_pairSubspace_isIso X R Y m k)
  let largeY := relativeCohomologyPullback R ΦY hΦYU k
  have hsquareY : largeY ≫ r0Y = rZY ≫ innerY :=
    relativeCohomologyPullback_restriction_square R (X := DY)
      (Y := TopCat.of (Skeleton X m × Y)) U0Y V0Y UY VY ΦY hΦYU hΦYV k
  have : IsIso (largeY ≫ r0Y) := by rw [hsquareY]; infer_instance
  have : IsIso largeY := IsIso.of_isIso_comp_right largeY r0Y
  have htargetNative (n : ℕ) : IsIso (cohomologyPullback R
      (TopCat.ofHom (ContinuousMap.inclusion (show
        ({z : Skeleton X m × Y | z.1 ∈ lowerSkeleton X m} : Set _) ⊆ UY by
          intro z hz
          exact Or.inl hz))) n) := by
    let L : Set (Skeleton X m) := lowerSkeleton X m
    let U : Set (Skeleton X m) := skeletonCollar X m
    have hLU : L ⊆ U := by intro z hz; exact Or.inl hz
    let i : C(↥L, ↥U) := ContinuousMap.inclusion hLU
    obtain ⟨hAU', r, hr, ⟨H⟩⟩ := skeletonCollar_strongDeformationRetraction X m
    have hri : TopCat.ofHom i ≫ TopCat.ofHom r = 𝟙 _ := by
      ext a : 1; exact hr a
    let ip : C(↥L × Y, ↥U × Y) := i.prodMap (ContinuousMap.id Y)
    let rp : C(↥U × Y, ↥L × Y) := r.prodMap (ContinuousMap.id Y)
    have hpr : TopCat.ofHom ip ≫ TopCat.ofHom rp = 𝟙 _ := by
      ext z : 1; apply Prod.ext
      · exact congrArg (fun f : TopCat.of ↥L ⟶ TopCat.of ↥L ↦ f z.1) hri
      · rfl
    let Hp : TopCat.Homotopy (𝟙 (TopCat.of (↥U × Y))) (TopCat.ofHom rp ≫ TopCat.ofHom ip) := {
      toFun := fun z ↦ (H.toHomotopy (z.1, z.2.1), z.2.2)
      continuous_toFun := (H.toHomotopy.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd
      map_zero_left := by intro z; exact Prod.ext (H.toHomotopy.map_zero_left z.1) rfl
      map_one_left := by intro z; exact Prod.ext (H.toHomotopy.map_one_left z.1) rfl }
    let PL : Set (Skeleton X m × Y) := {z | z.1 ∈ L}
    let PU : Set (Skeleton X m × Y) := {z | z.1 ∈ U}
    let dL0 : (↥(L ×ˢ (Set.univ : Set Y))) ≃ₜ (↥L × Y) :=
      (Homeomorph.Set.prod L (Set.univ : Set Y)).trans
        (Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.Set.univ Y))
    let dU0 : (↥(U ×ˢ (Set.univ : Set Y))) ≃ₜ (↥U × Y) :=
      (Homeomorph.Set.prod U (Set.univ : Set Y)).trans
        (Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.Set.univ Y))
    let dL : (↥L × Y) ≃ₜ ↥PL := dL0.symm.trans
      (Homeomorph.setCongr (Set.ext (by intro z; simp [PL])))
    let dU : (↥U × Y) ≃ₜ ↥PU := dU0.symm.trans
      (Homeomorph.setCongr (Set.ext (by intro z; simp [PU])))
    let iY : C(↥PL, ↥PU) :=
      { toFun := fun z ↦ dU (ip (dL.symm z))
        continuous_toFun := dU.continuous.comp (ip.continuous.comp dL.symm.continuous) }
    let rY : C(↥PU, ↥PL) :=
      { toFun := fun z ↦ dL (rp (dU.symm z))
        continuous_toFun := dL.continuous.comp (rp.continuous.comp dU.symm.continuous) }
    have hiY : TopCat.ofHom iY ≫ TopCat.ofHom rY = 𝟙 _ := by
      ext z : 1; apply Subtype.ext
      have hpr' (x : ↥L × Y) : rp (ip x) = x := congrArg (fun f : TopCat.of (↥L × Y) ⟶ TopCat.of (↥L × Y) ↦ f x) hpr
      simp [iY, rY, dL, dU, hpr']
    let HY : TopCat.Homotopy (𝟙 (TopCat.of ↥PU)) (TopCat.ofHom rY ≫ TopCat.ofHom iY) := {
      toFun := fun tz ↦ dU (Hp (tz.1, dU.symm tz.2))
      continuous_toFun := dU.continuous.comp (Hp.continuous.comp (continuous_fst.prodMk (dU.symm.continuous.comp continuous_snd)))
      map_zero_left := by intro z; simp [dU]
      map_one_left := by intro z; simp [iY, rY, dU, dL] }
    have hi : IsIso (cohomologyPullback R (TopCat.ofHom iY) n) :=
      cohomologyPullback_isIso_of_deformationRetraction R (TopCat.ofHom iY) (TopCat.ofHom rY) hiY HY n
    have hiEq : iY = ContinuousMap.inclusion (show PL ⊆ PU by
      intro z hz; exact hLU hz) := by
      ext z
      · rfl
      · rfl
    rw [← hiEq]
    exact hi
  have hSUY : SY ⊆ U0Y := by
    intro z hz
    have hn : ‖z.2.1.down.1‖ = 1 := by
      simpa [SY, cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere,
        dist_zero_right] using hz
    dsimp [U0Y]
    rw [hn]
    norm_num
  have hAUY : {z : Skeleton X m × Y | z.1 ∈ lowerSkeleton X m} ⊆ UY := by
    intro z hz
    exact Or.inl hz
  have hSUYMap : MapsTo (𝟙 DY) SY U0Y := fun _ hz ↦ hSUY hz
  have hAUYMap : MapsTo (𝟙 (TopCat.of (Skeleton X m × Y)))
      {z : Skeleton X m × Y | z.1 ∈ lowerSkeleton X m} UY := fun _ hz ↦ hAUY hz
  let iSource := relativeCohomologyPullback R (X := DY) (Y := DY)
    (A := SY) (B := U0Y) (𝟙 DY) hSUYMap k
  let iTarget := relativeCohomologyPullback R
    (X := TopCat.of (Skeleton X m × Y)) (Y := TopCat.of (Skeleton X m × Y))
    (A := {z : Skeleton X m × Y | z.1 ∈ lowerSkeleton X m}) (B := UY)
    (𝟙 _) hAUYMap k
  have hcomp {P Q T : TopCat.{u}} {A : Set P} {B : Set Q} {C : Set T}
      (f : P ⟶ Q) (g : Q ⟶ T) (hf : MapsTo f A B) (hg : MapsTo g B C) :
      relativeCohomologyPullback R (f ≫ g) (hg.comp hf) k =
        relativeCohomologyPullback R g hg k ≫ relativeCohomologyPullback R f hf k := by
    have hc : relativePullback R (f ≫ g) (hg.comp hf) =
        relativePullback R g hg ≫ relativePullback R f hf := by
      apply (cancel_mono (kernel.ι (pullback R (subspaceInclusion P A)))).mp
      dsimp only [relativePullback, kernel.map]
      simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
      change kernel.ι (pullback R (subspaceInclusion T C)) ≫
          (cochainFunctor R).map (f ≫ g).op =
        kernel.ι (pullback R (subspaceInclusion T C)) ≫
          (cochainFunctor R).map g.op ≫ (cochainFunctor R).map f.op
      simp only [op_comp, Functor.map_comp]
    dsimp only [relativeCohomologyPullback]
    rw [hc, quotientMap_comp_bridge]
  have hid (Z : TopCat.{u}) (n : ℕ) :
      Function.Bijective (cohomologyPullback R (𝟙 Z) n) := by
    have he : cohomologyPullback R (𝟙 Z) n = 𝟙 _ := by
      have hp : SingularCochain.pullback R (𝟙 Z) = 𝟙 _ :=
        (cochainFunctor R).map_id (op Z)
      unfold cohomologyPullback
      rw [hp]
      unfold quotientMap
      rw [HomologicalComplex.homologyMap_id]
      let e := (HomologicalComplex.sc (complex R Z) n).moduleCatHomologyIso
      change e.inv ≫ 𝟙 _ ≫ e.hom = 𝟙 _
      simp only [Category.id_comp, Iso.inv_hom_id]
    rw [he]
    exact Function.bijective_id
  have hsourcePair (n : ℕ) :
      IsIso (cohomologyPullback R (pairSubspaceMap (𝟙 DY) hSUYMap) n) := by
    have heq : pairSubspaceMap (𝟙 DY) hSUYMap =
        TopCat.ofHom (ContinuousMap.inclusion hSUY) := by
      ext z : 1
      rfl
    rw [heq]
    exact hsourceNative n
  have htargetPair (n : ℕ) :
      IsIso (cohomologyPullback R (pairSubspaceMap (𝟙 _) hAUYMap) n) := by
    have heq : pairSubspaceMap (𝟙 _) hAUYMap =
        TopCat.ofHom (ContinuousMap.inclusion hAUY) := by
      ext z : 1
      rfl
    rw [heq]
    exact htargetNative n
  have : IsIso iSource := (ConcreteCategory.isIso_iff_bijective iSource).mpr
    (relative_cohomology_pullback_bijective_of_absolute R (𝟙 DY) hSUYMap
      (hid DY) (fun n ↦ (ConcreteCategory.isIso_iff_bijective _).mp
        (hsourcePair n)) k)
  have : IsIso iTarget := (ConcreteCategory.isIso_iff_bijective iTarget).mpr
    (relative_cohomology_pullback_bijective_of_absolute R (𝟙 _) hAUYMap
      (hid _) (fun n ↦ (ConcreteCategory.isIso_iff_bijective _).mp
        (htargetPair n)) k)
  have hcollarsY : largeY ≫ iSource = iTarget ≫
      relativeCohomologyPullback R ΦY hΦY k := by
    dsimp only [largeY, iSource, iTarget]
    rw [← hcomp, ← hcomp]
    congr 1
  have : IsIso (iTarget ≫ relativeCohomologyPullback R ΦY hΦY k) := by
    rw [← hcollarsY]
    infer_instance
  have : IsIso (relativeCohomologyPullback R ΦY hΦY k) :=
    IsIso.of_isIso_comp_left iTarget _
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end HolomorphicAnosov.CharacteristicCellComparison
