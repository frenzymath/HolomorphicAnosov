import HolomorphicAnosov.Topology.Cubical.CWHighDegreeHomologyG15
import HolomorphicAnosov.Topology.Cubical.SigmaRelativeHomology

noncomputable section
open CategoryTheory CategoryTheory.Limits Set _root_.Topology
namespace HolomorphicAnosov.CharacteristicCellComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An injective selection of disjoint identical pairs is injective on homology.
If the selected index set is nonempty, retract every unused component onto a
chosen component; this is a continuous retraction of pairs. If it is empty,
its chain complex and hence its homology vanish. -/
theorem sigmaPair_homology_mono {ι κ : Type} (j : ι → κ) (hj : Function.Injective j)
    (Y : TopCat) (A : Set Y) (R : ModuleCat ℚ) (n : ℕ) (hn : 0 < n) :
    let f : TopCat.of (Σ _ : ι, Y) ⟶ TopCat.of (Σ _ : κ, Y) :=
      TopCat.ofHom ⟨fun x ↦ ⟨j x.1, x.2⟩, continuous_sigma fun i ↦
        (show Continuous (@Sigma.mk κ (fun _ ↦ (Y : Type)) (j i)) from continuous_sigmaMk)⟩
    Mono (SSetPair.homologyMap (singularSubspacePairMap f
      {x | x.2 ∈ A} {x | x.2 ∈ A} (fun _ hx ↦ hx)) R n) := by
  classical
  dsimp only
  let f : TopCat.of (Σ _ : ι, Y) ⟶ TopCat.of (Σ _ : κ, Y) :=
    TopCat.ofHom ⟨fun x ↦ ⟨j x.1, x.2⟩, continuous_sigma fun i ↦
        (show Continuous (@Sigma.mk κ (fun _ ↦ (Y : Type)) (j i)) from continuous_sigmaMk)⟩
  let P := singularSubspacePair (TopCat.of (Σ _ : ι, Y)) {x | x.2 ∈ A}
  let Q := singularSubspacePair (TopCat.of (Σ _ : κ, Y)) {x | x.2 ∈ A}
  let F := singularSubspacePairMap f {x | x.2 ∈ A} {x | x.2 ∈ A} (fun _ hx ↦ hx)
  change Mono (SSetPair.homologyMap F R n)
  by_cases hi : Nonempty ι
  · let r : κ → ι := Function.invFun j
    have hr : Function.LeftInverse r j := Function.leftInverse_invFun hj
    let g : TopCat.of (Σ _ : κ, Y) ⟶ TopCat.of (Σ _ : ι, Y) :=
      TopCat.ofHom ⟨fun x ↦ ⟨r x.1, x.2⟩, continuous_sigma fun i ↦
        (show Continuous (@Sigma.mk ι (fun _ ↦ (Y : Type)) (r i)) from continuous_sigmaMk)⟩
    let G := singularSubspacePairMap g {x | x.2 ∈ A} {x | x.2 ∈ A} (fun _ hx ↦ hx)
    have hfg : f ≫ g = 𝟙 _ := by ext x : 1; exact Sigma.ext (hr x.1) HEq.rfl
    have hFG : F ≫ G = 𝟙 P := by
      dsimp only [F, G]
      rw [singularSubspacePairMap_comp]
      simpa only [hfg] using singularSubspacePairMap_id
        (TopCat.of (Σ _ : ι, Y)) {x | x.2 ∈ A} (fun _ hx ↦ hx)
    have he : SSetPair.homologyMap F R n ≫ SSetPair.homologyMap G R n = 𝟙 _ := by
      change (SSetPair.homologyFunctor R n).map F ≫ (SSetPair.homologyFunctor R n).map G = _
      rw [← CategoryTheory.Functor.map_comp, hFG, CategoryTheory.Functor.map_id]
      rfl
    exact mono_of_mono_fac he
  · have : IsEmpty ι := not_nonempty_iff.mp hi
    have hr := singular_homology_isZero_of_isEmpty (TopCat.of (Σ _ : ι, Y)) R n
    have : IsEmpty {x : (Σ _ : ι, Y) // x.2 ∈ A} := inferInstance
    have hl := singular_homology_isZero_of_isEmpty
      (TopCat.of {x : (Σ _ : ι, Y) // x.2 ∈ A}) R (n - 1)
    have hz : IsZero (P.homology R n) :=
      (P.homology_exact₃ R n (n - 1) (by omega)).isZero_of_both_isZero hr hl
    exact hz.mono _

set_option maxHeartbeats 200000 in
/-- A map of finite CW skeleta that embeds characteristic q-cells induces an
injection on q-homology. The source Hq embeds in the relative group because
its lower skeleton has dimension q-1. Characteristic excision identifies the
relative map with the injective selection of disk pairs, and naturality gives
the absolute injection. Source: Hatcher Lemma 2.34 and Theorem 2.35, pp.137–141. -/
theorem skeleton_homology_mono_of_characteristic
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    [CWComplex (univ : Set X)] [CWComplex (univ : Set Y)]
    [CWComplex.Finite (univ : Set X)] [CWComplex.Finite (univ : Set Y)]
    (q : ℕ) (hq : 0 < q)
    (f : TopCat.of (Skeleton X q) ⟶ TopCat.of (Skeleton Y q))
    (hf : MapsTo f (lowerSkeleton X q) (lowerSkeleton Y q))
    (j : RelCWComplex.cell (univ : Set X) q → RelCWComplex.cell (univ : Set Y) q)
    (hj : Function.Injective j)
    (hchar : ∀ (i : RelCWComplex.cell (univ : Set X) q) (z : CellDisk.{0} q),
      f (characteristicCell X q i z) = characteristicCell Y q (j i) z) :
    Mono (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
      (ModuleCat.of ℚ ℚ)).map f) := by
  let R := ModuleCat.of ℚ ℚ
  let P := singularSubspacePair (TopCat.of (Skeleton X q)) (lowerSkeleton X q)
  let Q := singularSubspacePair (TopCat.of (Skeleton Y q)) (lowerSkeleton Y q)
  let F := singularSubspacePairMap f (lowerSkeleton X q) (lowerSkeleton Y q) hf
  let SX := TopCat.of (Σ _i : RelCWComplex.cell (univ : Set X) q, CellDisk.{0} q)
  let SY := TopCat.of (Σ _i : RelCWComplex.cell (univ : Set Y) q, CellDisk.{0} q)
  let AX : Set SX := {z | z.2 ∈ cellBoundary q}
  let AY : Set SY := {z | z.2 ∈ cellBoundary q}
  let g : SX ⟶ SY := TopCat.ofHom ⟨fun x ↦ ⟨j x.1, x.2⟩,
    continuous_sigma fun i ↦ (show Continuous
      (@Sigma.mk (RelCWComplex.cell (univ : Set Y) q) (fun _ ↦ CellDisk.{0} q) (j i))
      from continuous_sigmaMk)⟩
  let G := singularSubspacePairMap g AX AY (fun _ hx ↦ hx)
  let φX : SX ⟶ TopCat.of (Skeleton X q) := TopCat.ofHom
    ⟨fun z ↦ characteristicCell X q z.1 z.2,
      continuous_sigma fun i ↦ (characteristicCell X q i).continuous⟩
  let φY : SY ⟶ TopCat.of (Skeleton Y q) := TopCat.ofHom
    ⟨fun z ↦ characteristicCell Y q z.1 z.2,
      continuous_sigma fun i ↦ (characteristicCell Y q i).continuous⟩
  let ΦX := singularSubspacePairMap φX AX (lowerSkeleton X q)
    (fun z hz ↦ characteristicCell_mapsTo X q z.1 hz)
  let ΦY := singularSubspacePairMap φY AY (lowerSkeleton Y q)
    (fun z hz ↦ characteristicCell_mapsTo Y q z.1 hz)
  have hiX : IsIso (SSetPair.homologyMap ΦX R q) := by
    dsimp only [ΦX, φX, AX, SX]
    exact characteristic_relative_homology_isIso X q R q
  have hiY : IsIso (SSetPair.homologyMap ΦY R q) := by
    dsimp only [ΦY, φY, AY, SY]
    exact characteristic_relative_homology_isIso Y q R q
  have hiG : Mono (SSetPair.homologyMap G R q) := by
    dsimp only [G, g, AX, AY, SX, SY]
    exact sigmaPair_homology_mono j hj (TopCat.of (CellDisk.{0} q)) (cellBoundary q) R q hq
  have hsquare : ΦX ≫ F = G ≫ ΦY := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      congr 1
      ext z : 2
      exact hchar z.val.1 z.val.2
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      congr 1
      ext z : 1
      exact hchar z.1 z.2
  have hiF : Mono (SSetPair.homologyMap F R q) := by
    have he := congrArg ((SSetPair.homologyFunctor R q).map) hsquare
    simp only [CategoryTheory.Functor.map_comp] at he
    change SSetPair.homologyMap ΦX R q ≫ SSetPair.homologyMap F R q =
      SSetPair.homologyMap G R q ≫ SSetPair.homologyMap ΦY R q at he
    have : Mono (SSetPair.homologyMap ΦX R q ≫ SSetPair.homologyMap F R q) := by
      rw [he]
      infer_instance
    exact (mono_comp_iff_of_isIso _ _).mp this
  have hz : IsZero (P.left.homology R q) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) (m + 1)).obj R
    exact (skeleton_high_degree X m (m + 1) (by omega)).of_iso
      (H.mapIso (TopCat.isoOfHomeo (X := TopCat.of (lowerSkeleton X (m + 1)))
        (Y := TopCat.of (Skeleton X m)) (lowerSkeletonHomeomorph X m)))
  have hiπ : Mono (P.homologyπ R q) :=
    (P.homology_exact₂ R q).mono_g (hz.eq_zero_of_src _)
  have he : SSet.homologyMap F.hom.right R q ≫ Q.homologyπ R q =
      P.homologyπ R q ≫ SSetPair.homologyMap F R q := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    exact ((SSetPair.chainComplexFunctorπ (ModuleCat ℚ)).app R).naturality F
  have : Mono (SSet.homologyMap F.hom.right R q ≫ Q.homologyπ R q) := by
    rw [he]
    infer_instance
  exact mono_of_mono (SSet.homologyMap F.hom.right R q) (Q.homologyπ R q)

end HolomorphicAnosov.CharacteristicCellComparison

