import HolomorphicAnosov.Topology.HomologyZeroPathConnectedMap
import HolomorphicAnosov.Topology.ContractibleSubspaceHomologyProjection
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_discrete
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundaryCollapseSphereHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundarySphereHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundaryCollarRetract
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundary_goodPair_guards
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundary_nonempty
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import HolomorphicAnosov.Topology.Homology.SSetPairRestrictScalarsHomologyIso
import HolomorphicAnosov.Topology.CWComplex.EuclideanSupRadialHomeomorph
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.Topology.Homology.EmptySingularHomology

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov

/-- Above its dimension a sphere has zero ordinary homology with any abelian-group
coefficient object. Source: Hatcher, Corollary 2.14 p.114 and Proposition 2.22 p.124.
The zero sphere is discrete. In the induction step collapse the boundary of the disk;
the quotient is the next sphere. The good-pair map identifies relative homology,
and the exact sequence of the contractible disk shifts its degree down by one.
Since the degree is above the sphere dimension, both shifted degrees are positive,
so ordinary homology suffices throughout. -/
theorem sphere_high_degree_integral_module (m q : ℕ) (hq : m < q)
    (R : ModuleCat ℤ) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) q).obj R).obj
      (TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1})) := by
  induction m generalizing q with
  | zero =>
    let : DiscreteTopology {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1} :=
      Topology.Homology.zeroSphere_discrete
    exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) q R _ (by omega)
  | succ m ih =>
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    let E := EuclideanSpace ℝ (Fin (m + 1))
    let D := {x : E // ‖x‖ ≤ 1}
    let A : Set D := {x | ‖x.val‖ = 1}
    let V : Set D := {x | (1 : ℝ) / 2 < ‖x.val‖}
    obtain ⟨hclosed, _, hneighborhood⟩ :=
      Topology.Homology.diskBoundary_goodPair_guards (E := E)
    have hA : A.Nonempty := Topology.Homology.diskBoundary_nonempty m
    have hAV : A ⊆ V := by
      intro x hx
      change (1 : ℝ) / 2 < ‖x.val‖
      change ‖x.val‖ = 1 at hx
      rw [hx]
      norm_num
    have : ContractibleSpace D := by
      have hc := Metric.contractibleSpace_closedBall (x := (0 : E)) (r := 1) (by norm_num)
      have he : Metric.closedBall (0 : E) 1 = {x : E | ‖x‖ ≤ 1} := by
        ext x
        simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq]
      rw [he] at hc
      exact hc
    let Q := GoodPair.Collapsed A
    let B := GoodPair.collapsedPart A
    let P := singularSubspacePair (TopCat.of D) A
    let PB := singularSubspacePair (TopCat.of Q) B
    have : Subsingleton B := ⟨by
      intro x y
      apply Subtype.ext
      obtain ⟨a, ha, hax⟩ := x.property
      obtain ⟨b, hb, hby⟩ := y.property
      rw [← hax, ← hby]
      exact Quotient.sound (Or.inr ⟨ha, hb⟩)⟩
    have : Nonempty B := (Set.Nonempty.image (GoodPair.collapse A) hA).to_subtype
    have : ContractibleSpace B := inferInstance
    have hproj := contractible_subspace_homology_projection_isIso
      (TopCat.of Q) B R (q + 1) (by omega)
    have hcollapse := GoodPair.collapse_homology_isIso_of_good_pair
      (TopCat.of D) A V hA hclosed hAV hneighborhood
      Topology.Homology.diskBoundaryCollarRetract R (q + 1)
    have hz (k : ℕ) (hk : k ≠ 0) : IsZero (P.right.homology R k) :=
      singular_homology_isZero_of_contractible (TopCat.of D) R k hk
    let shift := (P.shortExact_chainComplexShortComplex R).δIso (q + 1) q
      (by simp) (hz (q + 1) (by omega)) (hz q (by omega))
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) q).obj R
    let eA := F.mapIso (TopCat.isoOfHomeo (X := TopCat.of A)
      (Y := TopCat.of {x : E // ‖x‖ = 1})
      (Topology.Homology.diskBoundarySphereHomeomorph (E := E)))
    have hzeroA : IsZero (P.left.homology R q) :=
      (ih q (by omega)).of_iso eA
    have hzeroP : IsZero (P.homology R (q + 1)) := hzeroA.of_iso shift
    have hzeroPB : IsZero (PB.homology R (q + 1)) :=
      hzeroP.of_iso (asIso (SSetPair.homologyMap
        (GoodPair.collapseSingularPairMap (TopCat.of D) A) R (q + 1))).symm
    have hzeroQ : IsZero (PB.right.homology R (q + 1)) :=
      hzeroPB.of_iso (asIso (PB.homologyπ R (q + 1)))
    let G := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) (q + 1)).obj R
    exact hzeroQ.of_iso (G.mapIso (TopCat.isoOfHomeo (X := TopCat.of Q)
      (Y := TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1 + 1)) // ‖x‖ = 1})
      (Topology.Homology.diskBoundaryCollapseSphereHomeomorph m))).symm

/-- Every positive-dimensional Euclidean unit sphere is path connected. -/
theorem euclideanSphere_pathConnected (m : ℕ) (hm : 0 < m) :
    PathConnectedSpace {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1} := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  have hrank : 1 < Module.rank ℝ E := by
    apply Module.one_lt_rank_of_one_lt_finrank
    simpa [E] using (by omega : 1 < m + 1)
  have hp := isPathConnected_sphere hrank (0 : E) (by norm_num : (0 : ℝ) ≤ 1)
  have hset : Metric.sphere (0 : E) 1 = {x : E | ‖x‖ = 1} := by
    ext x
    simp only [Metric.mem_sphere, dist_zero_right, Set.mem_ofPred_eq]
  rw [hset] at hp
  exact isPathConnected_iff_pathConnectedSpace.mp hp

/-- Positive homology below the sphere dimension vanishes with arbitrary integer-module
coefficients. Source: Hatcher, Corollary 2.14 p.114 and Proposition 2.22 p.124.
Collapse the boundary of the contractible disk to identify the next sphere.
In degrees at least two the exact sequence shifts to the preceding sphere.
In degree one the preceding sphere is path connected, so its H₀ inclusion into
the disk is an isomorphism and exactness gives zero relative H₁. -/
theorem sphere_low_degree_integral_module (m q : ℕ) (hq : q < m) (hqpos : 0 < q)
    (R : ModuleCat ℤ) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) q).obj R).obj
      (TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1})) := by
  induction m generalizing q with
  | zero => omega
  | succ m ih =>
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    let E := EuclideanSpace ℝ (Fin (m + 1))
    let D := {x : E // ‖x‖ ≤ 1}
    let A : Set D := {x | ‖x.val‖ = 1}
    let V : Set D := {x | (1 : ℝ) / 2 < ‖x.val‖}
    obtain ⟨hclosed, _, hneighborhood⟩ :=
      Topology.Homology.diskBoundary_goodPair_guards (E := E)
    have hA : A.Nonempty := Topology.Homology.diskBoundary_nonempty m
    have hAV : A ⊆ V := by
      intro x hx
      change (1 : ℝ) / 2 < ‖x.val‖
      change ‖x.val‖ = 1 at hx
      rw [hx]
      norm_num
    have : ContractibleSpace D := by
      have hc := Metric.contractibleSpace_closedBall (x := (0 : E)) (r := 1) (by norm_num)
      have he : Metric.closedBall (0 : E) 1 = {x : E | ‖x‖ ≤ 1} := by
        ext x
        simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq]
      rw [he] at hc
      exact hc
    let Q := GoodPair.Collapsed A
    let B := GoodPair.collapsedPart A
    let P := singularSubspacePair (TopCat.of D) A
    let PB := singularSubspacePair (TopCat.of Q) B
    have : Subsingleton B := ⟨by
      intro x y
      apply Subtype.ext
      obtain ⟨a, ha, hax⟩ := x.property
      obtain ⟨b, hb, hby⟩ := y.property
      rw [← hax, ← hby]
      exact Quotient.sound (Or.inr ⟨ha, hb⟩)⟩
    have : Nonempty B := (Set.Nonempty.image (GoodPair.collapse A) hA).to_subtype
    have : ContractibleSpace B := inferInstance
    have hproj := contractible_subspace_homology_projection_isIso
      (TopCat.of Q) B R (q + 1) (by omega)
    have hcollapse := GoodPair.collapse_homology_isIso_of_good_pair
      (TopCat.of D) A V hA hclosed hAV hneighborhood
      Topology.Homology.diskBoundaryCollarRetract R (q + 1)
    have hz (k : ℕ) (hk : k ≠ 0) : IsZero (P.right.homology R k) :=
      singular_homology_isZero_of_contractible (TopCat.of D) R k hk
    have hzeroP : IsZero (P.homology R (q + 1)) := by
      by_cases hq0 : q = 0
      · subst q
        have : PathConnectedSpace {x : E // ‖x‖ = 1} :=
          euclideanSphere_pathConnected m (by omega)
        have : PathConnectedSpace A :=
          (Topology.Homology.diskBoundarySphereHomeomorph (E := E)).symm.pathConnectedSpace
        have hi : IsIso (SSet.homologyMap P.hom R 0) :=
          singular_homology_zero_map_isIso_of_pathConnected
            (singularSubspaceInclusion (TopCat.of D) A) R
        have hδ : P.homologyδ R 1 0 = 0 := by
          apply (cancel_mono (SSet.homologyMap P.hom R 0)).mp
          simp only [P.homologyδ_comp R 1 0, zero_comp]
        exact (P.homology_exact₃ R 1 0).isZero_of_both_zeros
          ((hz 1 (by omega)).eq_zero_of_src _) hδ
      · let shift := (P.shortExact_chainComplexShortComplex R).δIso (q + 1) q
          (by simp) (hz (q + 1) (by omega)) (hz q hq0)
        let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) q).obj R
        let eA := F.mapIso (TopCat.isoOfHomeo (X := TopCat.of A)
          (Y := TopCat.of {x : E // ‖x‖ = 1})
          (Topology.Homology.diskBoundarySphereHomeomorph (E := E)))
        have hzeroA : IsZero (P.left.homology R q) :=
          (ih q (by omega) (by omega)).of_iso eA
        exact hzeroA.of_iso shift
    have hzeroPB : IsZero (PB.homology R (q + 1)) :=
      hzeroP.of_iso (asIso (SSetPair.homologyMap
        (GoodPair.collapseSingularPairMap (TopCat.of D) A) R (q + 1))).symm
    have hzeroQ : IsZero (PB.right.homology R (q + 1)) :=
      hzeroPB.of_iso (asIso (PB.homologyπ R (q + 1)))
    let G := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) (q + 1)).obj R
    exact hzeroQ.of_iso (G.mapIso (TopCat.isoOfHomeo (X := TopCat.of Q)
      (Y := TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1 + 1)) // ‖x‖ = 1})
      (Topology.Homology.diskBoundaryCollapseSphereHomeomorph m))).symm

/-- Forgetting rational scalars leaves the same homology group, so the preceding
arbitrary integer-module calculation implies the rational sphere calculation. -/
theorem sphere_high_degree_rational (m q : ℕ) (hq : m < q) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
      (ModuleCat.of ℚ ℚ)).obj
      (TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1})) := by
  let X := TopCat.toSSet.obj
    (TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1})
  let R := ModuleCat.of ℚ ℚ
  let F := ModuleCat.restrictScalars (Int.castRingHom ℚ)
  let G := F.mapHomologicalComplex (.down ℕ)
  let K := X.chainComplex R
  let e := (SSet.chainComplexFunctorObjCompMapIso F R).app X
  let h : F.obj (K.homology q) ≅ (X.chainComplex (F.obj R)).homology q :=
    ((K.sc q).mapHomologyIso F).symm ≪≫
      ((HomologicalComplex.homologyFunctorIso (ModuleCat ℤ) (.down ℕ) q).app
        (G.obj K)).symm ≪≫ HomologicalComplex.homologyMapIso e q
  have hz : IsZero (F.obj (K.homology q)) :=
    (sphere_high_degree_integral_module m q hq (F.obj R)).of_iso h
  have hs : Subsingleton (F.obj (K.homology q)) := ModuleCat.subsingleton_of_isZero hz
  have hs' : Subsingleton (K.homology q) := hs
  change IsZero (K.homology q)
  exact ModuleCat.isZero_of_subsingleton _

/-- Forgetting rational scalars leaves the same homology group, so the preceding
arbitrary integer-module calculation implies the rational sphere calculation. -/
theorem sphere_low_degree_rational (m q : ℕ) (hq : q < m) (hqpos : 0 < q) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
      (ModuleCat.of ℚ ℚ)).obj
      (TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1})) := by
  let X := TopCat.toSSet.obj
    (TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1})
  let R := ModuleCat.of ℚ ℚ
  let F := ModuleCat.restrictScalars (Int.castRingHom ℚ)
  let G := F.mapHomologicalComplex (.down ℕ)
  let K := X.chainComplex R
  let e := (SSet.chainComplexFunctorObjCompMapIso F R).app X
  let h : F.obj (K.homology q) ≅ (X.chainComplex (F.obj R)).homology q :=
    ((K.sc q).mapHomologyIso F).symm ≪≫
      ((HomologicalComplex.homologyFunctorIso (ModuleCat ℤ) (.down ℕ) q).app
        (G.obj K)).symm ≪≫ HomologicalComplex.homologyMapIso e q
  have hz : IsZero (F.obj (K.homology q)) :=
    (sphere_low_degree_integral_module m q hq hqpos (F.obj R)).of_iso h
  have hs : Subsingleton (F.obj (K.homology q)) := ModuleCat.subsingleton_of_isZero hz
  have hs' : Subsingleton (K.homology q) := hs
  change IsZero (K.homology q)
  exact ModuleCat.isZero_of_subsingleton _

/-- The boundary of the native characteristic disk is the Euclidean sphere,
through the norm-preserving radial change of coordinates. -/
theorem cellBoundary_euclidean_homeomorph (m : ℕ) :
    Nonempty (CharacteristicCellComparison.cellBoundary.{0} m ≃ₜ
      {x : EuclideanSpace ℝ (Fin m) // ‖x‖ = 1}) := by
  obtain ⟨e, he⟩ := euclidean_sup_radial_homeomorph m
  let f : CharacteristicCellComparison.cellBoundary.{0} m ≃ₜ
      {x : Fin m → ℝ // ‖x‖ = 1} := {
    toFun := fun x ↦ ⟨x.val.down.val, by
      simpa [CharacteristicCellComparison.cellBoundary, Metric.mem_sphere, dist_zero_right]
        using x.property⟩
    invFun := fun x ↦ ⟨ULift.up ⟨x.val, by
      simpa [Metric.mem_closedBall, dist_zero_right] using x.property.le⟩, by
      simpa [CharacteristicCellComparison.cellBoundary, Metric.mem_sphere, dist_zero_right]
        using x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val)
    continuous_invFun := by continuity }
  exact ⟨f.trans (e.symm.subtype (fun x ↦ by
    have h := he (e.symm x)
    rw [e.apply_symm_apply] at h
    rw [h]))⟩

/-- The literal characteristic disk pair has zero relative rational homology above
its cell dimension. Source: Hatcher Lemma 2.34(a), pp.137–138. The disk is
contractible; its pair sequence identifies degree q≥2 with sphere degree q−1.
In dimension zero the boundary is empty and the disk is a point. -/
theorem cellDisk_high_degree_rational (m q : ℕ) (hq : m < q) :
    IsZero ((singularSubspacePair (TopCat.of (CharacteristicCellComparison.CellDisk.{0} m))
      (CharacteristicCellComparison.cellBoundary m)).homology (ModuleCat.of ℚ ℚ) q) := by
  let D := CharacteristicCellComparison.CellDisk.{0} m
  let A := CharacteristicCellComparison.cellBoundary.{0} m
  let R := ModuleCat.of ℚ ℚ
  let P := singularSubspacePair (TopCat.of D) A
  have : ContractibleSpace (Metric.closedBall (0 : Fin m → ℝ) 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  have : ContractibleSpace D := Homeomorph.ulift.contractibleSpace
  have hz (n : ℕ) (hn : n ≠ 0) : IsZero (P.right.homology R n) :=
    singular_homology_isZero_of_contractible (TopCat.of D) R n hn
  cases m with
  | zero =>
    have : IsEmpty A := ⟨by
      intro x
      have hx := x.property
      change x.val.down.val ∈ Metric.sphere (0 : Fin 0 → ℝ) 1 at hx
      rw [show x.val.down.val = 0 from Subsingleton.elim _ _] at hx
      simp only [Metric.mem_sphere, dist_self, zero_ne_one] at hx⟩
    have : Mono (P.homologyδ R q (q - 1)) :=
      (P.homology_exact₃ R q (q - 1) (by omega)).mono_g ((hz q (by omega)).eq_of_src _ _)
    have ha := singular_homology_isZero_of_isEmpty (TopCat.of A) R (q - 1)
    have hδ : q - 1 + 1 = q := by omega
    exact IsZero.of_mono (P.homologyδ R q (q - 1) hδ) ha
  | succ m =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    obtain ⟨e⟩ := cellBoundary_euclidean_homeomorph (m + 1)
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) r).obj R
    have ha : IsZero (P.left.homology R r) :=
      (sphere_high_degree_rational m r (by omega)).of_iso
        (F.mapIso (TopCat.isoOfHomeo (X := TopCat.of A)
          (Y := TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1}) e))
    exact ha.of_iso ((P.shortExact_chainComplexShortComplex R).δIso (r + 1) r
      (by simp) (hz (r + 1) (by omega)) (hz r (by omega)))

/-- Below its cell dimension the characteristic disk-boundary pair has zero rational
homology. Source: Hatcher Lemma 2.34(a), pp.137–138. In degrees at least two the
pair sequence shifts to sphere homology one degree lower. In degree one the
boundary is connected and its H₀ map is an isomorphism. In degree zero its
nonempty boundary surjects onto the H₀ of the disk. -/
theorem cellDisk_low_degree_rational (m q : ℕ) (hq : q < m) :
    IsZero ((singularSubspacePair (TopCat.of (CharacteristicCellComparison.CellDisk.{0} m))
      (CharacteristicCellComparison.cellBoundary m)).homology (ModuleCat.of ℚ ℚ) q) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let D := CharacteristicCellComparison.CellDisk.{0} (m + 1)
  let A := CharacteristicCellComparison.cellBoundary.{0} (m + 1)
  let R := ModuleCat.of ℚ ℚ
  let P := singularSubspacePair (TopCat.of D) A
  have : ContractibleSpace (Metric.closedBall (0 : Fin (m + 1) → ℝ) 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  have : ContractibleSpace D := Homeomorph.ulift.contractibleSpace
  obtain ⟨e⟩ := cellBoundary_euclidean_homeomorph (m + 1)
  have hz (n : ℕ) (hn : n ≠ 0) : IsZero (P.right.homology R n) :=
    singular_homology_isZero_of_contractible (TopCat.of D) R n hn
  by_cases hq0 : q = 0
  · subst q
    have hne : Nonempty {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1} := by
      obtain ⟨x, hx⟩ := Topology.Homology.diskBoundary_nonempty m
      exact ⟨⟨x.val, hx⟩⟩
    have : Nonempty A := ⟨e.symm (Classical.choice hne)⟩
    have hi : Epi (SSet.homologyMap P.hom R 0) :=
      singular_homology_zero_map_epi_of_pathConnected
        (singularSubspaceInclusion (TopCat.of D) A) R
    apply IsZero.of_epi_eq_zero (P.homologyπ R 0)
    apply (cancel_epi (SSet.homologyMap P.hom R 0)).mp
    exact (P.homologyMap_hom_homologyπ R 0).trans (comp_zero).symm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
  by_cases hq1 : q = 0
  · subst q
    have : PathConnectedSpace {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1} :=
      euclideanSphere_pathConnected m (by omega)
    have : PathConnectedSpace A := e.symm.pathConnectedSpace
    have hi : IsIso (SSet.homologyMap P.hom R 0) :=
      singular_homology_zero_map_isIso_of_pathConnected
        (singularSubspaceInclusion (TopCat.of D) A) R
    have hδ : P.homologyδ R 1 0 = 0 := by
      apply (cancel_mono (SSet.homologyMap P.hom R 0)).mp
      simp only [P.homologyδ_comp R 1 0, zero_comp]
    exact (P.homology_exact₃ R 1 0).isZero_of_both_zeros
      ((hz 1 (by omega)).eq_zero_of_src _) hδ
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj R
  have ha : IsZero (P.left.homology R q) :=
    (sphere_low_degree_rational m q (by omega) (by omega)).of_iso
      (F.mapIso (TopCat.isoOfHomeo (X := TopCat.of A)
        (Y := TopCat.of {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1}) e))
  exact ha.of_iso ((P.shortExact_chainComplexShortComplex R).δIso (q + 1) q
    (by simp) (hz (q + 1) (by omega)) (hz q hq1))

end HolomorphicAnosov



