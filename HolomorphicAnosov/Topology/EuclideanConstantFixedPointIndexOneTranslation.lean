import HolomorphicAnosov.Topology.EuclideanConstantZeroDisplacementPositiveClass
import HolomorphicAnosov.Topology.EuclideanConstantFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanFixedPointIndexRestriction
import HolomorphicAnosov.Topology.EuclideanSupportOrientationEnlargement
import HolomorphicAnosov.Topology.DiskDegreePairHomotopy
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

noncomputable section
open CategoryTheory TopologicalSpace Set
namespace HolomorphicAnosov

/-- The displacement of a constant map sends its canonical supported orientation
 to the specified positive local class at zero.

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §§1.3–1.4 and 1.7, pp.1–2; Hatcher,
*Algebraic Topology*, Proposition 2.19, p.118.

Proof: first work on all of Euclidean space. The constants `t • c`, for `t ∈ [0,1]`,
have singleton fixed sets contained in the compact segment `L = {t • c}`.
The continuous displacements `x - t • c` never vanish outside L, hence give a
homotopy from the zero-constant displacement to the c-constant displacement on
the fixed pair `(ℝⁿ, ℝⁿ \ L)`. Relative homotopy invariance identifies their
homology maps. Support-enlargement naturality sends `o(ℝⁿ,L)` to the singleton
supported orientation at either endpoint, so the endpoint indices agree.
The zero-displacement theorem identifies the first endpoint with the specified
positive local class. The full-space fixed set `{c}` lies in U, so restriction
naturality identifies the index on U with the full-space index. Finally the
positive local coordinate is injective, giving equality of the classes themselves.
This proof also covers c=0 and dimension zero, where the segment is a singleton.
-/
theorem euclidean_constant_displacement_positive_class
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ U) :
    let f : C(U, EuclideanSpace ℝ (Fin n)) := ContinuousMap.const U c
    let K : Set (EuclideanSpace ℝ (Fin n)) := euclideanAmbientFixedSet f
    let hK : IsCompact K := (constant_fixedSet_compact c hc).image continuous_subtype_val
    let hKU : K ⊆ (U : Set (EuclideanSpace ℝ (Fin n))) := by
      rintro x ⟨u, _hu, rfl⟩
      exact u.property
    (euclideanDisplacementHomologyMap f).hom
      (euclideanSupportOrientation n (U : Set (EuclideanSpace ℝ (Fin n))) K
        U.isOpen hK hKU) = euclideanPositiveLocalClass n := by
  let W : Opens (EuclideanSpace ℝ (Fin n)) := ⊤
  let F (t : unitInterval) : C(W, EuclideanSpace ℝ (Fin n)) :=
    ContinuousMap.const W ((t : ℝ) • c)
  let L : Set (EuclideanSpace ℝ (Fin n)) := range (fun t : unitInterval ↦ (t : ℝ) • c)
  have hL : IsCompact L := isCompact_range (continuous_subtype_val.smul continuous_const)
  have hLW : L ⊆ (W : Set _) := subset_univ _
  have hK (t : unitInterval) : IsCompact (euclideanFixedSet (F t)) :=
    constant_fixedSet_compact _ (by trivial)
  have hKL (t : unitInterval) : euclideanAmbientFixedSet (F t) ⊆ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨t, hx⟩
  let A : Set W := {x | x.val ∉ L}
  let B : Set (EuclideanSpace ℝ (Fin n)) := {0}ᶜ
  have hd (t : unitInterval) : MapsTo (euclideanDisplacement (F t)) A B := by
    intro x hx hz
    apply hx
    exact ⟨t, (sub_eq_zero.mp hz).symm⟩
  let d (t : unitInterval) := singularSubspacePairMap
    (TopCat.ofHom (euclideanDisplacement (F t))) A B (hd t)
  let H : ContinuousMap.Homotopy (euclideanDisplacement (F 0))
      (euclideanDisplacement (F 1)) :=
    { toFun := fun p ↦ p.2.val - (p.1 : ℝ) • c
      continuous_toFun := (continuous_subtype_val.comp continuous_snd).sub
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
      map_zero_left := by intro x; rfl
      map_one_left := by intro x; rfl }
  have hH : ∀ (t : unitInterval) (x : W), x ∈ A → H (t, x) ∈ B := by
    intro t x hx
    exact hd t hx
  have hmaps := (relative_singular_homotopy_invariance (ModuleCat ℤ)
    (Topology.topPairHomotopy_of_continuousMapHomotopy A B
      (euclideanDisplacement (F 0)) (euclideanDisplacement (F 1))
      (hd 0) (hd 1) H hH) reducedSingularIntegralCoefficients).2 n
  change SSetPair.homologyMap (d 0) reducedSingularIntegralCoefficients n =
    SSetPair.homologyMap (d 1) reducedSingularIntegralCoefficients n at hmaps
  let o := euclideanSupportOrientation n (W : Set _) L W.isOpen hL hLW
  have hindex (t : unitInterval) : euclideanFixedPointIndex (F t) (hK t) =
      euclideanPositiveLocalCoordinate n
        ((SSetPair.homologyMap (d t) reducedSingularIntegralCoefficients n).hom o) := by
    let r := singularSubspacePairMap (𝟙 (TopCat.of W)) A
      {x : W | x.val ∉ euclideanAmbientFixedSet (F t)}
      (by intro x hx hk; exact hx (hKL t hk))
    have hp : r ≫ euclideanDisplacementPairMap (F t) = d t := by
      apply MorphismProperty.Arrow.Hom.ext
      · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
        rw [← Functor.map_comp]
        rfl
      · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
        rw [← Functor.map_comp]
        rfl
    have hcomp : SSetPair.homologyMap r reducedSingularIntegralCoefficients n ≫
        euclideanDisplacementHomologyMap (F t) =
        SSetPair.homologyMap (d t) reducedSingularIntegralCoefficients n := by
      unfold euclideanDisplacementHomologyMap
      rw [← SSetPair.homologyMap_comp, hp]
    have ho := euclideanSupportOrientation_enlargement n (W : Set _)
      (euclideanAmbientFixedSet (F t)) L W.isOpen
      ((hK t).image continuous_subtype_val) hL (hKL t) hLW
    have he := congrArg (fun q ↦ q.hom o) hcomp
    have hor := congrArg (fun x ↦ (euclideanDisplacementHomologyMap (F t)).hom x) ho
    exact congrArg (euclideanPositiveLocalCoordinate n) (hor.symm.trans he)
  have hsame : euclideanFixedPointIndex (F 1) (hK 1) =
      euclideanFixedPointIndex (F 0) (hK 0) := by
    rw [hindex 1, hindex 0, hmaps]
  have hzero : euclideanFixedPointIndex (F 0) (hK 0) =
      euclideanPositiveLocalCoordinate n (euclideanPositiveLocalClass n) := by
    have hz := euclidean_zero_displacement_positive_class (U := W) (by trivial)
    have hF0 : F 0 = ContinuousMap.const W 0 := by
      apply ContinuousMap.ext
      intro x
      exact zero_smul ℝ c
    generalize_proofs p
    revert p
    rw [hF0]
    intro p
    exact congrArg (euclideanPositiveLocalCoordinate n) hz
  have hrestriction := restriction_index (ContinuousMap.const W c)
    (constant_fixedSet_compact c (by trivial)) U (show U ≤ W from le_top)
    (by intro x hx; change c = x.val at hx; exact hx ▸ hc)
    (show IsCompact (euclideanFixedSet (restrictedMap (ContinuousMap.const W c) U le_top))
      from constant_fixedSet_compact c hc)
  apply (euclideanPositiveLocalCoordinate n).injective
  change euclideanFixedPointIndex (ContinuousMap.const U c) (constant_fixedSet_compact c hc) = _
  calc
    _ = euclideanFixedPointIndex (ContinuousMap.const W c)
        (constant_fixedSet_compact c (by trivial)) := hrestriction
    _ = euclideanFixedPointIndex (F 0) (hK 0) := by
      simpa only [F, (show ((1 : unitInterval) : ℝ) = 1 from rfl), one_smul] using hsame
    _ = _ := hzero

end HolomorphicAnosov
