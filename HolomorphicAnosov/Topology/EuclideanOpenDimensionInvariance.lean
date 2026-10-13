import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero

/-!
# Invariance of dimension for open Euclidean sets

Source: Hatcher, Algebraic Topology, Theorem 2.26 and proof, printed p. 126,
with the integral sphere calculation, Corollary 2.14, p. 114.
DAG node: `topo.euclidean_open_dimension_invariance`.
-/

namespace HolomorphicAnosov

/-- A nonempty open Euclidean set is a singleton only in dimension zero.
This proves the zero-dimensional edge of Hatcher Theorem 2.26 without negative
sphere notation or an assumed homology profile. In positive dimension an actual
small nonzero coordinate vector translates an interior point to a distinct point. -/
theorem euclidean_open_subsingleton_dimension_zero
    {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hne : U.Nonempty) (hsub : Subsingleton U) : n = 0 := by
  by_contra hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let i : Fin n := ⟨0, hnpos⟩
  let v : EuclideanSpace ℝ (Fin n) := PiLp.single 2 i (ε / 2)
  have hvnorm : ‖v‖ = ε / 2 := by
    simp [v, Real.norm_eq_abs, abs_of_nonneg hε.le]
  have hxv : x + v ∈ U := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hvnorm]
    linarith)
  have he : x + v = x :=
    congrArg Subtype.val (@Subsingleton.elim U hsub ⟨x + v, hxv⟩ ⟨x, hx⟩)
  have hv0 : v = 0 := add_left_cancel (he.trans (add_zero x).symm)
  have heps : ε / 2 = 0 := by
    have hh := congrArg norm hv0
    simpa [hvnorm] using hh
  linarith

/-- The zero-dimensional alternatives are preserved by the actual given
homeomorphism. This includes arbitrary disconnected open sets and the genuine
native Euclidean L² topology; it assumes no differentiability of the map. -/
theorem euclidean_open_dimension_zero_iff
    {m n : ℕ} (U : Set (EuclideanSpace ℝ (Fin m)))
    (W : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hW : IsOpen W) (hneU : U.Nonempty) (hneW : W.Nonempty)
    (h : ↥U ≃ₜ ↥W) : m = 0 ↔ n = 0 := by
  constructor
  · intro hm
    subst m
    have : Subsingleton U := inferInstance
    have hs : Subsingleton W := h.symm.injective.subsingleton
    exact euclidean_open_subsingleton_dimension_zero W hW hneW hs
  · intro hn
    subst n
    have : Subsingleton W := inferInstance
    have hs : Subsingleton U := h.injective.subsingleton
    exact euclidean_open_subsingleton_dimension_zero U hU hneU hs

open CategoryTheory
noncomputable section

/-- A homeomorphism carries the actual punctured pair to the actual punctured pair.
Both component maps are literal h and its restriction; no abstract local-homology
or dimension invariant is introduced. Source: Hatcher Theorem 2.26 p.126. -/
def puncturedPairHomeomorphIso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x : X) :
    TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X)) ≅
      TopPair.ofSubset ({h x}ᶜ : Set (TopCat.of Y)) where
  hom := TopPair.ofHom (TopCat.ofHom ⟨h, h.continuous⟩)
    (TopCat.ofHom ⟨fun z ↦ ⟨h z.val, by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (fun he ↦ z.property (h.injective he))⟩,
      (h.continuous.comp continuous_subtype_val).subtype_mk (by
        intro z he
        exact z.property (h.injective he))⟩) (by rfl)
  inv := TopPair.ofHom (TopCat.ofHom ⟨h.symm, h.symm.continuous⟩)
    (TopCat.ofHom ⟨fun z ↦ ⟨h.symm z.val, by
      intro he
      apply z.property
      exact (h.apply_symm_apply z.val).symm.trans (congrArg h he)⟩,
      (h.symm.continuous.comp continuous_subtype_val).subtype_mk (by
        intro z he
        apply z.property
        exact (h.apply_symm_apply z.val).symm.trans (congrArg h he))⟩) (by rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      apply Subtype.ext
      exact h.symm_apply_apply z.val
    · ext z
      exact h.symm_apply_apply z
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      apply Subtype.ext
      exact h.apply_symm_apply z.val
    · ext z
      exact h.apply_symm_apply z

/-- The actual pair homeomorphism induces inverse relative singular homology maps
in EVERY nonnegative degree, with arbitrary genuine integer-module coefficients.
This completes Step 1 of Hatcher's dimension argument entirely in native APIs. -/
def puncturedRelativeHomologyIso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x : X) (R : ModuleCat.{u} ℤ) (k : ℕ) :
    (singularPairFunctor.obj (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X)))).homology R k ≅
      (singularPairFunctor.obj (TopPair.ofSubset ({h x}ᶜ : Set (TopCat.of Y)))).homology R k :=
  (SSetPair.homologyFunctor R k).mapIso
    (singularPairFunctor.mapIso (puncturedPairHomeomorphIso h x))

end

open CategoryTheory

/-- Native excision for an actual open neighborhood of a closed Euclidean point.
The source is literally the original U and its punctured native subspace. All
interior-cover hypotheses are proved here; only the existing named source excision
result is used for the homology isomorphism certificate, so its admission remains
visible in the axiom report. Source: Hatcher Theorems 2.20 and 2.26 pp.119,124,126. -/
theorem euclidean_open_neighbourhood_excision
    {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
    (R : ModuleCat ℤ) (k : ℕ) :
    IsIso (SSetPair.homologyMap
      (singularExcisionInclusion (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ U) R k) := by
  have hA : IsOpen ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := isClosed_singleton.isOpen_compl
  have hcover : interior ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) ∪ interior U = Set.univ := by
    rw [hA.interior_eq, hU.interior_eq]
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hz : z = x
    · exact Or.inr (hz ▸ hx)
    · exact Or.inl hz
  exact ((singular_homology_excision_barycentric_subdivision.2.1
    (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ U hcover R).2.2) k

open scoped unitInterval
noncomputable section

/-- Literal radial normalization off zero, in the original norm topology.
Source: Hatcher's punctured Euclidean deformation in Theorem 2.26 p.126.
The same formula is valid in any real normed space, including the vacuous
punctured rank-zero space; no arbitrary coordinate transport is used. -/
def puncturedRadialSphereMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C({x : E // x ≠ 0}, {x : E // ‖x‖ = 1}) where
  toFun x := ⟨‖x.val‖⁻¹ • x.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr x.property)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.property)]⟩
  continuous_toFun :=
    (((continuous_norm.comp continuous_subtype_val).inv₀
      (fun x ↦ norm_ne_zero_iff.mpr x.property)).smul continuous_subtype_val).subtype_mk _

/-- Unit-sphere inclusion into the actual punctured space. -/
def spherePuncturedInclusion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C({x : E // ‖x‖ = 1}, {x : E // x ≠ 0}) where
  toFun x := ⟨x.val, by intro h; have := x.property; simp [h] at this⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Actual punctured radial homotopy with all-time nonzero guard.
At t=0 the scalar is one; at t=1 it is inverse norm; at every intermediate
point its two nonnegative summands cannot both vanish. This is the literal
Hatcher radial algorithm and an ordinary native continuous homotopy. -/
def puncturedRadialHomotopy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.Homotopy (ContinuousMap.id {x : E // x ≠ 0})
      (spherePuncturedInclusion.comp puncturedRadialSphereMap) where
  toFun z := ⟨((1 - (z.1 : ℝ)) + (z.1 : ℝ) * ‖z.2.val‖⁻¹) • z.2.val, by
    have hn : 0 < ‖z.2.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr z.2.property)
    have ht0 := z.1.property.1
    have ht1 := z.1.property.2
    have hc : 0 < (1 - (z.1 : ℝ)) + (z.1 : ℝ) * ‖z.2.val‖⁻¹ := by
      by_cases ht : (z.1 : ℝ) = 1
      · simp [ht, hn]
      · have hlt : (z.1 : ℝ) < 1 := lt_of_le_of_ne ht1 ht
        have hmul : 0 ≤ (z.1 : ℝ) * ‖z.2.val‖⁻¹ := mul_nonneg ht0 hn.le
        linarith
    exact smul_ne_zero hc.ne' z.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hn : Continuous (fun z : unitInterval × {x : E // x ≠ 0} ↦ ‖z.2.val‖⁻¹) :=
      (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).inv₀
        (fun z ↦ norm_ne_zero_iff.mpr z.2.property)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul hn)).smul
        (continuous_subtype_val.comp continuous_snd)
  map_zero_left x := by apply Subtype.ext; simp
  map_one_left x := by apply Subtype.ext; simp [puncturedRadialSphereMap, spherePuncturedInclusion]

end

noncomputable section

/-- Punctured normed space is homotopy equivalent to its actual unit sphere,
with the specified radial normalization/inclusion as the two maps. For a
zero-dimensional space both carriers are empty and the construction is still
valid. Positive-dimensional sphere homology is used only later in Hatcher's
argument. Both inverse homotopies are provided here, not supplied hypotheses. -/
def puncturedSphereHomotopyEquiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.HomotopyEquiv {x : E // x ≠ 0} {x : E // ‖x‖ = 1} where
  toFun := puncturedRadialSphereMap
  invFun := spherePuncturedInclusion
  left_inv := ⟨puncturedRadialHomotopy.symm⟩
  right_inv := by
    have he : (puncturedRadialSphereMap.comp spherePuncturedInclusion :
        C({x : E // ‖x‖ = 1}, {x : E // ‖x‖ = 1})) = ContinuousMap.id _ := by
      ext x
      change ‖x.val‖⁻¹ • x.val = x.val
      rw [x.property, inv_one, one_smul]
    rw [he]

/-- The radial deformation fixes the genuine unit sphere at every time. -/
theorem puncturedRadialHomotopy_fixes_sphere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : unitInterval) (x : {x : E // ‖x‖ = 1}) :
    puncturedRadialHomotopy (t, spherePuncturedInclusion x) =
      spherePuncturedInclusion x := by
  apply Subtype.ext
  change ((1 - (t : ℝ)) + (t : ℝ) * ‖x.val‖⁻¹) • x.val = x.val
  rw [x.property, inv_one, mul_one, sub_add_cancel, one_smul]

end

noncomputable section

/-- Hatcher's actual radial deformation induces the reduced homology comparison
with the actual unit sphere, including the augmentation-kernel degree zero. -/
def puncturedReducedSphereHomologyIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    integralReducedSingularHomology (TopCat.of {x : E // x ≠ 0}) n ≅
      integralReducedSingularHomology (TopCat.of {x : E // ‖x‖ = 1}) n :=
  Topology.Homology.integralReducedHomologyIsoOfHomotopyEquiv
    puncturedSphereHomotopyEquiv n

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary zero-dimensional singular homology is the actual cokernel of
the first boundary. This uses no connectedness or nonemptiness assumption. -/
def ordinaryIntegralH0CokernelIso (X : TopCat.{u}) :
    ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients).homology 0 ≅
      CategoryTheory.Limits.cokernel
        (((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients).d 1 0) := by
  let C := (TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients
  let S := C.sc' 1 0 0
  exact C.homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    S.asIsoHomologyι (C.shape 0 0 (by simp)) ≪≫ S.opcyclesIsoCokernel

/-- The coefficient-sum augmentation induced on ORDINARY singular H₀.
It is descended from the original chain augmentation through the actual first
boundary cokernel. Source: Hatcher p.110. -/
def ordinaryIntegralH0Augmentation (X : TopCat.{u}) :
    ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients).homology 0 ⟶
      reducedSingularIntegralCoefficients :=
  (ordinaryIntegralH0CokernelIso X).hom ≫
    CategoryTheory.Limits.cokernel.desc _ (integralSingularAugmentation X) (by
      apply SSet.chainComplex_hom_ext
      intro simplex
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp [integralSingularAugmentation, SSet.ιChainComplex, Fin.sum_univ_two])

set_option backward.isDefEq.respectTransparency false in
/-- The augmented reduced H₀ is the kernel of coefficient sum on ORDINARY H₀.
This is the exact degree-one edge needed by the local-relative-homology argument;
no false identification of reduced H₀ with ordinary H₀ is made. -/
def integralReducedH0AugmentationKernelIso (X : TopCat.{u}) :
    integralReducedSingularHomology X 0 ≅
      CategoryTheory.Limits.kernel (ordinaryIntegralH0Augmentation X) := by
  let A := augmentedIntegralSingularChains X
  let S := A.sc' 2 1 0
  let e := ordinaryIntegralH0CokernelIso X
  exact A.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    S.homologyIsoKernelDesc ≪≫
    CategoryTheory.Limits.kernel.mapIso _ _ e.symm (Iso.refl _) (by
      simp [e, ordinaryIntegralH0Augmentation]
      rfl)

/-- Ordinary punctured homology in each positive degree is the actual augmented
reduced homology of the unit sphere, using the proved chain comparison and radial
homotopy. Source: Hatcher Theorem 2.26 p.126. -/
def puncturedOrdinaryPositiveSphereIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of {x : E // x ≠ 0})).chainComplex
      reducedSingularIntegralCoefficients).homology (n + 1) ≅
      integralReducedSingularHomology (TopCat.of {x : E // ‖x‖ = 1}) (n + 1) :=
  (Topology.Homology.integralReducedPositiveOrdinaryIso
    (TopCat.of {x : E // x ≠ 0}) n).symm ≪≫ puncturedReducedSphereHomologyIso (n + 1)

/-- The degree-one RELATIVE argument's punctured H₀ augmentation kernel is the
actual reduced sphere H₀. This retains the two-point S⁰ calculation and never
replaces its reduced H₀ by ordinary H₀. -/
def puncturedH0KernelSphereIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CategoryTheory.Limits.kernel
      (ordinaryIntegralH0Augmentation (TopCat.of {x : E // x ≠ 0})) ≅
      integralReducedSingularHomology (TopCat.of {x : E // ‖x‖ = 1}) 0 :=
  (integralReducedH0AugmentationKernelIso _).symm ≪≫ puncturedReducedSphereHomologyIso 0

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary H₀ cokernel comparison carries the original cycle-class map
to the cokernel projection of the first boundary. -/
theorem ordinaryIntegralH0CokernelIso_projection (X : TopCat.{u}) :
    let C := (TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients
    C.homologyπ 0 ≫ (ordinaryIntegralH0CokernelIso X).hom =
      C.iCycles 0 ≫ CategoryTheory.Limits.cokernel.π (C.d 1 0) := by
  simp [ordinaryIntegralH0CokernelIso, ShortComplex.opcyclesIsoCokernel]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient sum on ordinary H₀ agrees with Mathlib's canonical augmentation
through π₀. Equality is checked on actual zero-simplex generators. -/
theorem ordinaryIntegralH0Augmentation_eq (X : TopCat.{u}) :
    ordinaryIntegralH0Augmentation.{u, u} X =
      (TopCat.toSSet.obj X).homology₀ε reducedSingularIntegralCoefficients.{u} := by
  let C := (TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients.{u}
  apply (cancel_epi (C.homologyπ 0)).mp
  rw [ordinaryIntegralH0Augmentation, ← Category.assoc,
    ordinaryIntegralH0CokernelIso_projection, Category.assoc,
    CategoryTheory.Limits.cokernel.π_desc]
  apply (cancel_epi (C.cycles₀Iso.inv)).mp
  apply SSet.chainComplex_hom_ext
  intro simplex
  have he : C.cycles₀Iso.inv = C.liftCycles (𝟙 _) 0 (by simp) (by simp) := by
    apply (cancel_mono (C.iCycles 0)).mp
    simp
  rw [he]
  dsimp [C]
  simp only [← Category.assoc, HomologicalComplex.comp_liftCycles, Category.comp_id]
  rw [HomologicalComplex.liftCycles_i]
  simp only [SSet.ιChainComplex, integralSingularAugmentation, Category.assoc,
    CategoryTheory.Limits.Sigma.ι_comp_desc]
  exact ((TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε
    reducedSingularIntegralCoefficients.{u} simplex).symm

/-- On a path connected space the actual ordinary H₀ coefficient sum is an
isomorphism, without a chosen identification of H₀. -/
theorem ordinaryIntegralH0Augmentation_isIso (X : TopCat.{u}) [PathConnectedSpace X] :
    IsIso (ordinaryIntegralH0Augmentation.{u, u} X) := by
  rw [ordinaryIntegralH0Augmentation_eq X]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient sum is natural for the actual continuous map. -/
theorem ordinaryIntegralH0Augmentation_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.homologyMap (TopCat.toSSet.map f) reducedSingularIntegralCoefficients.{u} 0 ≫
      ordinaryIntegralH0Augmentation.{u, u} Y = ordinaryIntegralH0Augmentation.{u, u} X := by
  let C := (TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients.{u}
  let φ := SSet.chainComplexMap (TopCat.toSSet.map f) reducedSingularIntegralCoefficients.{u}
  apply (cancel_epi (((TopCat.toSSet.obj X).chainComplex
    reducedSingularIntegralCoefficients.{u}).homologyπ 0)).mp
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality]
  simp only [ordinaryIntegralH0Augmentation, Category.assoc]
  simp only [← Category.assoc]
  rw [Category.assoc (HomologicalComplex.cyclesMap
    (SSet.chainComplexMap (TopCat.toSSet.map f) reducedSingularIntegralCoefficients.{u}) 0)
    (((TopCat.toSSet.obj Y).chainComplex reducedSingularIntegralCoefficients.{u}).homologyπ 0)
    (ordinaryIntegralH0CokernelIso Y).hom,
    ordinaryIntegralH0CokernelIso_projection]
  rw [ordinaryIntegralH0CokernelIso_projection]
  simp only [Category.assoc, CategoryTheory.Limits.cokernel.π_desc]
  rw [← Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [Category.assoc]
  congr 1
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  simp [integralSingularAugmentation, SSet.ιChainComplex]

/-- Ordinary integral singular homology, with actual singular maps, carries a
continuous homotopy equivalence to an isomorphism. -/
def ordinaryIntegralHomologyIsoOfHomotopyEquiv {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y)
    (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      reducedSingularIntegralCoefficients.{u}).homology n ≅
    ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
      reducedSingularIntegralCoefficients.{u}).homology n where
  hom := SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom e.toFun))
    reducedSingularIntegralCoefficients.{u} n
  inv := SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom e.invFun))
    reducedSingularIntegralCoefficients.{u} n
  hom_inv_id := by
    rw [← SSet.homologyMap_comp, ← Functor.map_comp]
    obtain ⟨H⟩ := e.left_inv
    have H' : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 (TopCat.of X)) := H
    exact ((H'.toSSet.chainComplexMap reducedSingularIntegralCoefficients.{u}).homologyMap_eq n).trans
      (by simp)
  inv_hom_id := by
    rw [← SSet.homologyMap_comp, ← Functor.map_comp]
    obtain ⟨H⟩ := e.right_inv
    have H' : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 (TopCat.of Y)) := H
    exact ((H'.toSSet.chainComplexMap reducedSingularIntegralCoefficients.{u}).homologyMap_eq n).trans
      (by simp)

/-- The literal affine contraction of a real normed vector space to its zero
point, with a universe-compatible singleton target. -/
def normedSpacePointHomotopyEquiv {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.HomotopyEquiv E (ULift.{u, 0} PUnit.{1}) where
  toFun := ContinuousMap.const _ (ULift.up PUnit.unit)
  invFun := ContinuousMap.const _ 0
  left_inv := ⟨by simpa using
    ContinuousMap.Homotopy.affine (ContinuousMap.const E 0) (ContinuousMap.id E)⟩
  right_inv := by
    have he : ((ContinuousMap.const E (ULift.up PUnit.unit)).comp
        (ContinuousMap.const (ULift.{u, 0} PUnit.{1}) (0 : E))) =
        ContinuousMap.id (ULift.{u, 0} PUnit.{1}) := by
      ext x
    rw [he]


/-- Actual ordinary positive-degree homology of a real normed space vanishes.
The affine contraction induces a homology isomorphism to a point, whose alternating
constant chain complex is calculated by Mathlib. Source: Hatcher pp.109–113,126. -/
theorem normedSpace_positive_integral_homology_isZero {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero
      (((TopCat.toSSet.obj (TopCat.of E)).chainComplex
        reducedSingularIntegralCoefficients.{u}).homology n) := by
  have hpoint := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{u} ℤ) n reducedSingularIntegralCoefficients.{u}
    (TopCat.of (ULift.{u, 0} PUnit.{1})) hn
  exact hpoint.of_iso (ordinaryIntegralHomologyIsoOfHomotopyEquiv
    (normedSpacePointHomotopyEquiv (E := E)) n)

/-- Above degree one, the genuine punctured-pair connecting map is an isomorphism:
both adjacent ambient positive-degree homology objects are zero. -/
def normedSpacePuncturedRelativePositiveIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    (singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))).homology
      reducedSingularIntegralCoefficients.{u} (n + 2) ≅
    ((TopCat.toSSet.obj (TopCat.of {x : E // x ≠ 0})).chainComplex
      reducedSingularIntegralCoefficients.{u}).homology (n + 1) := by
  let P := singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))
  exact (P.shortExact_chainComplexShortComplex reducedSingularIntegralCoefficients.{u}).δIso
    (n + 2) (n + 1) (by simp)
    (normedSpace_positive_integral_homology_isZero _ (by omega))
    (normedSpace_positive_integral_homology_isZero _ (by omega))

/-- The entire positive-degree local-relative comparison except its degree-one
edge, composed with actual radial homotopy and positive augmentation comparison. -/
def normedSpacePuncturedRelativePositiveSphereIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    (singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))).homology
      reducedSingularIntegralCoefficients.{u} (n + 2) ≅
    integralReducedSingularHomology (TopCat.of {x : E // ‖x‖ = 1}) (n + 1) :=
  normedSpacePuncturedRelativePositiveIso n ≪≫ puncturedOrdinaryPositiveSphereIso n

set_option backward.isDefEq.respectTransparency false in
/-- The actual degree-one relative connecting map identifies its group with
the kernel of the inclusion on ordinary H₀. Exactness and the proved ambient H₁
vanishing supply the kernel universal property. -/
def normedSpacePuncturedRelativeH1InclusionKernelIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))).homology
      reducedSingularIntegralCoefficients.{u} 1 ≅
    CategoryTheory.Limits.kernel
      (SSet.homologyMap
        (singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))).hom
        reducedSingularIntegralCoefficients.{u} 0) := by
  let P := singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))
  let S := ShortComplex.mk _ _ (P.homologyδ_comp reducedSingularIntegralCoefficients.{u} 1 0)
  haveI : Mono S.f := (P.shortExact_chainComplexShortComplex
    reducedSingularIntegralCoefficients.{u}).mono_δ 1 0 (by simp)
      (normedSpace_positive_integral_homology_isZero 1 (by omega))
  have hS : S.Exact := P.homology_exact₁ reducedSingularIntegralCoefficients.{u} 1 0
  exact hS.fIsKernel.conePointUniqueUpToIso (CategoryTheory.Limits.limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
/-- The actual inclusion kernel in degree zero is the augmentation kernel:
coefficient sum is natural and is an isomorphism on the ambient normed space. -/
def normedSpacePuncturedH0InclusionAugmentationKernelIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CategoryTheory.Limits.kernel
      (SSet.homologyMap
        (singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))).hom
        reducedSingularIntegralCoefficients.{u} 0) ≅
    CategoryTheory.Limits.kernel
      (ordinaryIntegralH0Augmentation.{u, u} (TopCat.of {x : E // x ≠ 0})) := by
  let f : TopCat.of {x : E // x ≠ 0} ⟶ TopCat.of E :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  haveI : IsIso (ordinaryIntegralH0Augmentation.{u, u} (TopCat.of E)) :=
    ordinaryIntegralH0Augmentation_isIso (TopCat.of E)
  exact CategoryTheory.Limits.kernel.mapIso _ _ (Iso.refl _)
    (asIso (ordinaryIntegralH0Augmentation.{u, u} (TopCat.of E)))
    (by
      change SSet.homologyMap (TopCat.toSSet.map f) reducedSingularIntegralCoefficients.{u} 0 ≫
        ordinaryIntegralH0Augmentation.{u, u} (TopCat.of E) =
        𝟙 _ ≫ ordinaryIntegralH0Augmentation.{u, u} (TopCat.of {x : E // x ≠ 0})
      simpa using ordinaryIntegralH0Augmentation_naturality f)

/-- The actual degree-one punctured-pair group is reduced homology of the unit
sphere in degree zero, including the genuine S⁰ augmentation-kernel convention. -/
def normedSpacePuncturedRelativeH1SphereIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))).homology
      reducedSingularIntegralCoefficients.{u} 1 ≅
    integralReducedSingularHomology (TopCat.of {x : E // ‖x‖ = 1}) 0 :=
  normedSpacePuncturedRelativeH1InclusionKernelIso ≪≫
    normedSpacePuncturedH0InclusionAugmentationKernelIso ≪≫ puncturedH0KernelSphereIso

open scoped Simplicial in
/-- A genuine zero simplex gives a section of coefficient sum. This proves
surjectivity of ordinary H₀ augmentation on every nonempty space. -/
theorem ordinaryIntegralH0Augmentation_epi (X : TopCat.{u}) [Nonempty X] :
    Epi (ordinaryIntegralH0Augmentation.{u, u} X) := by
  classical
  let simplex0 := TopCat.toSSetObj₀Equiv.symm (Classical.arbitrary X)
  let C := (TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients.{u}
  let s := C.liftCycles ((TopCat.toSSet.obj X).ιChainComplex simplex0) 0 (by simp) (by simp) ≫ C.homologyπ 0
  have hs : s ≫ ordinaryIntegralH0Augmentation.{u, u} X = 𝟙 _ := by
    rw [ordinaryIntegralH0Augmentation_eq]
    exact (TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε
      reducedSingularIntegralCoefficients.{u} simplex0
  exact epi_of_epi_fac hs

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero the punctured relative group vanishes whenever the puncture
has an actual point. The original inclusion is epi on H₀ because coefficient
sum is natural and is an isomorphism on the contractible ambient space. -/
theorem normedSpacePuncturedRelativeH0_isZero {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nonempty {x : E // x ≠ 0}] :
    CategoryTheory.Limits.IsZero
      ((singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))).homology
        reducedSingularIntegralCoefficients.{u} 0) := by
  let P := singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))
  let f := singularSubspaceInclusion (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))
  let a := ordinaryIntegralH0Augmentation.{u, u} (TopCat.of E)
  have : IsIso a := ordinaryIntegralH0Augmentation_isIso _
  have : Epi (ordinaryIntegralH0Augmentation.{u, u}
      (TopCat.of ({0}ᶜ : Set (TopCat.of E)))) := by
    change Epi (ordinaryIntegralH0Augmentation.{u, u} (TopCat.of {x : E // x ≠ 0}))
    exact ordinaryIntegralH0Augmentation_epi _
  have hnat := ordinaryIntegralH0Augmentation_naturality f
  have hcomp : Epi (SSet.homologyMap P.hom reducedSingularIntegralCoefficients.{u} 0 ≫ a) := by
    change Epi (SSet.homologyMap (TopCat.toSSet.map f)
      reducedSingularIntegralCoefficients.{u} 0 ≫ a)
    rw [hnat]
    infer_instance
  have : Epi (SSet.homologyMap P.hom reducedSingularIntegralCoefficients.{u} 0) :=
    (epi_comp_iff_of_isIso _ a).mp hcomp
  have hp : P.homologyπ reducedSingularIntegralCoefficients.{u} 0 = 0 :=
    CategoryTheory.Limits.zero_of_epi_comp _ (P.homologyMap_hom_homologyπ reducedSingularIntegralCoefficients.{u} 0)
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi (P.homologyπ reducedSingularIntegralCoefficients.{u} 0)).mp
  simp [hp]

/-- Both positive relative degrees, including degree one, use the same genuine
augmented reduced-sphere group. -/
def normedSpacePuncturedRelativeSphereIso {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    (singularSubspacePair (TopCat.of E) ({0}ᶜ : Set (TopCat.of E))).homology
      reducedSingularIntegralCoefficients.{u} (k + 1) ≅
    integralReducedSingularHomology (TopCat.of {x : E // ‖x‖ = 1}) k := by
  cases k with
  | zero => exact normedSpacePuncturedRelativeH1SphereIso
  | succ k => exact normedSpacePuncturedRelativePositiveSphereIso k

set_option backward.isDefEq.respectTransparency false in
/-- The native punctured-pair and subspace-pair constructors use exactly the
same inclusion, not merely isomorphic ambient spaces. -/
theorem singularPairFunctor_punctured_eq {X : Type u} [TopologicalSpace X] (x : X) :
    singularPairFunctor.obj (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X))) =
      singularSubspacePair (TopCat.of X) ({x}ᶜ : Set (TopCat.of X)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Excision and translation transport the relative group of the actual original
open neighborhood to the puncture at zero. The only admitted dependency is the
named singular excision theorem. -/
def euclideanOpenPuncturedHomologyIso {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) (k : ℕ) :
    (singularPairFunctor.obj
      (TopPair.ofSubset ({(⟨x, hx⟩ : U)}ᶜ : Set (TopCat.of U)))).homology
      reducedSingularIntegralCoefficients k ≅
    (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin n))))).homology
      reducedSingularIntegralCoefficients k := by
  let E := EuclideanSpace ℝ (Fin n)
  have hset : {b : U | b.val ∈ ({x}ᶜ : Set E)} =
      ({(⟨x, hx⟩ : U)}ᶜ : Set U) := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact not_congr (show b.val = x ↔ b = ⟨x, hx⟩ from
      ⟨fun he ↦ Subtype.ext he, fun he ↦ congrArg Subtype.val he⟩)
  have hsource : singularExcisionSource (TopCat.of E) {x}ᶜ U =
      singularPairFunctor.obj
        (TopPair.ofSubset ({(⟨x, hx⟩ : U)}ᶜ : Set (TopCat.of U))) := by
    rw [singularExcisionSource, hset, singularPairFunctor_punctured_eq]
  letI := euclidean_open_neighbourhood_excision U hU x hx
    reducedSingularIntegralCoefficients k
  let e₁ := asIso (SSetPair.homologyMap
    (singularExcisionInclusion (TopCat.of E) {x}ᶜ U)
      reducedSingularIntegralCoefficients k)
  let t : E ≃ₜ E := Homeomorph.addLeft (-x)
  have ht : t x = 0 := by simp [t]
  have e₂ := puncturedRelativeHomologyIso t x reducedSingularIntegralCoefficients k
  rw [ht, singularPairFunctor_punctured_eq, singularPairFunctor_punctured_eq] at e₂
  exact eqToIso (congrArg (fun P : SSetPair =>
    P.homology reducedSingularIntegralCoefficients k) hsource.symm) ≪≫ e₁ ≪≫ e₂

/-- The actual positive local relative group of an original Euclidean open set
is the reduced sphere group, through the proved native excision and radial maps. -/
def euclideanOpenPuncturedSphereIso {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) (k : ℕ) :
    (singularPairFunctor.obj
      (TopPair.ofSubset ({(⟨x, hx⟩ : U)}ᶜ : Set (TopCat.of U)))).homology
      reducedSingularIntegralCoefficients (k + 1) ≅
    integralReducedSingularHomology
      (TopCat.of {z : EuclideanSpace ℝ (Fin n) // ‖z‖ = 1}) k :=
  euclideanOpenPuncturedHomologyIso U hU x hx (k + 1) ≪≫
    normedSpacePuncturedRelativeSphereIso k

end

/-- Homeomorphic nonempty open subsets of real Euclidean spaces have equal dimensions.

The open sets carry their induced subtype topologies. Only a homeomorphism between those
subspaces is assumed. Both dimensions are natural numbers, so zero is included; the nonempty
hypotheses exclude the homeomorphisms between empty open sets in different dimensions.

Source: Hatcher, Algebraic Topology, Theorem 2.26 and proof, printed p. 126, and the integral
sphere calculation, Corollary 2.14, p. 114; literature/hatcher-at.pdf/.txt.

Complete natural-language proof of `topo.euclidean_open_dimension_invariance`:
1. Fix x in U and set y=h(x). Regard h and its inverse as homeomorphisms of pairs (U,U minus {x})
and (W,W minus {y}). Relative singular homology with coefficient group Z is functorial, so their
induced maps are inverse isomorphisms in every nonnegative degree. Use the actual relative
singular groups, not a hypothesized local-dimension label.

2. By excision, the inclusion (U,U minus {x}) into (R^m,R^m minus {x}) induces an isomorphism:
remove the closed set R^m minus U, whose closure omits x and lies inside the open subspace R^m
minus {x}. Translation by -x is a homeomorphism of this pair with (R^m,R^m minus {0}), so
functoriality transports its groups. Apply the same argument to W in R^n.

3. For m>0, contract R^m to 0 by (t,z)↦(1-t)z. On the punctured space use r(z)=z/||z|| and
H(t,z)=((1-t)+t/||z||)z. The scalar factor is positive for 0≤t≤1 and z≠0, so H remains punctured,
starts at z, ends on the unit sphere, and fixes that sphere. Continuity follows from the norm,
reciprocal off zero and scalar multiplication. This is a deformation retraction onto S^(m-1).
Homotopy invariance, applied to pairs with empty subspace, and the sphere profile show its
reduced integral homology is Z in degree m-1 and zero elsewhere. The punctured space is nonempty:
a coordinate unit vector is a point.

4. Use the ordinary long exact sequence of the singular pair, constructed from the short exact chain
sequence. R^m is contractible, hence its positive-degree homology vanishes. For k≥2 the adjacent
ambient groups vanish, so H_k(R^m,R^m minus {0};Z) is isomorphic to H_(k-1)(R^m minus {0};Z),
equal to reduced homology since k-1>0. At k=1 the sequence injects H_1(relative) into
H_0(punctured) with image the kernel of H_0(punctured)→H_0(R^m). Contracting the ambient space
identifies H_0(R^m) with Z; inclusion followed by contraction is the map to a point, so this
homomorphism is exactly augmentation and its kernel is reduced H_0(punctured). The map is onto
because a chosen punctured point gives the generator 1; exactness makes relative H_0 zero. Thus
the relative group is Z exactly in degree m and zero otherwise, including m=1 with the genuine
reduced H_0(S^0)=Z rather than ordinary H_0(S^0).

5. If m=0, R^0 is a single point and its punctured space is empty. In each nonnegative degree the
singular complex of a point is Z generated by its sole constant simplex. The differential from
degree k>0 is multiplication by the alternating sum of k+1 ones: it is zero for odd k and
identity for even k. Consequently H_0 is Z (the degree-one differential is zero); in each
positive odd degree the next differential is onto, and in each positive even degree the outgoing
differential is injective, so higher homology vanishes. The relative complex modulo the empty-
space zero complex is this same complex. This proves the dimension-zero profile without a
negative-dimensional sphere; treat n=0 identically.

6. Take degree k=m. The preceding profile makes H_m(U,U minus {x};Z) nonzero. Its homeomorphism-
induced isomorphism to H_m(W,W minus {y};Z) forces n=m by the corresponding n-dimensional
profile; Z is nonzero whereas the zero group has one element.
-/
theorem euclidean_open_dimension_invariance
    {m n : ℕ} (U : Set (EuclideanSpace ℝ (Fin m)))
    (W : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hW : IsOpen W) (hneU : U.Nonempty) (hneW : W.Nonempty)
    (h : ↥U ≃ₜ ↥W) : m = n := by
  by_cases hm : m = 0
  · exact hm.trans ((euclidean_open_dimension_zero_iff U W hU hW hneU hneW h).mp hm).symm
  by_cases hn : n = 0
  · exact ((euclidean_open_dimension_zero_iff U W hU hW hneU hneW h).mpr hn).trans hn.symm
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨x, hx⟩ := hneU
  let y : W := h ⟨x, hx⟩
  let e := (euclideanOpenPuncturedSphereIso U hU x hx m').symm ≪≫
    puncturedRelativeHomologyIso h (⟨x, hx⟩ : U)
      reducedSingularIntegralCoefficients (m' + 1) ≪≫
    euclideanOpenPuncturedSphereIso W hW y.val y.property m'
  have hpM := Topology.Homology.reduced_sphere_homology m'
  have hpN := Topology.Homology.reduced_sphere_homology n'
  by_contra hne
  have hmn : m' ≠ n' := by
    intro he
    exact hne (congrArg Nat.succ he)
  have hz := hpN.2.1 m' hmn
  obtain ⟨ec⟩ := hpM.1
  have hc : CategoryTheory.Limits.IsZero reducedSingularIntegralCoefficients :=
    hz.of_iso (ec.symm ≪≫ e)
  have hs := ModuleCat.isZero_iff_subsingleton.mp hc
  have hh : (ULift.up (0 : ℤ) : ULift.{0} ℤ) = ULift.up 1 :=
    @Subsingleton.elim _ hs _ _
  exact Int.zero_ne_one (congrArg ULift.down hh)

end HolomorphicAnosov








