import HolomorphicAnosov.Topology.DerivativePuncturedDiskHomotopy
import HolomorphicAnosov.Topology.Homology.EmptySupportSubsingleton
import HolomorphicAnosov.Topology.Homology.IntegralCompactSupportOrientation
import HolomorphicAnosov.Topology.Homology.IntegralSupportRestrictionNormalization
import HolomorphicAnosov.Topology.PositiveLinearComponentPath
import HolomorphicAnosov.Topology.PointNeighborhoodExcision
import HolomorphicAnosov.Topology.SingularSubspaceHomeomorphHomology
import HolomorphicAnosov.Topology.ClosedBallRelativeConnecting
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.DiskDegreeFibreFinite
import HolomorphicAnosov.Topology.DiskDegreeFibreCompactBuffer
import HolomorphicAnosov.Topology.SingularSubspaceHomologyHomotopy
import HolomorphicAnosov.Topology.EuclideanPositiveLocalCoordinate
import HolomorphicAnosov.Topology.EuclideanOpenDimensionInvariance
import Mathlib.Data.Set.Card

/-!
# Relative disk degree and the count of orientation-preserving preimages

Source: Hatcher, *Algebraic Topology*, §2.2, pp.134–136, especially Proposition 2.30;
relative homotopy invariance Proposition 2.19 p.118 and excision Theorem 2.20 p.119.
All relative groups and maps below are Mathlib's ordinary singular simplicial homology
with coefficient module ℤ. A disk degree is characterized by comparing the induced map
of g−w with the induced map of the positive translation z−center(B). The latter carries
the positive disk fundamental class to the positive local plane class; thus the equality
of homomorphisms is precisely the oriented-class definition, without choosing either
generator or assuming an unspecified degree theory.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Metric
open scoped ContDiff Classical
open HolomorphicAnosov.GoodPair

namespace HolomorphicAnosov.Topology

universe u

/-- The standard Euclidean real plane used in Hatcher's local-degree calculation, p.136. -/
abbrev DiskDegreePlane := EuclideanSpace ℝ (Fin 2)

/-- The actual singular simplicial pair of a space and its given subspace, using
Mathlib's singular functor and its preservation of monomorphisms. Source: Hatcher,
relative singular chains pp.115–118; Mathlib `TopCat.toSSet` and `SSetPair.of`. -/
def diskDegreeSingularPair (X : Type) [TopologicalSpace X] (A : Set X) : SSetPair := by
  let i : TopCat.of A ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  letI : Mono i := (TopCat.mono_iff_injective i).mpr Subtype.val_injective
  exact SSetPair.of (TopCat.toSSet.map i)

/-- The literal morphism of singular pairs induced by a continuous subspace-preserving
map. Source: Hatcher pp.115–118, and Mathlib `SSetPair.homMk`. -/
def diskDegreeSingularPairMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :
    diskDegreeSingularPair X A ⟶ diskDegreeSingularPair Y B := by
  let fA : C(A, B) := ⟨fun x ↦ ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  refine SSetPair.homMk (TopCat.toSSet.map (TopCat.ofHom fA))
    (TopCat.toSSet.map (TopCat.ofHom f)) ?_
  change TopCat.toSSet.map (TopCat.ofHom fA) ≫ TopCat.toSSet.map _ =
    TopCat.toSSet.map _ ≫ TopCat.toSSet.map (TopCat.ofHom f)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Ordinary integral relative H₂, exactly the cokernel singular-chain construction.
Source: Hatcher pp.115–118; Mathlib `SSetPair.homology`. -/
abbrev diskDegreeRelativeH2 (X : Type) [TopologicalSpace X] (A : Set X) :=
  (diskDegreeSingularPair X A).homology (ModuleCat.of ℤ ℤ) 2

/-- The induced integral relative H₂ map of the actual pair morphism.
Source: Hatcher pp.115–118; Mathlib `SSetPair.homologyMap`. -/
def diskDegreeRelativeH2Map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :
    diskDegreeRelativeH2 X A ⟶ diskDegreeRelativeH2 Y B :=
  SSetPair.homologyMap (diskDegreeSingularPairMap A B f hf) (ModuleCat.of ℤ ℤ) 2

/-- Functorial composition for the literal disk-degree relative maps. -/
theorem diskDegreeRelativeH2Map_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set X) (B : Set Y) (D : Set Z) (f : C(X, Y)) (g : C(Y, Z))
    (hf : MapsTo f A B) (hg : MapsTo g B D) :
    diskDegreeRelativeH2Map A B f hf ≫ diskDegreeRelativeH2Map B D g hg =
      diskDegreeRelativeH2Map A D (g.comp f) (hg.comp hf) := by
  unfold diskDegreeRelativeH2Map
  rw [← SSetPair.homologyMap_comp]
  congr 1

/-- Composition with an explicitly identified continuous map. -/
theorem diskDegreeRelativeH2Map_comp_eq
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set X) (B : Set Y) (D : Set Z) (f : C(X, Y)) (g : C(Y, Z))
    (h : C(X, Z)) (hf : MapsTo f A B) (hg : MapsTo g B D) (hh : MapsTo h A D)
    (he : g.comp f = h) :
    diskDegreeRelativeH2Map A B f hf ≫ diskDegreeRelativeH2Map B D g hg =
      diskDegreeRelativeH2Map A D h hh := by
  subst h
  exact diskDegreeRelativeH2Map_comp A B D f g hf hg

/-- Threefold composition with an explicitly identified continuous map. -/
theorem diskDegreeRelativeH2Map_comp_three_eq
    {X Y Z W : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W]
    (A : Set X) (B : Set Y) (D : Set Z) (E : Set W)
    (f : C(X, Y)) (g : C(Y, Z)) (h : C(Z, W)) (k : C(X, W))
    (hf : MapsTo f A B) (hg : MapsTo g B D) (hh : MapsTo h D E) (hk : MapsTo k A E)
    (he : (h.comp g).comp f = k) :
    diskDegreeRelativeH2Map A B f hf ≫ diskDegreeRelativeH2Map B D g hg ≫
      diskDegreeRelativeH2Map D E h hh = diskDegreeRelativeH2Map A E k hk := by
  rw [diskDegreeRelativeH2Map_comp]
  exact diskDegreeRelativeH2Map_comp_eq A B E f (h.comp g) k hf (hh.comp hg) hk he

/-- A pair map that sends its entire source into the target subspace induces zero.
It factors through the pair of the source with itself, whose relative homology is zero. -/
theorem diskDegreeRelativeH2Map_eq_zero_of_range
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B)
    (hwhole : ∀ x, f x ∈ B) : diskDegreeRelativeH2Map A B f hf = 0 := by
  have hs : Subsingleton (diskDegreeRelativeH2 X (univ : Set X)) := by
    have hh := support_empty_subsingleton_public (TopCat.of X) (ModuleCat.of ℤ ℤ) 2
    change Subsingleton (diskDegreeRelativeH2 X (∅ : Set X)ᶜ) at hh
    simpa only [compl_empty] using hh
  let j := diskDegreeRelativeH2Map A univ (ContinuousMap.id X) (fun _ _ ↦ trivial)
  let k := diskDegreeRelativeH2Map univ B f (fun x _ ↦ hwhole x)
  have he : j ≫ k = diskDegreeRelativeH2Map A B f hf :=
    diskDegreeRelativeH2Map_comp A univ B (ContinuousMap.id X) f _ _
  rw [← he]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change k.hom (j.hom x) = 0
  rw [hs.elim (j.hom x) 0, map_zero]

/-!
The custom disk-degree wrappers above are literal aliases for Mathlib's native
singular-subspace pair construction.  Naming this identity makes the available
excision and naturality theorems usable directly at a `HasDiskDegree` map: no
new equivalence or choice of singular-chain model is hidden here.  Source:
Hatcher pp.115–118 and Mathlib `singularSubspacePair`/`singularSubspacePairMap`.
-/
theorem diskDegreeSingularPair_eq_native (X : Type) [TopologicalSpace X] (A : Set X) :
    diskDegreeSingularPair X A = singularSubspacePair (TopCat.of X) A := by
  rfl

theorem diskDegreeSingularPairMap_eq_native
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :
    diskDegreeSingularPairMap A B f hf =
      singularSubspacePairMap (TopCat.ofHom f) A B hf := by
  rfl

theorem diskDegreeRelativeH2Map_eq_native
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :
    diskDegreeRelativeH2Map A B f hf =
      SSetPair.homologyMap
        (singularSubspacePairMap (TopCat.ofHom f) A B hf)
        (ModuleCat.of ℤ ℤ) 2 := by
  rfl

/-!
The standard local excision instance needed by Hatcher's degree diagram is
available directly for a punctured plane and an open ball.  This theorem keeps
the exact native source map visible: its source is the ball together with the
punctured ball, and its target is the punctured plane pair.  Source: Hatcher,
Theorem 2.20 and Proposition 2.30, pp.119 and 136; the proof instantiates the
project's barycentric-subdivision excision theorem with the cover by the
punctured plane and the ball.
-/
theorem diskDegree_puncturedPlane_excision_ball_homology_iso
    (r : ℝ) (hr : 0 < r) :
    IsIso (SSetPair.homologyMap
      (singularExcisionInclusion (TopCat.of DiskDegreePlane) ({0}ᶜ)
        (ball (0 : DiskDegreePlane) r)) (ModuleCat.of ℤ ℤ) 2) := by
  let A : Set DiskDegreePlane := ({0}ᶜ)
  have hZA : (ball (0 : DiskDegreePlane) r)ᶜ ⊆ A := by
    intro x hx hx0
    apply hx
    rw [← hx0]
    exact mem_ball_self hr
  have hcl : closure (ball (0 : DiskDegreePlane) r)ᶜ ⊆ interior A := by
    dsimp [A]
    rw [closure_compl, IsOpen.interior_eq isOpen_ball,
      IsOpen.interior_eq isOpen_compl_singleton]
    exact hZA
  have hEx := singular_homology_excision_barycentric_subdivision
  have hi := (hEx.2.2.2.2 (TopCat.of DiskDegreePlane) A
    (ball (0 : DiskDegreePlane) r)ᶜ hZA hcl (ModuleCat.of ℤ ℤ)).2 2
  have hball : (ball (0 : DiskDegreePlane) r)ᶜᶜ = ball (0 : DiskDegreePlane) r := by
    simp
  rw [hball] at hi
  simpa only [A] using hi

/-- The boundary as a subspace of the actual closed disk, not of a replacement carrier.
Source: the disk pair in Hatcher's local relative-degree argument, p.136. -/
def diskDegreeBoundary (c : DiskDegreePlane) (r : ℝ) : Set (closedBall c r) :=
  {z | dist (z : DiskDegreePlane) c = r}

/-- Restriction of a continuous-on-disk map to that closed disk. Source: Hatcher p.136. -/
def diskDegreeRestriction (c : DiskDegreePlane) (r : ℝ) (f : DiskDegreePlane → DiskDegreePlane)
    (hf : ContinuousOn f (closedBall c r)) : C(closedBall c r, DiskDegreePlane) :=
  ⟨fun z ↦ f z, hf.domRestrict⟩

/-- The integer coefficient on the oriented fundamental class, expressed without
arbitrary generator data: compare g−w with the positive translation z−c into the
punctured plane pair. Both send boundary into the punctured plane, and z−c induces
an orientation-compatible isomorphism for r>0. Source: Hatcher pp.134–136 and the
relative pair/excision construction pp.118–119. -/
def HasDiskDegree (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (g : C(closedBall c r, DiskDegreePlane)) (w : DiskDegreePlane)
    (hboundary : ∀ z : closedBall c r, dist (z : DiskDegreePlane) c = r → g z ≠ w)
    (d : ℤ) : Prop :=
  diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane)
    ⟨fun z ↦ g z - w, g.continuous.sub continuous_const⟩
    (by intro z hz; exact sub_ne_zero.mpr (hboundary z hz)) =
  d • diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane)
    ⟨fun z ↦ (z : DiskDegreePlane) - c, continuous_subtype_val.sub continuous_const⟩
    (by
      intro z hz
      change (z : DiskDegreePlane) - c ≠ 0
      intro hzero
      have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
      have hrad : r = 0 := by simpa [hzc] using hz.symm
      exact (ne_of_gt hr) hrad)

/-- Boundary-avoiding homotopies on the same closed disk, with no differentiability
condition on the homotopy. Source: Hatcher Proposition 2.19 p.118 and §2.2 p.134(c). -/
def BoundaryAvoidingDiskHomotopy (c : DiskDegreePlane) (r : ℝ)
    (f g : C(closedBall c r, DiskDegreePlane)) (w : DiskDegreePlane) : Prop :=
  ∃ H : ContinuousMap.Homotopy f g,
    ∀ (t : unitInterval) (z : closedBall c r),
      dist (z : DiskDegreePlane) c = r → H (t, z) ≠ w

/-- The restriction of an open-set homeomorphism to the given closed disk.
Source: the homeomorphic local-degree case in Hatcher p.136. -/
def diskDegreeHomeomorphRestriction (c : DiskDegreePlane) (r : ℝ)
    (V W : Set DiskDegreePlane) (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V) :
    C(closedBall c r, DiskDegreePlane) :=
  ⟨fun z ↦ (h ⟨(z : DiskDegreePlane), hBV z.property⟩ : DiskDegreePlane),
    continuous_subtype_val.comp (h.continuous.comp
      (continuous_subtype_val.subtype_mk (fun z ↦ hBV z.property)))⟩

/-!
The two contracts below isolate the genuine local-degree work in Hatcher's
Proposition 2.30. The finite fibre and boundary buffer feed the local-degree
sum proved below.
-/

/--
Uniqueness of a disk-degree coefficient once the positive translation class is
known to have injective integer multiples.

This is the purely algebraic part of the generator argument.  If two maps in
`HasDiskDegree` have the same displacement map and the scalar-multiplication
map `d ↦ d • T` on the translation representative is injective, equality of
the two displayed homology morphisms forces equality of their coefficients.
The geometric proof that the translation representative has this injectivity
is the separate local-generator/excision obligation above.
-/
theorem disk_degree_has_degree_unique_of_translation_injective
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (g : C(closedBall c r, DiskDegreePlane)) (w : DiskDegreePlane)
    (hboundary : ∀ z : closedBall c r,
      dist (z : DiskDegreePlane) c = r → g z ≠ w)
    (hT : Function.Injective (fun e : ℤ ↦ e •
      diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (z : DiskDegreePlane) - c,
          continuous_subtype_val.sub continuous_const⟩
        (by
          intro z hz
          change (z : DiskDegreePlane) - c ≠ 0
          intro hzero
          have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
          have hrad : r = 0 := by simpa [hzc] using hz.symm
          exact (ne_of_gt hr) hrad))) :
    ∀ d e : ℤ, HasDiskDegree c r hr g w hboundary d →
      HasDiskDegree c r hr g w hboundary e → d = e := by
  intro d e hd he
  apply hT
  change diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ g z - w, g.continuous.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr (hboundary z hz)) =
      d • diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (z : DiskDegreePlane) - c,
          continuous_subtype_val.sub continuous_const⟩
        (by
          intro z hz
          change (z : DiskDegreePlane) - c ≠ 0
          intro hzero
          have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
          have hrad : r = 0 := by simpa [hzc] using hz.symm
          exact (ne_of_gt hr) hrad) at hd
  change diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ g z - w, g.continuous.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr (hboundary z hz)) =
      e • diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (z : DiskDegreePlane) - c,
          continuous_subtype_val.sub continuous_const⟩
        (by
          intro z hz
          change (z : DiskDegreePlane) - c ≠ 0
          intro hzero
          have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
          have hrad : r = 0 := by simpa [hzc] using hz.symm
          exact (ne_of_gt hr) hrad) at he
  exact hd.symm.trans he

/-!
The scalar cancellation used in the generator argument does not require a
global torsion-free instance on the relative homology object.  It is enough to
have an additive coordinate that sends the chosen translation class to `1`.
This is the ordinary integral version of the generator cancellation in
Hatcher, pp. 134--136.
-/
theorem disk_degree_integer_multiples_injective_of_coordinate
    {M : Type*} [AddCommGroup M] (x : M) (κ : M →+ ℤ)
    (hκ : κ x = 1) :
    Function.Injective (fun e : ℤ ↦ e • x) := by
  intro d e hde
  have hκde := congrArg κ hde
  simpa [map_zsmul, hκ] using hκde

/-!
Changing the coefficient module by an isomorphism changes each singular
relative homology group by an isomorphism.  This is the chain-level adapter
needed when comparing Mathlib's universe-lifted singular coefficients with the
literal `ModuleCat.of ℤ ℤ` coefficients in this file.
-/
theorem disk_degree_relative_coefficient_map_isIso
    {P : SSetPair.{u}} {R Q : ModuleCat.{u} ℤ}
    (e : R ≅ Q) (n : ℕ) :
    IsIso (singularRelativeCoefficientMap P e.hom n) := by
  let F := (SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map e.hom
  let h : P.chainComplex R ⟶ P.chainComplex Q := F.app P
  let hi := HomologicalComplex.Hom.isoOfComponents (fun i ↦ asIso (h.f i)) (by
    intro i j hij
    change h.f i ≫ (P.chainComplex Q).d i j =
      (P.chainComplex R).d i j ≫ h.f j
    exact h.comm i j)
  have : IsIso (HomologicalComplex.homologyMap h n) := by
    exact (HomologicalComplex.homologyMapIso hi n).isIso_hom
  change IsIso (HomologicalComplex.homologyMap h n)
  exact inferInstance

/-!
The ordinary integral local group in the plane is also infinite cyclic: apply
the coefficient-change isomorphism above to the existing universe-lifted
positive local coordinate.  This only transports a coordinate; it does not
identify the disk-to-plane map with its positive generator.
-/
theorem disk_degree_ordinary_plane_local_homology_coordinate :
    Nonempty (↥((singularSubspacePair
      (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane)).homology
      (ModuleCat.of ℤ ℤ) 2) ≃ₗ[ℤ] ℤ) := by
  let ec : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ (ULift ℤ) :=
    ULift.moduleEquiv.symm.toModuleIso
  have : IsIso (singularRelativeCoefficientMap
      (singularSubspacePair (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane))
      ec.hom 2) := disk_degree_relative_coefficient_map_isIso ec 2
  let hc := asIso (singularRelativeCoefficientMap
      (singularSubspacePair (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane))
      ec.hom 2)
  let hl : ↥((singularSubspacePair
      (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane)).homology
      (ModuleCat.of ℤ ℤ) 2) ≃ₗ[ℤ]
      ↥((singularSubspacePair
        (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane)).homology
        singularIntegralCoefficients 2) := hc.toLinearEquiv
  exact ⟨hl.trans (euclideanPositiveLocalCoordinate 2)⟩

/-- An integral linear automorphism has sign `+1` or `-1` on the unit class.
Source: the two automorphisms of the oriented local group `ℤ` in Hatcher,
*Algebraic Topology*, §2.2, pp.134--136. -/
theorem disk_degree_integer_linear_equiv_sign (e : ℤ ≃ₗ[ℤ] ℤ) :
    e 1 = 1 ∨ e 1 = -1 := by
  have hprod : e 1 * e.symm 1 = 1 := by
    have h := e.symm_apply_apply (1 : ℤ)
    have hs := e.symm.map_smul (e 1) (1 : ℤ)
    rw [smul_eq_mul] at hs
    simp only [mul_one] at hs
    rw [smul_eq_mul] at hs
    exact hs.symm.trans h
  have hu : IsUnit (e 1) := by
    rw [isUnit_iff_exists_inv]
    exact ⟨e.symm 1, by simpa [mul_comm] using hprod⟩
  rcases Int.isUnit_iff.mp hu with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- A homeomorphism restriction has a unique interior preimage of the target.
Source: Hatcher, *Algebraic Topology*, §2.2 p.136, where the local
homeomorphism branch is centered at its unique preimage. -/
theorem disk_degree_homeomorph_restriction_unique_preimage
    (c : DiskDegreePlane) (r : ℝ) (_hr : 0 < r)
    (w : DiskDegreePlane) (V W : Set DiskDegreePlane)
    (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V)
    (hpre : ∃ z : V, (z : DiskDegreePlane) ∈ ball c r ∧
      (h z : DiskDegreePlane) = w) :
    ∃! z : closedBall c r,
      (z : DiskDegreePlane) ∈ ball c r ∧
        diskDegreeHomeomorphRestriction c r V W h hBV z = w := by
  obtain ⟨z, hzball, hzw⟩ := hpre
  let zB : closedBall c r := ⟨(z : DiskDegreePlane),
    Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hzball))⟩
  refine ⟨zB, ?_, ?_⟩
  · exact ⟨hzball, hzw⟩
  · intro y hy
    have hyV : (⟨(y : DiskDegreePlane), hBV y.property⟩ : V) = z := by
      apply h.injective
      apply Subtype.ext
      exact hy.2.trans hzw.symm
    apply Subtype.ext
    exact congrArg (fun q : V ↦ (q : DiskDegreePlane)) hyV

/-- Translation identifies the metric boundary of a disk with the centered
radius sphere.  Source: Hatcher, *Algebraic Topology*, §2.2 pp.116--119;
this is the affine chart used to transport the disk boundary orientation. -/
theorem disk_degree_boundary_translation_homeomorph
    (c : DiskDegreePlane) (r : ℝ) :
    Nonempty (({z : closedBall c r // dist (z : DiskDegreePlane) c = r} ≃ₜ
      {u : DiskDegreePlane // ‖u‖ = r})) := by
  let A : Type := {z : closedBall c r // dist (z : DiskDegreePlane) c = r}
  let B : Type := {u : DiskDegreePlane // ‖u‖ = r}
  change Nonempty (A ≃ₜ B)
  let f0 : A → DiskDegreePlane := fun z ↦ (z.1 : DiskDegreePlane) - c
  have hvalA : Continuous (fun z : A ↦ (z.1 : DiskDegreePlane)) := by
    exact continuous_subtype_val.comp continuous_subtype_val
  have hf0 : Continuous f0 := by
    dsimp [f0]
    exact hvalA.sub continuous_const
  have hnorm : ∀ z : A, ‖f0 z‖ = r := by
    intro z
    dsimp [f0]
    rw [← dist_eq_norm]
    exact z.2
  let f : A → B := fun z ↦ ⟨f0 z, hnorm z⟩
  have hf : Continuous f := by
    exact hf0.subtype_mk hnorm
  let g0 : B → DiskDegreePlane := fun u ↦ c + (u.1 : DiskDegreePlane)
  have hg0 : Continuous g0 := by
    dsimp [g0]
    exact continuous_const.add continuous_subtype_val
  have hclosed : ∀ u : B, g0 u ∈ closedBall c r := by
    intro u
    apply mem_closedBall.mpr
    calc
      dist (g0 u) c = ‖(u.1 : DiskDegreePlane)‖ := by
        dsimp [g0]
        rw [dist_eq_norm]
        simp [sub_eq_add_neg, add_assoc]
      _ ≤ r := le_of_eq u.2
  let g1 : B → closedBall c r := fun u ↦ ⟨g0 u, hclosed u⟩
  have hg1 : Continuous g1 := by
    exact hg0.subtype_mk hclosed
  have hsphere : ∀ u : B, dist (g0 u) c = r := by
    intro u
    calc
      dist (g0 u) c = ‖(u.1 : DiskDegreePlane)‖ := by
        dsimp [g0]
        rw [dist_eq_norm]
        simp [sub_eq_add_neg, add_assoc]
      _ = r := u.2
  let g : B → A := fun u ↦ ⟨g1 u, hsphere u⟩
  have hg : Continuous g := by
    exact hg1.subtype_mk hsphere
  refine ⟨Homeomorph.mk
    { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ } hf hg⟩
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    dsimp [f, g, g1, g0, f0]
    simp [sub_eq_add_neg]
  · intro u
    apply Subtype.ext
    dsimp [f, g, g1, g0, f0]
    simp [sub_eq_add_neg]

/-!
The closed disk relative group is the remaining source-level generator input.
It is kept separate from the local degree theorem so the latter can use the
same fundamental-class coordinate for both normalization and uniqueness.
-/
/-- The ordinary integral relative H₂ of a closed Euclidean disk modulo its
boundary is infinite cyclic.

Source: Hatcher, *Algebraic Topology*, §2.2 pp.116--119 and pp.134--136.
The disk contracts, the boundary is its sphere, and the relative exact
sequence identifies the connecting map with the oriented boundary generator;
the integral sphere calculation gives a free rank-one group. -/
theorem disk_degree_closed_ball_boundary_coordinate
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r) :
    Nonempty (↥((diskDegreeSingularPair (closedBall c r)
      (diskDegreeBoundary c r)).homology (ModuleCat.of ℤ ℤ) 2) ≃ₗ[ℤ] ℤ) := by
  let P := singularSubspacePair (TopCat.of (closedBall c r)) (diskDegreeBoundary c r)
  let A : Type := {z : closedBall c r // dist (z : DiskDegreePlane) c = r}
  let B : Type := {u : DiskDegreePlane // ‖u‖ = r}
  have htr : Nonempty (A ≃ₜ B) := disk_degree_boundary_translation_homeomorph c r
  obtain ⟨eAB⟩ := htr
  let e1 := HolomorphicAnosov.Topology.Homology.reducedHomologyHomeomorphIso eAB 1
  have hconn : IsIso (P.homologyδ (ModuleCat.of ℤ ℤ) 2 1 (by omega)) :=
    closedBall_relative_connecting_isIso c r hr.le (diskDegreeBoundary c r)
      (ModuleCat.of ℤ ℤ) 0
  have h21 : 1 + 1 = 2 := by omega
  let δ := P.homologyδ (ModuleCat.of ℤ ℤ) 2 1 h21
  have : IsIso δ := by simpa [δ] using hconn
  let d := asIso δ
  let redA := HolomorphicAnosov.Topology.Homology.integralReducedPositiveOrdinaryIso
    (TopCat.of A) 0
  let redB := HolomorphicAnosov.Topology.Homology.integralReducedPositiveOrdinaryIso
    (TopCat.of B) 0
  have hs := (HolomorphicAnosov.Topology.Homology.reduced_sphere_homology 1).2.2 r hr
  obtain ⟨sB⟩ := hs.1
  let ec : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ (ULift ℤ) :=
    ULift.moduleEquiv.symm.toModuleIso
  let F := (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map ec.hom
  let hF := F.app (TopCat.toSSet.obj (TopCat.of B))
  let hi := HomologicalComplex.Hom.isoOfComponents (fun i ↦ asIso (hF.f i)) (by
    intro i j hij
    exact hF.comm i j)
  have : IsIso (HomologicalComplex.homologyMap hF 1) :=
    (HomologicalComplex.homologyMapIso hi 1).isIso_hom
  let cb :
      ((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of ℤ ℤ)).homology 1 ≅
      ((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of ℤ (ULift ℤ))).homology 1 :=
    asIso (HomologicalComplex.homologyMap hF 1)
  let redB' : integralReducedSingularHomology (TopCat.of B) 1 ≅
      ((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of ℤ (ULift ℤ))).homology 1 := by
    simpa using redB
  let redA' : integralReducedSingularHomology (TopCat.of A) 1 ≅
      ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℤ (ULift ℤ))).homology 1 := by
    simpa using redA
  let eu : ModuleCat.of ℤ (ULift ℤ) ≅ ModuleCat.of ℤ ℤ :=
    ULift.moduleEquiv.toModuleIso
  let linB : ↥(((TopCat.toSSet.obj (TopCat.of B)).chainComplex
      (ModuleCat.of ℤ ℤ)).homology 1) ≃ₗ[ℤ] ℤ :=
    (cb.toLinearEquiv.trans redB'.symm.toLinearEquiv).trans
      (sB.toLinearEquiv.trans eu.toLinearEquiv)
  let FA := (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map ec.hom
  let hFA := FA.app (TopCat.toSSet.obj (TopCat.of A))
  let hiA := HomologicalComplex.Hom.isoOfComponents (fun i ↦ asIso (hFA.f i)) (by
    intro i j hij
    exact hFA.comm i j)
  have : IsIso (HomologicalComplex.homologyMap hFA 1) :=
    (HomologicalComplex.homologyMapIso hiA 1).isIso_hom
  let ca :
      ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℤ ℤ)).homology 1 ≅
      ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℤ (ULift ℤ))).homology 1 :=
    asIso (HomologicalComplex.homologyMap hFA 1)
  let linA : ↥(((TopCat.toSSet.obj (TopCat.of A)).chainComplex
      (ModuleCat.of ℤ ℤ)).homology 1) ≃ₗ[ℤ] ℤ :=
    (ca.toLinearEquiv.trans redA'.symm.toLinearEquiv).trans
      ((e1.toLinearEquiv.trans redB'.toLinearEquiv).trans
        (cb.symm.toLinearEquiv.trans linB))
  exact ⟨d.toLinearEquiv.trans linA⟩

/-!
The remaining local-orientation bridge is kept as separate source contracts.
The first two contracts are the excision/naturality isomorphisms; the unit
conclusion below is then a formal rank-one calculation.
-/

/-- Source contract for the native positive translation relative map.
Source: Hatcher, *Algebraic Topology*, §2.2, pp.134--136: affine pair
translation, excision, and connecting-map naturality identify this map with an
integral linear equivalence. -/
theorem disk_degree_positive_translation_native_equiv
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r) :
    Nonempty (↥((diskDegreeSingularPair (closedBall c r)
      (diskDegreeBoundary c r)).homology (ModuleCat.of ℤ ℤ) 2) ≃ₗ[ℤ]
      ↥((singularSubspacePair (TopCat.of DiskDegreePlane)
        ({0}ᶜ : Set DiskDegreePlane)).homology (ModuleCat.of ℤ ℤ) 2)) := by
  obtain ⟨eS⟩ := disk_degree_closed_ball_boundary_coordinate c r hr
  obtain ⟨eT⟩ := disk_degree_ordinary_plane_local_homology_coordinate
  exact ⟨eS.trans eT.symm⟩

/-- Lower-level affine-excision source contract for the native positive translation map.
Source: Hatcher, *Algebraic Topology*, §2.2, pp.134--136. -/
theorem disk_degree_homotopy_equiv_homologyMap_isIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (R : ModuleCat ℤ) (n : ℕ) :
    IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom e.toFun)) R n) := by
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  let F := SSet.homologyMap (TopCat.toSSet.map f) R n
  let G := SSet.homologyMap (TopCat.toSSet.map g) R n
  have hfg : F ≫ G = 𝟙 _ := by
    rw [← SSet.homologyMap_comp]
    change SSet.homologyMap (TopCat.toSSet.map (f ≫ g)) R n = _
    have htop : f ≫ g = TopCat.ofHom (e.invFun.comp e.toFun) := by rfl
    rw [htop]
    obtain ⟨h⟩ := e.left_inv
    let hh : TopCat.Homotopy (TopCat.ofHom (e.invFun.comp e.toFun)) (𝟙 _) := h
    have hhom := SSet.Homotopy.congr_homologyMap (hh.toSSet) R n
    simpa only [TopCat.toSSet.map_id, SSet.homologyMap_id] using hhom
  have hgf : G ≫ F = 𝟙 _ := by
    rw [← SSet.homologyMap_comp]
    change SSet.homologyMap (TopCat.toSSet.map (g ≫ f)) R n = _
    have htop : g ≫ f = TopCat.ofHom (e.toFun.comp e.invFun) := by rfl
    rw [htop]
    obtain ⟨h⟩ := e.right_inv
    let hh : TopCat.Homotopy (TopCat.ofHom (e.toFun.comp e.invFun)) (𝟙 _) := h
    have hhom := SSet.Homotopy.congr_homologyMap (hh.toSSet) R n
    simpa only [TopCat.toSSet.map_id, SSet.homologyMap_id] using hhom
  exact ⟨⟨G, hfg, hgf⟩⟩

/-- Radial scaling identifies the metric sphere of radius `r` with the unit sphere. -/
def diskDegreeSphereScale (r : ℝ) (hr : 0 < r) :
    {u : DiskDegreePlane // ‖u‖ = r} ≃ₜ {u : DiskDegreePlane // ‖u‖ = 1} := by
  let h := Homeomorph.smulOfNeZero (α := DiskDegreePlane) (r⁻¹) (inv_ne_zero hr.ne')
  apply h.subtype
  intro u
  change ‖u‖ = r ↔ ‖r⁻¹ • u‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  constructor
  · intro hu; rw [hu]; field_simp
  · intro hu
    calc
      ‖u‖ = r * (r⁻¹ * ‖u‖) := by field_simp [hr.ne']
      _ = r * 1 := by rw [hu]
      _ = r := by simp

/-- Ambient multiplication by a positive scalar preserves the punctured plane. -/
def diskDegreePuncturedAmbientScale (r : ℝ) (hr : 0 < r) :
    {u : DiskDegreePlane // u ≠ 0} ≃ₜ {u : DiskDegreePlane // u ≠ 0} := by
  let h := Homeomorph.smulOfNeZero (α := DiskDegreePlane) r hr.ne'
  apply h.subtype
  intro x
  change x ≠ 0 ↔ r • x ≠ 0
  simp [hr.ne']

/-- The inclusion of a positive-radius sphere into the punctured plane. -/
def diskDegreeBoundarySphereInclusion (r : ℝ) (hr : 0 < r) :
    C({u : DiskDegreePlane // ‖u‖ = r}, {x : DiskDegreePlane // x ≠ 0}) :=
  { toFun := fun (u : {u : DiskDegreePlane // ‖u‖ = r}) =>
      ⟨u.1, by
        intro hu
        have h := u.property
        rw [hu] at h
        exact (ne_of_gt hr) (h.symm.trans norm_zero)⟩
    continuous_toFun := continuous_subtype_val.subtype_mk (fun u => by
      intro hu
      have h := u.property
      rw [hu] at h
      exact (ne_of_gt hr) (h.symm.trans norm_zero)) }

/-- The radius-r sphere inclusion into the punctured plane induces an ordinary
singular H₁ isomorphism, via radial normalization and ambient scaling. -/
theorem disk_degree_radius_sphere_inclusion_homologyMap_isIso
    (r : ℝ) (hr : 0 < r) :
    IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (diskDegreeBoundarySphereInclusion r hr)))
      (ModuleCat.of ℤ ℤ) 1) := by
  let e1 := (diskDegreeSphereScale r hr).toHomotopyEquiv
  let e2 := (HolomorphicAnosov.puncturedSphereHomotopyEquiv
    (E := DiskDegreePlane)).symm
  let e3 := (diskDegreePuncturedAmbientScale r hr).toHomotopyEquiv
  let e := e1.trans (e2.trans e3)
  have hi := disk_degree_homotopy_equiv_homologyMap_isIso e (ModuleCat.of ℤ ℤ) 1
  have he : diskDegreeBoundarySphereInclusion r hr = e.toFun := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    dsimp [e, e1, e2, e3, diskDegreeSphereScale, diskDegreePuncturedAmbientScale,
      diskDegreeBoundarySphereInclusion, HolomorphicAnosov.puncturedSphereHomotopyEquiv,
      HolomorphicAnosov.puncturedRadialSphereMap, HolomorphicAnosov.spherePuncturedInclusion]
    change (u : DiskDegreePlane) = r • (r⁻¹ • (u : DiskDegreePlane))
    rw [smul_smul]
    simp [hr.ne']
  rw [he]
  exact hi

/-- The displayed affine translation map sits in the native connecting-map
diagram for the disk pair and the punctured-plane pair.  This is the exact
relative naturality equation used by the remaining affine-excision contract.
Source: Hatcher, *Algebraic Topology*, Theorem 2.16, pp.116--118. -/
theorem disk_degree_positive_translation_connecting_naturality
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r) :
    let f : singularSubspacePair (TopCat.of (closedBall c r))
          (diskDegreeBoundary c r) ⟶
        singularSubspacePair (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane) :=
      singularSubspacePairMap
        (TopCat.ofHom ⟨fun z : closedBall c r ↦ (z : DiskDegreePlane) - c,
          continuous_subtype_val.sub continuous_const⟩)
        (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane)
        (fun z hz ↦ by
          change (z : DiskDegreePlane) - c ≠ 0
          intro hzero
          have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
          have hrad : r = 0 := by simpa [hzc] using hz.symm
          exact (ne_of_gt hr) hrad)
    let R : ModuleCat ℤ := ModuleCat.of ℤ ℤ
    (singularSubspacePair (TopCat.of (closedBall c r))
        (diskDegreeBoundary c r)).homologyδ R 2 1 (by simp) ≫
      HomologicalComplex.homologyMap
        (HolomorphicAnosov.GoodPair.pairChainShortComplexMap f R).τ₁ 1 =
    HomologicalComplex.homologyMap
        (HolomorphicAnosov.GoodPair.pairChainShortComplexMap f R).τ₃ 2 ≫
      (singularSubspacePair (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane)).homologyδ
        R 2 1 (by simp) := by
  dsimp only
  exact HolomorphicAnosov.GoodPair.pair_connecting_naturality _ _ 0

/-- Explicit translation homeomorphism from a disk boundary to the centered sphere. -/
def diskDegreeBoundaryTranslationExplicit (c : DiskDegreePlane) (r : ℝ) :
    ({z : closedBall c r // dist (z : DiskDegreePlane) c = r} ≃ₜ
      {u : DiskDegreePlane // ‖u‖ = r}) := by
  let A : Type := {z : closedBall c r // dist (z : DiskDegreePlane) c = r}
  let B : Type := {u : DiskDegreePlane // ‖u‖ = r}
  let f0 : A → DiskDegreePlane := fun z ↦ (z.1 : DiskDegreePlane) - c
  have hvalA : Continuous (fun z : A ↦ (z.1 : DiskDegreePlane)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hf0 : Continuous f0 := by
    dsimp [f0]
    exact hvalA.sub continuous_const
  have hnorm : ∀ z : A, ‖f0 z‖ = r := by
    intro z
    dsimp [f0]
    rw [← dist_eq_norm]
    exact z.2
  let f : A → B := fun z ↦ ⟨f0 z, hnorm z⟩
  have hf : Continuous f := hf0.subtype_mk hnorm
  let g0 : B → DiskDegreePlane := fun u ↦ c + (u.1 : DiskDegreePlane)
  have hg0 : Continuous g0 := by
    dsimp [g0]
    exact continuous_const.add continuous_subtype_val
  have hclosed : ∀ u : B, g0 u ∈ closedBall c r := by
    intro u
    apply mem_closedBall.mpr
    calc
      dist (g0 u) c = ‖(u.1 : DiskDegreePlane)‖ := by
        dsimp [g0]
        rw [dist_eq_norm]
        simp [sub_eq_add_neg, add_assoc]
      _ ≤ r := le_of_eq u.2
  let g1 : B → closedBall c r := fun u ↦ ⟨g0 u, hclosed u⟩
  have hg1 : Continuous g1 := hg0.subtype_mk hclosed
  have hsphere : ∀ u : B, dist (g0 u) c = r := by
    intro u
    calc
      dist (g0 u) c = ‖(u.1 : DiskDegreePlane)‖ := by
        dsimp [g0]
        rw [dist_eq_norm]
        simp [sub_eq_add_neg, add_assoc]
      _ = r := u.2
  let g : B → A := fun u ↦ ⟨g1 u, hsphere u⟩
  have hg : Continuous g := hg1.subtype_mk hsphere
  refine Homeomorph.mk { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ } hf hg
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    dsimp [f, g, g1, g0, f0]
    simp [sub_eq_add_neg]
  · intro u
    apply Subtype.ext
    dsimp [f, g, g1, g0, f0]
    simp [sub_eq_add_neg, add_assoc]

theorem disk_degree_punctured_radial_homologyMap_isIso
    (R : ModuleCat ℤ) (n : ℕ) :
    IsIso (SSet.homologyMap
      (TopCat.toSSet.map
        (TopCat.ofHom (puncturedSphereHomotopyEquiv (E := DiskDegreePlane)).toFun)) R n) := by
  exact disk_degree_homotopy_equiv_homologyMap_isIso
    (puncturedSphereHomotopyEquiv (E := DiskDegreePlane)) R n

/-- The punctured-plane relative connecting map in degree two is an isomorphism.
Source: Hatcher, Theorem 2.16, pp.116--118; the plane is contractible, so the
two adjacent positive ordinary homology groups vanish. -/
theorem disk_degree_punctured_plane_connecting_isIso :
    IsIso ((singularSubspacePair (TopCat.of DiskDegreePlane)
      ({0}ᶜ : Set DiskDegreePlane)).homologyδ (ModuleCat.of ℤ ℤ) 2 1 (by simp)) := by
  let P := singularSubspacePair (TopCat.of DiskDegreePlane)
    ({0}ᶜ : Set DiskDegreePlane)
  let : ContractibleSpace DiskDegreePlane := inferInstance
  have hz (n : ℕ) (hn : n ≠ 0) :
      IsZero ((TopCat.toSSet.obj (TopCat.of DiskDegreePlane)).homology
        (ModuleCat.of ℤ ℤ) n) :=
    singular_homology_isZero_of_contractible (TopCat.of DiskDegreePlane)
      (ModuleCat.of ℤ ℤ) n hn
  exact P.shortExact_chainComplexShortComplex (ModuleCat.of ℤ ℤ) |>.isIso_δ
    2 1 (by simp) (hz 2 (by omega)) (hz 1 (by omega))

/-- Formal cancellation reduces native affine relative-map invertibility to the
boundary homology-map invertibility.  Source: Hatcher, Theorem 2.16,
pp.116--118; this is the algebraic cancellation in the pair LES comparison.
The remaining geometric input is isolated as the explicit `hb` hypothesis.
-/
theorem disk_degree_positive_translation_native_map_isIso_of_boundary_map
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (hb : IsIso (HomologicalComplex.homologyMap
      (HolomorphicAnosov.GoodPair.pairChainShortComplexMap
        (singularSubspacePairMap
          (TopCat.ofHom ⟨fun z : closedBall c r ↦ (z : DiskDegreePlane) - c,
            continuous_subtype_val.sub continuous_const⟩)
          (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane)
          (fun z hz ↦ by
            change (z : DiskDegreePlane) - c ≠ 0
            intro hzero
            have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
            have hrad : r = 0 := by simpa [hzc] using hz.symm
            exact (ne_of_gt hr) hrad)) (ModuleCat.of ℤ ℤ)).τ₁ 1)) :
    IsIso (diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ (z : DiskDegreePlane) - c,
        continuous_subtype_val.sub continuous_const⟩
      (by
        intro z hz
        change (z : DiskDegreePlane) - c ≠ 0
        intro hzero
        have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
        have hrad : r = 0 := by simpa [hzc] using hz.symm
        exact (ne_of_gt hr) hrad)) := by
  let f : singularSubspacePair (TopCat.of (closedBall c r))
      (diskDegreeBoundary c r) ⟶
      singularSubspacePair (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane) :=
    singularSubspacePairMap
      (TopCat.ofHom ⟨fun z : closedBall c r ↦ (z : DiskDegreePlane) - c,
        continuous_subtype_val.sub continuous_const⟩)
      (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane)
      (fun z hz ↦ by
        change (z : DiskDegreePlane) - c ≠ 0
        intro hzero
        have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
        have hrad : r = 0 := by simpa [hzc] using hz.symm
        exact (ne_of_gt hr) hrad)
  let dD := (singularSubspacePair (TopCat.of (closedBall c r))
    (diskDegreeBoundary c r)).homologyδ (ModuleCat.of ℤ ℤ) 2 1 (by simp)
  let dP := (singularSubspacePair (TopCat.of DiskDegreePlane) ({0}ᶜ : Set DiskDegreePlane)).homologyδ
    (ModuleCat.of ℤ ℤ) 2 1 (by simp)
  let b := HomologicalComplex.homologyMap
    (HolomorphicAnosov.GoodPair.pairChainShortComplexMap f (ModuleCat.of ℤ ℤ)).τ₁ 1
  let q := HomologicalComplex.homologyMap
    (HolomorphicAnosov.GoodPair.pairChainShortComplexMap f (ModuleCat.of ℤ ℤ)).τ₃ 2
  have hdD : IsIso dD := by
    exact closedBall_relative_connecting_isIso c r (le_of_lt hr) (diskDegreeBoundary c r)
      (ModuleCat.of ℤ ℤ) 0
  have hdP : IsIso dP := disk_degree_punctured_plane_connecting_isIso
  let : IsIso dD := hdD
  let : IsIso dP := hdP
  let : IsIso b := hb
  have hn := disk_degree_positive_translation_connecting_naturality c r hr
  change IsIso q
  have hq : q = dD ≫ b ≫ inv dP := by
    apply (cancel_mono dP).mp
    simpa [q, dD, b, f, Category.assoc] using hn.symm
  rw [hq]
  infer_instance

theorem disk_degree_positive_translation_native_map_isIso_source
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r) :
    IsIso (diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ (z : DiskDegreePlane) - c,
        continuous_subtype_val.sub continuous_const⟩
      (by
        intro z hz
        change (z : DiskDegreePlane) - c ≠ 0
        intro hzero
        have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
        have hrad : r = 0 := by simpa [hzc] using hz.symm
        exact (ne_of_gt hr) hrad)) := by
  let A : Type := {z : closedBall c r // dist (z : DiskDegreePlane) c = r}
  let B : Type := {u : DiskDegreePlane // ‖u‖ = r}
  let eAB := diskDegreeBoundaryTranslationExplicit c r
  let eRad := (diskDegreeSphereScale r hr).toHomotopyEquiv.trans
    ((HolomorphicAnosov.puncturedSphereHomotopyEquiv
      (E := DiskDegreePlane)).symm.trans
      (diskDegreePuncturedAmbientScale r hr).toHomotopyEquiv)
  let e := eAB.toHomotopyEquiv.trans eRad
  have hi := disk_degree_homotopy_equiv_homologyMap_isIso e (ModuleCat.of ℤ ℤ) 1
  let f0 : C(closedBall c r, DiskDegreePlane) :=
    ⟨fun z ↦ (z : DiskDegreePlane) - c,
      continuous_subtype_val.sub continuous_const⟩
  let f : C((diskDegreeBoundary c r), {x : DiskDegreePlane // x ≠ 0}) :=
    ⟨fun z ↦ ⟨f0 z.1, by
      intro hz
      have hzc : (z.1 : DiskDegreePlane) = c := sub_eq_zero.mp hz
      have hnorm : dist (z.1 : DiskDegreePlane) c = r := z.2
      have : r = 0 := by simpa [hzc] using hnorm.symm
      exact (ne_of_gt hr) this⟩,
      (f0.continuous.comp continuous_subtype_val).subtype_mk (fun z ↦ by
        intro hz
        have hzc : (z.1 : DiskDegreePlane) = c := sub_eq_zero.mp hz
        have hnorm : dist (z.1 : DiskDegreePlane) c = r := z.2
        have : r = 0 := by simpa [hzc] using hnorm.symm
        exact (ne_of_gt hr) this)⟩
  have he : f = e.toFun := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change (z.1 : DiskDegreePlane) - c = (e.toFun z : DiskDegreePlane)
    dsimp [e, eRad, eAB, f, f0, diskDegreeSphereScale, diskDegreePuncturedAmbientScale,
      diskDegreeBoundarySphereInclusion, HolomorphicAnosov.puncturedSphereHomotopyEquiv,
      HolomorphicAnosov.puncturedRadialSphereMap, HolomorphicAnosov.spherePuncturedInclusion]
    change (z.1 : DiskDegreePlane) - c = r • (r⁻¹ • ((z.1 : DiskDegreePlane) - c))
    rw [smul_smul]
    simp [hr.ne']
  have hb : IsIso (HomologicalComplex.homologyMap
      (HolomorphicAnosov.GoodPair.pairChainShortComplexMap
        (singularSubspacePairMap
          (TopCat.ofHom f0) (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane)
          (by
            intro z hz
            change (z : DiskDegreePlane) - c ≠ 0
            intro hzero
            have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
            have hnorm : dist (z : DiskDegreePlane) c = r := hz
            have : r = 0 := by simpa [hzc] using hnorm.symm
            exact (ne_of_gt hr) this)) (ModuleCat.of ℤ ℤ)).τ₁ 1) := by
    change IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f))
      (ModuleCat.of ℤ ℤ) 1)
    rw [he]
    exact hi
  exact disk_degree_positive_translation_native_map_isIso_of_boundary_map c r hr hb


/-- The affine translation carries the chosen positive disk coordinate to the
chosen positive punctured-plane coordinate with unit coefficient. This is the
orientation/naturality bridge in Hatcher §2.2, pp.134--136; it is stated
separately so the native-map isomorphism wrapper has an exact source obligation.
Source: Hatcher, *Algebraic Topology*, §2.2, pp.134--136. -/
theorem disk_degree_positive_translation_coordinate_sign
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r) :
    ∃ eS : ↥((diskDegreeSingularPair (closedBall c r)
      (diskDegreeBoundary c r)).homology (ModuleCat.of ℤ ℤ) 2) ≃ₗ[ℤ] ℤ,
      ∃ eT : ↥((singularSubspacePair (TopCat.of DiskDegreePlane)
        ({0}ᶜ : Set DiskDegreePlane)).homology (ModuleCat.of ℤ ℤ) 2) ≃ₗ[ℤ] ℤ,
      eT ((diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (z : DiskDegreePlane) - c,
          continuous_subtype_val.sub continuous_const⟩
        (by
          intro z hz
          change (z : DiskDegreePlane) - c ≠ 0
          intro hzero
          have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
          have hrad : r = 0 := by simpa [hzc] using hz.symm
          exact (ne_of_gt hr) hrad)).hom (eS.symm 1)) = 1 := by
  let F := diskDegreeRelativeH2Map (diskDegreeBoundary c r)
    ({0}ᶜ : Set DiskDegreePlane)
    ⟨fun z ↦ (z : DiskDegreePlane) - c,
      continuous_subtype_val.sub continuous_const⟩
    (by
      intro z hz
      change (z : DiskDegreePlane) - c ≠ 0
      intro hzero
      have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
      have hrad : r = 0 := by simpa [hzc] using hz.symm
      exact (ne_of_gt hr) hrad)
  let : IsIso F := disk_degree_positive_translation_native_map_isIso_source c r hr
  obtain ⟨eS⟩ := disk_degree_closed_ball_boundary_coordinate c r hr
  let fE := (asIso F).toLinearEquiv
  let eT : ↥((singularSubspacePair (TopCat.of DiskDegreePlane)
      ({0}ᶜ : Set DiskDegreePlane)).homology (ModuleCat.of ℤ ℤ) 2) ≃ₗ[ℤ] ℤ :=
    fE.symm.trans eS
  refine ⟨eS, eT, ?_⟩
  change eT (F.hom (eS.symm 1)) = 1
  have hf : fE (eS.symm 1) = F.hom (eS.symm 1) := by rfl
  rw [← hf]
  change eS (fE.symm (fE (eS.symm 1))) = 1
  rw [fE.symm_apply_apply]
  exact eS.apply_symm_apply 1


/-- Exact source contract for the native positive translation map.
Source: Hatcher, *Algebraic Topology*, §2.2, pp.134--136: affine pair
translation, excision, and connecting-map naturality identify the displayed
native relative homology map as an isomorphism. -/
theorem disk_degree_positive_translation_native_map_isIso
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r) :
    IsIso (diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ (z : DiskDegreePlane) - c,
        continuous_subtype_val.sub continuous_const⟩
      (by
        intro z hz
        change (z : DiskDegreePlane) - c ≠ 0
        intro hzero
        have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
        have hrad : r = 0 := by simpa [hzc] using hz.symm
        exact (ne_of_gt hr) hrad)) := by
  exact disk_degree_positive_translation_native_map_isIso_source c r hr

/-- The positive translation from a closed disk to the punctured plane induces an
isomorphism on relative H₂.  Source: Hatcher, *Algebraic Topology*, §2.2,
pp.134--136: affine translation identifies the disk pair with the standard
local pair, and excision identifies the latter with the punctured plane pair.
The statement records only the native homology map; no generator choice is
hidden in this contract. -/
theorem disk_degree_positive_translation_map_isIso
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r) :
    IsIso (diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ (z : DiskDegreePlane) - c,
        continuous_subtype_val.sub continuous_const⟩
      (by
        intro z hz
        change (z : DiskDegreePlane) - c ≠ 0
        intro hzero
        have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
        have hrad : r = 0 := by simpa [hzc] using hz.symm
        exact (ne_of_gt hr) hrad)) := by
  exact disk_degree_positive_translation_native_map_isIso c r hr

/-- Moving a puncture inside the convex open disk leaves its boundary degree map
unchanged. The affine segment of punctures stays strictly inside, so subtraction
is a boundary-avoiding homotopy. Source: Hatcher §2.2 p.134(c). -/
theorem disk_degree_translation_map_eq
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (a : DiskDegreePlane) (ha : a ∈ ball c r)
    (hc : MapsTo (fun z : closedBall c r ↦ z.val - c) (diskDegreeBoundary c r) ({0}ᶜ))
    (ha' : MapsTo (fun z : closedBall c r ↦ z.val - a) (diskDegreeBoundary c r) ({0}ᶜ)) :
    diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ)
      ⟨fun z ↦ z.val - c, continuous_subtype_val.sub continuous_const⟩ hc =
    diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ)
      ⟨fun z ↦ z.val - a, continuous_subtype_val.sub continuous_const⟩ ha' := by
  let p (v : DiskDegreePlane) : C(closedBall c r, DiskDegreePlane) :=
    ⟨fun z ↦ z.val - v, continuous_subtype_val.sub continuous_const⟩
  have hp (v : DiskDegreePlane) (hv : v ∈ ball c r) :
      MapsTo (p v) (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane) := by
    intro z hz hzero
    have hzv : z.val = v := sub_eq_zero.mp hzero
    have hzlt : dist z.val c < r := hzv ▸ hv
    exact (ne_of_lt hzlt) hz
  let H : ContinuousMap.Homotopy (p c) (p a) :=
    { toFun := fun z ↦ z.2.val - ((1 - (z.1 : ℝ)) • c + (z.1 : ℝ) • a)
      continuous_toFun := by fun_prop
      map_zero_left := by intro z; simp [p]
      map_one_left := by intro z; simp [p] }
  have hH : ∀ (t : unitInterval) (z : closedBall c r), z ∈ diskDegreeBoundary c r →
      H (t, z) ∈ ({0}ᶜ : Set DiskDegreePlane) := by
    intro t z hz hzero
    have ht : (1 - (t : ℝ)) • c + (t : ℝ) • a ∈ ball c r :=
      (convex_ball c r) (mem_ball_self hr) ha (sub_nonneg.mpr t.property.2)
        t.property.1 (sub_add_cancel 1 (t : ℝ))
    have hzv : z.val = (1 - (t : ℝ)) • c + (t : ℝ) • a := sub_eq_zero.mp hzero
    have hzlt : dist z.val c < r := hzv ▸ ht
    exact (ne_of_lt hzlt) hz
  have heq : diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ) (p c)
        (hp c (mem_ball_self hr)) =
      diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ) (p a) (hp a ha) :=
    (relative_singular_homotopy_invariance (ModuleCat ℤ)
      (topPairHomotopy_of_continuousMapHomotopy (diskDegreeBoundary c r) ({0}ᶜ)
        (p c) (p a) (hp c (mem_ball_self hr)) (hp a ha) H hH)
      (ModuleCat.of ℤ ℤ)).2 2
  exact heq

/--
Named local-pair transport provider for the disk-degree restriction map.

Source: Hatcher, *Algebraic Topology*, §2.2, Proposition 2.30 and the local-pair
diagram on pp.134--136. The source map is the literal singular pair map from
`(closedBall c r, diskDegreeBoundary c r)` to the punctured plane pair induced
by the chart restriction minus `w`. The missing transport consists of two exact
comparisons: excision from the closed disk pair to a sufficiently small local
pair around the unique interior preimage, and the chart homeomorphism/inverse
naturality square from that local pair to the target punctured pair. This named
provider records those maps at the native `SSetPair.homologyMap` level without
weakening the parent statement or choosing generators.
-/
theorem disk_degree_homeomorph_restriction_local_pair_excision_transport
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (w : DiskDegreePlane)
    (V W : Set DiskDegreePlane) (hV : IsOpen V) (hW : IsOpen W)
    (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V)
    (hpre : ∃ z : V, (z : DiskDegreePlane) ∈ ball c r ∧
      (h z : DiskDegreePlane) = w)
    (hfboundary : ∀ z : closedBall c r,
      dist (z : DiskDegreePlane) c = r →
        diskDegreeHomeomorphRestriction c r V W h hBV z ≠ w) :
    IsIso (diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ (diskDegreeHomeomorphRestriction c r V W h hBV) z - w,
        (diskDegreeHomeomorphRestriction c r V W h hBV).continuous.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr (hfboundary z hz))) := by
  obtain ⟨a, ha, haw⟩ := hpre
  let p (v : DiskDegreePlane) : C(closedBall c r, DiskDegreePlane) :=
    ⟨fun z ↦ z.val - v, continuous_subtype_val.sub continuous_const⟩
  have hp (v : DiskDegreePlane) (hv : v ∈ ball c r) :
      MapsTo (p v) (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane) := by
    intro z hz hzero
    have hzv : z.val = v := sub_eq_zero.mp hzero
    have hzlt : dist z.val c < r := hzv ▸ hv
    exact (ne_of_lt hzlt) hz
  have heq := disk_degree_translation_map_eq c r hr a.val ha
    (hp c (mem_ball_self hr)) (hp a.val ha)
  have hpa : IsIso (diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ)
      (p a.val) (hp a.val ha)) := by
    rw [← heq]
    exact disk_degree_positive_translation_map_isIso c r hr
  let trans (v : DiskDegreePlane) : DiskDegreePlane ≃ₜ DiskDegreePlane :=
    { toFun := fun x ↦ x - v
      invFun := fun x ↦ x + v
      left_inv := fun x ↦ sub_add_cancel x v
      right_inv := fun x ↦ add_sub_cancel_right x v
      continuous_toFun := continuous_id.sub continuous_const
      continuous_invFun := continuous_id.add continuous_const }
  have htrans (v : DiskDegreePlane) :
      IsIso (diskDegreeRelativeH2Map ({v}ᶜ) ({0}ᶜ)
        ⟨trans v, (trans v).continuous⟩ (fun x hx ↦ sub_ne_zero.mpr hx)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact singular_subspace_homeomorph_homology_bijective
      (X := TopCat.of DiskDegreePlane) (Y := TopCat.of DiskDegreePlane) (trans v) ({v}ᶜ) ({0}ᶜ)
      (fun x ↦ sub_ne_zero) (ModuleCat.of ℤ ℤ) 2
  let AV : Set V := {x | x.val ≠ a.val}
  let AW : Set W := {x | x.val ≠ w}
  let j : C(closedBall c r, V) :=
    ⟨fun x ↦ ⟨x.val, hBV x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hj : MapsTo j (diskDegreeBoundary c r) AV := by
    intro z hz heza
    have hzlt : dist z.val c < r := heza ▸ ha
    exact (ne_of_lt hzlt) hz
  let v : C(V, DiskDegreePlane) := ⟨Subtype.val, continuous_subtype_val⟩
  let wv : C(W, DiskDegreePlane) := ⟨Subtype.val, continuous_subtype_val⟩
  have hv : MapsTo v AV ({a.val}ᶜ : Set DiskDegreePlane) := fun _ hx ↦ hx
  have hw : MapsTo wv AW ({w}ᶜ : Set DiskDegreePlane) := fun _ hx ↦ hx
  let J := diskDegreeRelativeH2Map (diskDegreeBoundary c r) AV j hj
  let I := diskDegreeRelativeH2Map AV ({a.val}ᶜ) v hv
  let T := diskDegreeRelativeH2Map ({a.val}ᶜ) ({0}ᶜ)
    ⟨trans a.val, (trans a.val).continuous⟩ (fun x hx ↦ sub_ne_zero.mpr hx)
  have hI : IsIso I :=
    euclidean_open_neighbourhood_excision V hV a.val a.property (ModuleCat.of ℤ ℤ) 2
  have hT : IsIso T := htrans a.val
  have hJIT : J ≫ I ≫ T = diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ) (p a.val) (hp a.val ha) := by
    dsimp only [J, I, T, diskDegreeRelativeH2Map]
    rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp]
    congr 1
  have hJ : IsIso J := by
    have : IsIso (J ≫ (I ≫ T)) := by rw [hJIT]; exact hpa
    exact IsIso.of_isIso_comp_right J (I ≫ T)
  have hhh (x : V) : h x ∈ AW ↔ x ∈ AV := by
    change (h x).val ≠ w ↔ x.val ≠ a.val
    rw [← haw]
    constructor
    · intro hx he
      exact hx (congrArg (fun z : V ↦ (h z).val) (Subtype.ext he))
    · intro hx he
      exact hx (congrArg Subtype.val (h.injective (Subtype.ext he)))
  let HH := diskDegreeRelativeH2Map AV AW ⟨h, h.continuous⟩ (fun x hx ↦ (hhh x).2 hx)
  have hHH : IsIso HH := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact singular_subspace_homeomorph_homology_bijective
      (X := TopCat.of V) (Y := TopCat.of W) h AV AW hhh
      (ModuleCat.of ℤ ℤ) 2
  let IW := diskDegreeRelativeH2Map AW ({w}ᶜ) wv hw
  have hwW : w ∈ W := haw ▸ (h a).property
  have hIW : IsIso IW :=
    euclidean_open_neighbourhood_excision W hW w hwW (ModuleCat.of ℤ ℤ) 2
  let TW := diskDegreeRelativeH2Map ({w}ᶜ) ({0}ᶜ)
    ⟨trans w, (trans w).continuous⟩ (fun x hx ↦ sub_ne_zero.mpr hx)
  have hTW : IsIso TW := htrans w
  have hfinal : J ≫ HH ≫ IW ≫ TW = diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ (diskDegreeHomeomorphRestriction c r V W h hBV) z - w,
        (diskDegreeHomeomorphRestriction c r V W h hBV).continuous.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr (hfboundary z hz)) := by
    dsimp only [J, HH, IW, TW, diskDegreeRelativeH2Map]
    rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp,
      ← SSetPair.homologyMap_comp]
    congr 1
  rw [← hfinal]
  infer_instance

theorem disk_degree_homeomorph_restriction_local_pair_map_isIso
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (w : DiskDegreePlane)
    (V W : Set DiskDegreePlane) (hV : IsOpen V) (hW : IsOpen W)
    (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V)
    (hpre : ∃ z : V, (z : DiskDegreePlane) ∈ ball c r ∧
      (h z : DiskDegreePlane) = w)
    (hfboundary : ∀ z : closedBall c r,
      dist (z : DiskDegreePlane) c = r →
        diskDegreeHomeomorphRestriction c r V W h hBV z ≠ w) :
    IsIso (diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ (diskDegreeHomeomorphRestriction c r V W h hBV) z - w,
        (diskDegreeHomeomorphRestriction c r V W h hBV).continuous.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr (hfboundary z hz))) := by
  exact disk_degree_homeomorph_restriction_local_pair_excision_transport
    c r hr w V W hV hW h hBV hpre hfboundary

/-- A plane homeomorphism on open neighbourhoods induces a unit local relative
degree on the closed disk.  Source: Hatcher, *Algebraic Topology*, §2.2,
Proposition 2.30 and the local-pair comparison on pp.134--136.  Restrict the
homeomorphism and its inverse around the unique interior preimage, apply
excision to identify those local pairs with the punctured plane pair, and use
the integral local orientation action; an orientation-preserving chart gives
`+1`, while an orientation-reversing chart gives `-1`. -/
theorem disk_degree_homeomorph_restriction_local_pair_unit
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (w : DiskDegreePlane)
    (V W : Set DiskDegreePlane) (hV : IsOpen V) (hW : IsOpen W)
    (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V)
    (hpre : ∃ z : V, (z : DiskDegreePlane) ∈ ball c r ∧
      (h z : DiskDegreePlane) = w)
    (hfboundary : ∀ z : closedBall c r,
      dist (z : DiskDegreePlane) c = r →
        diskDegreeHomeomorphRestriction c r V W h hBV z ≠ w) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (diskDegreeHomeomorphRestriction c r V W h hBV) z - w,
          (diskDegreeHomeomorphRestriction c r V W h hBV).continuous.sub continuous_const⟩
        (fun z hz ↦ sub_ne_zero.mpr (hfboundary z hz)) =
      ε • diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (z : DiskDegreePlane) - c,
          continuous_subtype_val.sub continuous_const⟩
        (by
          intro z hz
          change (z : DiskDegreePlane) - c ≠ 0
          intro hzero
          have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
          have hrad : r = 0 := by simpa [hzc] using hz.symm
          exact (ne_of_gt hr) hrad) := by
  let F := diskDegreeRelativeH2Map (diskDegreeBoundary c r)
    ({0}ᶜ : Set DiskDegreePlane)
    ⟨fun z ↦ (diskDegreeHomeomorphRestriction c r V W h hBV) z - w,
      (diskDegreeHomeomorphRestriction c r V W h hBV).continuous.sub continuous_const⟩
    (fun z hz ↦ sub_ne_zero.mpr (hfboundary z hz))
  let P := diskDegreeRelativeH2Map (diskDegreeBoundary c r)
    ({0}ᶜ : Set DiskDegreePlane)
    ⟨fun z ↦ (z : DiskDegreePlane) - c,
      continuous_subtype_val.sub continuous_const⟩
    (by
      intro z hz
      change (z : DiskDegreePlane) - c ≠ 0
      intro hzero
      have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
      have hrad : r = 0 := by simpa [hzc] using hz.symm
      exact (ne_of_gt hr) hrad)
  let : IsIso F := disk_degree_homeomorph_restriction_local_pair_map_isIso
    c r hr w V W hV hW h hBV hpre hfboundary
  let : IsIso P := disk_degree_positive_translation_map_isIso c r hr
  obtain ⟨eS⟩ := disk_degree_closed_ball_boundary_coordinate c r hr
  obtain ⟨eT⟩ := disk_degree_ordinary_plane_local_homology_coordinate
  let fE := (asIso F).toLinearEquiv
  let pE := (asIso P).toLinearEquiv
  let q : ℤ ≃ₗ[ℤ] ℤ := eS.symm.trans (fE.trans eT)
  let qP : ℤ ≃ₗ[ℤ] ℤ := eS.symm.trans (pE.trans eT)
  let a : ℤ ≃ₗ[ℤ] ℤ := q.trans qP.symm
  obtain hsign | hsign := disk_degree_integer_linear_equiv_sign a
  · refine ⟨1, Or.inl rfl, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply eT.injective
    have ha : a (eS x) = eS x := by
      have hm := a.map_smul (eS x) (1 : ℤ)
      simpa [smul_eq_mul, hsign] using hm
    have hq : q (eS x) = qP (a (eS x)) := by
      simpa only [a, LinearEquiv.trans_apply] using
        (qP.apply_symm_apply (q (eS x))).symm
    have hcoord : (fE.trans eT) x = (pE.trans eT) x := by
      simpa only [q, qP, LinearEquiv.trans_apply, eS.symm_apply_apply, ha] using hq
    have hf : fE x = F.hom x := by rfl
    have hp : pE x = P.hom x := by rfl
    change eT (fE x) = eT (pE x) at hcoord
    rw [hf, hp] at hcoord
    rw [one_smul]
    change eT (F.hom x) = eT (P.hom x)
    exact hcoord
  · refine ⟨-1, Or.inr rfl, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply eT.injective
    have ha : a (eS x) = -eS x := by
      have hm := a.map_smul (eS x) (1 : ℤ)
      simpa [smul_eq_mul, hsign] using hm
    have hq : q (eS x) = qP (a (eS x)) := by
      simpa only [a, LinearEquiv.trans_apply] using
        (qP.apply_symm_apply (q (eS x))).symm
    have hcoord : (fE.trans eT) x = -(pE.trans eT) x := by
      simpa only [q, qP, LinearEquiv.trans_apply, eS.symm_apply_apply, ha, map_neg] using hq
    have hf : fE x = F.hom x := by rfl
    have hp : pE x = P.hom x := by rfl
    change eT (fE x) = -eT (pE x) at hcoord
    rw [hf, hp] at hcoord
    change eT (F.hom x) = eT (((-1 : ℤ) • P).hom x)
    have hneg : (((-1 : ℤ) • P).hom x) = -(P.hom x) := by
      change ((-1 : ℤ) • P.hom) x = _
      simp
    calc
      eT (F.hom x) = -eT (P.hom x) := hcoord
      _ = eT (-(P.hom x)) := (map_neg eT (P.hom x)).symm
      _ = eT (((-1 : ℤ) • P).hom x) := by rw [hneg]

/-- The positive derivative gives the same punctured local homology map as translation.
Source: Hatcher, Proposition 2.30 p.136. The derivative homotopy avoids zero on
an entire punctured closed ball; a path of positive linear equivalences then
joins the derivative to the identity and gives equality of the actual pair maps. -/
theorem disk_degree_positive_local_map
    (O : Set DiskDegreePlane) (hO : IsOpen O)
    (g : DiskDegreePlane → DiskDegreePlane) (hg : ContDiffOn ℝ 1 g O)
    (a : DiskDegreePlane) (ha : a ∈ O)
    (hdet : 0 < LinearMap.det (fderiv ℝ g a).toLinearMap) :
    ∃ (r : ℝ) (_hr : 0 < r) (hBO : closedBall a r ⊆ O)
      (havoid : ∀ z : closedBall a r, z.val ≠ a → g z.val ≠ g a),
      diskDegreeRelativeH2Map {z : closedBall a r | z.val ≠ a} ({0}ᶜ)
        ⟨fun z ↦ g z.val - g a, (hg.continuousOn.mono hBO).domRestrict.sub continuous_const⟩
        (fun z hz ↦ sub_ne_zero.mpr (havoid z hz)) =
      diskDegreeRelativeH2Map {z : closedBall a r | z.val ≠ a} ({0}ᶜ)
        ⟨fun z ↦ z.val - a, continuous_subtype_val.sub continuous_const⟩
        (fun _z hz ↦ sub_ne_zero.mpr hz) := by
  let L := (fderiv ℝ g a).toLinearMap.equivOfDetNeZero hdet.ne'
  have hL : HasFDerivAt g (L.toContinuousLinearEquiv : DiskDegreePlane →L[ℝ] DiskDegreePlane) a := by
    exact (hg.differentiableOn one_ne_zero a ha).differentiableAt (hO.mem_nhds ha) |>.hasFDerivAt
  obtain ⟨r, hr, hBO, H, hH⟩ := exists_derivative_punctured_disk_homotopy
    g O hO hg.continuousOn a ha L.toContinuousLinearEquiv hL
  have havoid (z : closedBall a r) (hz : z.val ≠ a) : g z.val ≠ g a := by
    have ht := hH 1 z hz
    intro he
    apply ht
    exact (H.map_one_left z).trans (sub_eq_zero.mpr he)
  refine ⟨r, hr, hBO, havoid, ?_⟩
  let A : Set (closedBall a r) := {z | z.val ≠ a}
  let F : C(closedBall a r, DiskDegreePlane) :=
    ⟨fun z ↦ L (z.val - a), L.toContinuousLinearEquiv.continuous.comp
      (continuous_subtype_val.sub continuous_const)⟩
  let G : C(closedBall a r, DiskDegreePlane) :=
    ⟨fun z ↦ g z.val - g a, (hg.continuousOn.mono hBO).domRestrict.sub continuous_const⟩
  let P : C(closedBall a r, DiskDegreePlane) :=
    ⟨fun z ↦ z.val - a, continuous_subtype_val.sub continuous_const⟩
  have hF : MapsTo F A ({0}ᶜ : Set DiskDegreePlane) := by
    intro z hz he
    exact hz (sub_eq_zero.mp (L.injective (he.trans L.map_zero.symm)))
  have hG : MapsTo G A ({0}ᶜ : Set DiskDegreePlane) :=
    fun z hz ↦ sub_ne_zero.mpr (havoid z hz)
  have hP : MapsTo P A ({0}ᶜ : Set DiskDegreePlane) := fun z hz ↦ sub_ne_zero.mpr hz
  have hFG : diskDegreeRelativeH2Map A ({0}ᶜ) F hF =
      diskDegreeRelativeH2Map A ({0}ᶜ) G hG :=
    (relative_singular_homotopy_invariance (ModuleCat ℤ)
      (topPairHomotopy_of_continuousMapHomotopy A ({0}ᶜ) F G hF hG H hH)
      (ModuleCat.of ℤ ℤ)).2 2
  obtain ⟨D, hD, hI, h0, h1⟩ := exists_positive_linear_equiv_injective_path 2 L hdet
  let Hlin : F.Homotopy P :=
    { toFun := fun z ↦ D z.1 (z.2.val - a)
      continuous_toFun := (hD.comp continuous_fst).clm_apply
        ((continuous_subtype_val.comp continuous_snd).sub continuous_const)
      map_zero_left := by intro z; rw [h0]; rfl
      map_one_left := by intro z; rw [h1]; rfl }
  have hlin : ∀ (t : unitInterval) (z : closedBall a r), z ∈ A →
      Hlin (t, z) ∈ ({0}ᶜ : Set DiskDegreePlane) := by
    intro t z hz he
    exact hz (sub_eq_zero.mp (hI t (he.trans (D t).map_zero.symm)))
  have hFP : diskDegreeRelativeH2Map A ({0}ᶜ) F hF =
      diskDegreeRelativeH2Map A ({0}ᶜ) P hP :=
    (relative_singular_homotopy_invariance (ModuleCat ℤ)
      (topPairHomotopy_of_continuousMapHomotopy A ({0}ᶜ) F P hF hP Hlin hlin)
      (ModuleCat.of ℤ ℤ)).2 2
  exact hFG.symm.trans hFP

/-- Native disk-pair formulation of finite-support point detection. -/
theorem diskDegreeRelativeH2_finite_support_ext
    (X : Type) [TopologicalSpace X] [T2Space X] (K : Set X) (hK : K.Finite)
    (v : diskDegreeRelativeH2 X Kᶜ)
    (hv : ∀ (a : X) (ha : a ∈ K),
      (diskDegreeRelativeH2Map Kᶜ ({a}ᶜ) (ContinuousMap.id X)
        (fun z hz hza ↦ hz ((show z = a from hza) ▸ ha))).hom v = 0) : v = 0 := by
  let v' : supportSingularHomology (TopCat.of X) K (ModuleCat.of ℤ ℤ) 2 :=
    (by simpa [supportSingularHomology, supportSingularChainComplex, supportSingularPair,
      diskDegreeRelativeH2, diskDegreeSingularPair] using v)
  have hv' : ∀ (a : X) (ha : a ∈ K),
      supportSingularHomologyRestrict (TopCat.of X) (ModuleCat.of ℤ ℤ)
        (Set.singleton_subset_iff.mpr ha) 2 v' = 0 := by
    intro a ha
    rw [integral_support_restrict_native_apply]
    exact hv a ha
  exact IntegralCompactSupportOrientation.finite_support_zero_of_point_restrictions
    (TopCat.of X) (ModuleCat.of ℤ ℤ) 2 K hK v' hv'

/-- Translation identifies the local group of a closed ball with the punctured plane.
The closed ball contains a neighborhood of its centre, so its inclusion is excision;
translation is a homeomorphism of the corresponding punctured pairs. -/
theorem disk_degree_punctured_ball_translation_isIso
    (c : DiskDegreePlane) (r : ℝ) (a : DiskDegreePlane) (ha : a ∈ ball c r) :
    IsIso (diskDegreeRelativeH2Map {z : closedBall c r | z.val ≠ a} ({0}ᶜ)
      ⟨fun z ↦ z.val - a, continuous_subtype_val.sub continuous_const⟩
      (fun _z hz ↦ sub_ne_zero.mpr hz)) := by
  let e : DiskDegreePlane ≃ₜ DiskDegreePlane :=
    { toFun := fun x ↦ x - a
      invFun := fun x ↦ x + a
      left_inv := fun x ↦ sub_add_cancel x a
      right_inv := fun x ↦ add_sub_cancel_right x a
      continuous_toFun := continuous_id.sub continuous_const
      continuous_invFun := continuous_id.add continuous_const }
  let I := diskDegreeRelativeH2Map {z : closedBall c r | z.val ≠ a} ({a}ᶜ)
    ⟨Subtype.val, continuous_subtype_val⟩ (fun _ hx ↦ hx)
  let T := diskDegreeRelativeH2Map ({a}ᶜ) ({0}ᶜ)
    ⟨e, e.continuous⟩ (fun _ hx ↦ sub_ne_zero.mpr hx)
  have hI : IsIso I := point_neighborhood_excision_isIso (TopCat.of DiskDegreePlane)
    a (closedBall c r) (mem_interior.mpr ⟨ball c r, ball_subset_closedBall,
      isOpen_ball, ha⟩) (ModuleCat.of ℤ ℤ) 2
  have hT : IsIso T := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact singular_subspace_homeomorph_homology_bijective
      (X := TopCat.of DiskDegreePlane) (Y := TopCat.of DiskDegreePlane) e ({a}ᶜ) ({0}ᶜ)
      (fun x ↦ sub_ne_zero) (ModuleCat.of ℤ ℤ) 2
  have he : I ≫ T = diskDegreeRelativeH2Map {z : closedBall c r | z.val ≠ a} ({0}ᶜ)
      ⟨fun z ↦ z.val - a, continuous_subtype_val.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr hz) := by
    dsimp only [I, T, diskDegreeRelativeH2Map]
    rw [← SSetPair.homologyMap_comp]
    congr 1
  rw [← he]
  infer_instance

/--
Finite-fibre local-degree sum provider.

Source: Hatcher, *Algebraic Topology*, §2.2, Proposition 2.30, pp.134--136.
The fibre is finite and lies in the disk interior. At each fibre point choose a
small closed disk on which the derivative homotopy avoids zero off its centre.
A path of positive linear maps to the identity identifies its local map with
translation. Lift a global class through each local translation isomorphism and
sum the inclusions. Finite-support point detection identifies this sum with the
global class: at each puncture the matching term agrees by moving the puncture
inside the disk, while every other term factors through the full subspace and
vanishes. Applying g−w sends each local term to the same translated global class,
so the resulting map is the fibre cardinality times translation, including zero
for an empty fibre.
-/
theorem disk_degree_local_degree_count_finite_fibre_provider
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (O : Set DiskDegreePlane) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (g : DiskDegreePlane → DiskDegreePlane) (hg : ContDiffOn ℝ 1 g O)
    (hdet : ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ g z).toLinearMap)
    (w : DiskDegreePlane) (hboundary : ∀ z ∈ sphere c r, g z ≠ w) :
    let gB := diskDegreeRestriction c r g (hg.continuousOn.mono hBO)
    let hboundaryB : ∀ z : closedBall c r,
        dist (z : DiskDegreePlane) c = r → gB z ≠ w := fun z hz ↦ hboundary z hz
    ∃ d : ℤ,
      HasDiskDegree c r hr gB w hboundaryB d ∧
      d = ({z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}.ncard : ℤ) := by
  dsimp only
  let B := closedBall c r
  let K : Set B := {z | g z.val = w}
  have hfin : K.Finite :=
    (disk_degree_fibre_finite c r O hO hBO g hg hdet w hboundary).preimage
      Subtype.val_injective.injOn |>.subset (by intro z hz; exact ⟨z.property, hz⟩)
  have hinside : ∀ z ∈ K, z.val ∈ ball c r := by
    intro z hz
    exact (disk_degree_fibre_compact_buffer c r g (hg.continuousOn.mono hBO)
      w hboundary).2.1 ⟨z.property, hz⟩
  have hAK : MapsTo (ContinuousMap.id B) (diskDegreeBoundary c r) Kᶜ := by
    intro z hz hgzw
    exact hboundary z.val hz hgzw
  let R := diskDegreeRelativeH2Map (diskDegreeBoundary c r) Kᶜ (ContinuousMap.id B) hAK
  let G : C(B, DiskDegreePlane) :=
    ⟨fun z ↦ g z.val - w, (hg.continuousOn.mono hBO).domRestrict.sub continuous_const⟩
  let F := diskDegreeRelativeH2Map Kᶜ ({0}ᶜ) G (fun z hz ↦ sub_ne_zero.mpr hz)
  let P : C(B, DiskDegreePlane) :=
    ⟨fun z ↦ z.val - c, continuous_subtype_val.sub continuous_const⟩
  have hP : MapsTo P (diskDegreeBoundary c r) ({0}ᶜ : Set DiskDegreePlane) := by
    intro z hz he
    have hz' : z.val = c := sub_eq_zero.mp he
    have hrad : r = 0 := by simpa [hz'] using hz.symm
    exact hr.ne' hrad
  let T := diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ) P hP
  have hlocal (a : K) :
      ∃ (s : ℝ) (_hs : 0 < s) (hBs : closedBall a.val.val s ⊆ O ∩ ball c r)
        (hav : ∀ z : closedBall a.val.val s, z.val ≠ a.val.val → g z.val ≠ g a.val.val),
        diskDegreeRelativeH2Map {z : closedBall a.val.val s | z.val ≠ a.val.val} ({0}ᶜ)
          ⟨fun z ↦ g z.val - g a.val.val,
            (hg.continuousOn.mono (hBs.trans inter_subset_left)).domRestrict.sub continuous_const⟩
          (fun z hz ↦ sub_ne_zero.mpr (hav z hz)) =
        diskDegreeRelativeH2Map {z : closedBall a.val.val s | z.val ≠ a.val.val} ({0}ᶜ)
          ⟨fun z ↦ z.val - a.val.val, continuous_subtype_val.sub continuous_const⟩
          (fun z hz ↦ sub_ne_zero.mpr hz) := by
    exact disk_degree_positive_local_map (O ∩ ball c r) (hO.inter isOpen_ball) g
      (hg.mono inter_subset_left) a.val.val
      ⟨hBO a.val.property, hinside a.val a.property⟩ (hdet _ (hBO a.val.property))
  choose s hs hBs hav hmaps using hlocal
  let D (a : K) := closedBall a.val.val (s a)
  let A (a : K) : Set (D a) := {z | z.val ≠ a.val.val}
  let p (a : K) : C(D a, DiskDegreePlane) :=
    ⟨fun z ↦ z.val - a.val.val, continuous_subtype_val.sub continuous_const⟩
  let L (a : K) := diskDegreeRelativeH2Map (A a) ({0}ᶜ) (p a)
    (fun z hz ↦ sub_ne_zero.mpr hz)
  have hL (a : K) : IsIso (L a) :=
    disk_degree_punctured_ball_translation_isIso a.val.val (s a) a.val.val (mem_ball_self (hs a))
  let j (a : K) : C(D a, B) :=
    ⟨fun z ↦ ⟨z.val, ball_subset_closedBall ((hBs a z.property).2)⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hj (a : K) : MapsTo (j a) (A a) Kᶜ := by
    intro z hz he
    exact hav a z hz (he.trans a.property.symm)
  let J (a : K) := diskDegreeRelativeH2Map (A a) Kᶜ (j a) (hj a)
  have hJF (a : K) : J a ≫ F = L a := by
    have hm := hmaps a
    change _ = L a at hm
    apply Eq.trans ?_ hm
    apply diskDegreeRelativeH2Map_comp_eq (A a) Kᶜ ({0}ᶜ) (j a) G _ (hj a) _ _
    ext z : 1
    change g z.val - w = g z.val - g a.val.val
    rw [a.property]
  have hcount : K.ncard = {z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}.ncard := by
    apply Set.ncard_congr'
    exact { toFun := fun z ↦ ⟨z.val.val, hinside z.val z.property, z.property⟩
            invFun := fun z ↦ ⟨⟨z.val, ball_subset_closedBall z.property.1⟩, z.property.2⟩
            left_inv := fun z ↦ rfl
            right_inv := fun z ↦ rfl }
  let : Fintype K := hfin.fintype
  have hsum : R ≫ F = (Fintype.card K : ℤ) • T := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let localClass (a : K) := (inv (L a)).hom (T.hom x)
    let total := ∑ a : K, (J a).hom (localClass a)
    have htotal : R.hom x = total := by
      apply sub_eq_zero.mp
      apply diskDegreeRelativeH2_finite_support_ext B K hfin
      intro b hb
      let bK : K := ⟨b, hb⟩
      let Q := diskDegreeRelativeH2Map Kᶜ ({b}ᶜ) (ContinuousMap.id B)
        (fun z hz hzb ↦ hz ((show z = b from hzb) ▸ hb))
      let U := diskDegreeRelativeH2Map ({b}ᶜ : Set B) ({0}ᶜ)
        (⟨fun z ↦ z.val - b.val, continuous_subtype_val.sub continuous_const⟩ : C(B, DiskDegreePlane))
        (fun z hz ↦ sub_ne_zero.mpr (fun he ↦ hz (Subtype.ext he)))
      have : IsIso U := by
        have he : {z : B | z.val ≠ b.val} = ({b}ᶜ : Set B) := by
          ext z
          simp only [Set.mem_ofPred_eq, mem_compl_iff, mem_singleton_iff, Subtype.ext_iff]
        have aux (S : Set B)
            (hS : MapsTo (fun z : B ↦ z.val - b.val) S ({0}ᶜ))
            (heS : S = {z : B | z.val ≠ b.val}) :
            IsIso (diskDegreeRelativeH2Map S ({0}ᶜ)
              ⟨fun z ↦ z.val - b.val, continuous_subtype_val.sub continuous_const⟩ hS) := by
          subst S
          exact disk_degree_punctured_ball_translation_isIso c r b.val (hinside b hb)
        exact aux _ _ he.symm
      have hRQU : R ≫ Q ≫ U = T := by
        have hbnd : MapsTo (fun z : B ↦ z.val - b.val) (diskDegreeBoundary c r) ({0}ᶜ) := by
          intro z hz he
          have heq := sub_eq_zero.mp he
          have hlt := hinside b hb
          rw [← heq] at hlt
          exact (ne_of_lt hlt) hz
        have ht := disk_degree_translation_map_eq c r hr b.val (hinside b hb) hP hbnd
        apply Eq.trans ?_ ht.symm
        exact diskDegreeRelativeH2Map_comp_three_eq (diskDegreeBoundary c r) Kᶜ ({b}ᶜ)
          ({0}ᶜ) (ContinuousMap.id B) (ContinuousMap.id B) _ _ _ _ _ _ rfl
      have hJQU : J bK ≫ Q ≫ U = L bK := by
        exact diskDegreeRelativeH2Map_comp_three_eq (A bK) Kᶜ ({b}ᶜ) ({0}ᶜ)
          (j bK) (ContinuousMap.id B) _ (p bK) _ _ _ _ rfl
      have hcross (a : K) (hab : a ≠ bK) : J a ≫ Q = 0 := by
        have hmiss : ∀ z : D a, j a z ∈ ({b}ᶜ : Set B) := by
          intro z he
          have hz : z.val = b.val := congrArg Subtype.val he
          have hza : z.val ≠ a.val.val := by
            intro hza
            apply hab
            apply Subtype.ext
            apply Subtype.ext
            exact hza.symm.trans hz
          exact hav a z hza (by rw [hz]; exact hb.trans a.property.symm)
        have heq : J a ≫ Q = diskDegreeRelativeH2Map (A a) ({b}ᶜ) (j a)
            (fun z _ ↦ hmiss z) := by
          exact diskDegreeRelativeH2Map_comp_eq (A a) Kᶜ ({b}ᶜ)
            (j a) (ContinuousMap.id B) (j a) _ _ _ rfl
        rw [heq]
        exact diskDegreeRelativeH2Map_eq_zero_of_range (A a) ({b}ᶜ) (j a) _ hmiss
      change Q.hom (R.hom x - total) = 0
      rw [map_sub, sub_eq_zero]
      apply (asIso U).toLinearEquiv.injective
      change (R ≫ Q ≫ U).hom x = U.hom (Q.hom total)
      rw [hRQU]
      change T.hom x = U.hom (Q.hom (∑ a : K, (J a).hom (localClass a)))
      rw [map_sum, map_sum]
      rw [Finset.sum_eq_single bK]
      · change T.hom x = (J bK ≫ Q ≫ U).hom (localClass bK)
        rw [hJQU]
        exact ((asIso (L bK)).toLinearEquiv.apply_symm_apply _).symm
      · intro a _ hab
        change U.hom ((J a ≫ Q).hom (localClass a)) = 0
        rw [hcross a hab]
        simp
      · simp
    change F.hom (R.hom x) = ((Fintype.card K : ℤ) • T).hom x
    rw [htotal]
    change F.hom (∑ a : K, (J a).hom (localClass a)) = _
    rw [map_sum]
    have hterm (a : K) : F.hom ((J a).hom (localClass a)) = T.hom x := by
      change (J a ≫ F).hom (localClass a) = _
      rw [hJF]
      exact (asIso (L a)).toLinearEquiv.apply_symm_apply _
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    change (Fintype.card K) • T.hom x = (Fintype.card K : ℤ) • T.hom x
    exact (natCast_zsmul _ _).symm
  refine ⟨(Fintype.card K : ℤ), ?_, ?_⟩
  · change diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ) G _ = _
    have he : R ≫ F = diskDegreeRelativeH2Map (diskDegreeBoundary c r) ({0}ᶜ) G
        (fun z hz ↦ sub_ne_zero.mpr (hboundary z.val hz)) := by
      exact diskDegreeRelativeH2Map_comp_eq (diskDegreeBoundary c r) Kᶜ ({0}ᶜ)
        (ContinuousMap.id B) G G _ _ _ rfl
    exact he.symm.trans hsum
  · congr 1
    rw [← hcount]
    exact Set.fintypeCard_eq_ncard K


/--
The excision part of the local-degree calculation, before uniqueness of the
coefficient is invoked.

Source: Hatcher, *Algebraic Topology*, §2.2, Proposition 2.30, pp.134--136.
The finite inverse charts give a direct sum of local relative groups.  Excision
identifies the global class with the tuple of local classes, and the positive
determinant makes every local linearized contribution equal to `+1`.  Summing
the finitely many summands yields a coefficient whose value is the interior
fibre cardinality.  The remaining uniqueness statement is deliberately kept in
`disk_degree_local_degree_count`, where it can be proved by the corresponding
generator/cancellation argument.
-/
theorem disk_degree_local_excision_sum
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (O : Set DiskDegreePlane) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (g : DiskDegreePlane → DiskDegreePlane) (hg : ContDiffOn ℝ 1 g O)
    (hdet : ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ g z).toLinearMap)
    (w : DiskDegreePlane) (hboundary : ∀ z ∈ sphere c r, g z ≠ w) :
    let gB := diskDegreeRestriction c r g (hg.continuousOn.mono hBO)
    let hboundaryB : ∀ z : closedBall c r,
        dist (z : DiskDegreePlane) c = r → gB z ≠ w := fun z hz ↦ hboundary z hz
    ∃ d : ℤ,
      HasDiskDegree c r hr gB w hboundaryB d ∧
      d = ({z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}.ncard : ℤ) := by
  dsimp only
  exact disk_degree_local_degree_count_finite_fibre_provider
    c r hr O hO hBO g hg hdet w hboundary

/--
Local-degree excision and normalization for an orientation-preserving plane map.

Source: Hatcher, *Algebraic Topology*, §2.2, pp. 134--136, especially
Proposition 2.30 and the excision diagram on p. 136.  Excision identifies the
relative group over the finite fibre with the direct sum of the local relative
groups.  The positive determinant makes every local linear model orientation
preserving, so each local summand contributes `+1`; the sum is therefore the
cardinality of the interior fibre.  The same calculation, together with the
disk and punctured-plane connecting maps, proves existence and uniqueness of the
integer coefficient in `HasDiskDegree`.
-/
theorem disk_degree_local_degree_count
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (O : Set DiskDegreePlane) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (g : DiskDegreePlane → DiskDegreePlane) (hg : ContDiffOn ℝ 1 g O)
    (hdet : ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ g z).toLinearMap)
    (w : DiskDegreePlane) (hboundary : ∀ z ∈ sphere c r, g z ≠ w) :
    let gB := diskDegreeRestriction c r g (hg.continuousOn.mono hBO)
    let hboundaryB : ∀ z : closedBall c r,
        dist (z : DiskDegreePlane) c = r → gB z ≠ w := fun z hz ↦ hboundary z hz
    ∃ d : ℤ,
      HasDiskDegree c r hr gB w hboundaryB d ∧
      (∀ e : ℤ, HasDiskDegree c r hr gB w hboundaryB e → e = d) ∧
      d = ({z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}.ncard : ℤ) := by
  dsimp only
  obtain ⟨d, hd, hcount⟩ := disk_degree_local_degree_count_finite_fibre_provider
    c r hr O hO hBO g hg hdet w hboundary
  refine ⟨d, hd, ?_, hcount⟩
  intro e he
  let P := diskDegreeRelativeH2Map (diskDegreeBoundary c r)
    ({0}ᶜ : Set DiskDegreePlane)
    ⟨fun z ↦ (z : DiskDegreePlane) - c,
      continuous_subtype_val.sub continuous_const⟩
    (by
      intro z hz
      change (z : DiskDegreePlane) - c ≠ 0
      intro hzero
      have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
      have hrad : r = 0 := by simpa [hzc] using hz.symm
      exact (ne_of_gt hr) hrad)
  have : IsIso P := disk_degree_positive_translation_map_isIso c r hr
  obtain ⟨κnative⟩ := disk_degree_ordinary_plane_local_homology_coordinate
  let κ : diskDegreeRelativeH2 DiskDegreePlane ({0}ᶜ : Set DiskDegreePlane) ≃ₗ[ℤ] ℤ := κnative
  let x := (asIso P).toLinearEquiv.symm (κ.symm 1)
  have hPx : P.hom x = κ.symm 1 := (asIso P).toLinearEquiv.apply_symm_apply _
  have hmaps : e • P = d • P := he.symm.trans hd
  have hev := congrArg (fun F ↦ κ (F.hom x)) hmaps
  change κ (e • P.hom x) = κ (d • P.hom x) at hev
  simpa [hPx] using hev

/-- The translated identity map realizes degree one by definition.

This is the normalization case used in the local-degree excision argument.
For `z ↦ (z-c)+w`, subtracting `w` gives exactly the positive translation
representative in `HasDiskDegree`, and scalar multiplication by `1` is
definitionally the same map. -/
theorem disk_degree_translation_has_degree_one
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r) (w : DiskDegreePlane) :
    let gB : C(closedBall c r, DiskDegreePlane) :=
      ⟨fun z ↦ (z : DiskDegreePlane) - c + w,
        (continuous_subtype_val.sub continuous_const).add continuous_const⟩
    let hboundaryB : ∀ z : closedBall c r,
        dist (z : DiskDegreePlane) c = r → gB z ≠ w := by
      intro z hz hzero
      change (z : DiskDegreePlane) - c + w = w at hzero
      have hzc : (z : DiskDegreePlane) = c := by
        apply sub_eq_zero.mp
        have hz' : (z : DiskDegreePlane) - c + w = 0 + w := by simpa using hzero
        exact add_right_cancel hz'
      have : r = 0 := by simpa [hzc] using hz.symm
      exact (ne_of_gt hr) this
    HasDiskDegree c r hr gB w hboundaryB 1 := by
  dsimp only
  unfold HasDiskDegree
  simp

/--
The restriction of a plane homeomorphism has local degree a unit.

Source: Hatcher, *Algebraic Topology*, §2.2, pp.134--136.  A homeomorphism
between open neighbourhoods restricts near the unique preimage of `w` to a
homeomorphism of local pairs.  The induced map on the integral local relative
H₂ group is therefore multiplication by `+1` or `-1`; no orientation choice is
made in this contract.  The displayed `HasDiskDegree` conclusion records that
unit coefficient against the same positive disk representative used throughout
this file.
-/
theorem disk_degree_homeomorph_restriction_degree_sign
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (w : DiskDegreePlane)
    (V W : Set DiskDegreePlane) (hV : IsOpen V) (hW : IsOpen W)
    (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V)
    (hpre : ∃ z : V, (z : DiskDegreePlane) ∈ ball c r ∧
      (h z : DiskDegreePlane) = w)
    (hfboundary : ∀ z : closedBall c r,
      dist (z : DiskDegreePlane) c = r →
        diskDegreeHomeomorphRestriction c r V W h hBV z ≠ w) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      HasDiskDegree c r hr
        (diskDegreeHomeomorphRestriction c r V W h hBV) w hfboundary ε := by
  obtain ⟨ε, hε, hmap⟩ := disk_degree_homeomorph_restriction_local_pair_unit
    c r hr w V W hV hW h hBV hpre hfboundary
  exact ⟨ε, hε, hmap⟩

/--
Homeomorphism comparison for the local degree on a disk.

Source: Hatcher, *Algebraic Topology*, §2.2, pp. 134--136.  A homeomorphism of
open plane neighbourhoods carrying an interior point to the avoided value has
local degree `+1` or `-1`, according to its (a priori unknown) orientation.
A boundary-avoiding homotopy identifies this coefficient with the degree of
`g`.  The preceding local-degree count makes the latter a nonnegative fibre
count, so equality with either sign forces exactly one interior preimage.  This
statement deliberately does not assume that the comparison homeomorphism
preserves orientation.
-/
theorem disk_degree_homeomorph_unique_preimage
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (O : Set DiskDegreePlane) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (g : DiskDegreePlane → DiskDegreePlane) (hg : ContDiffOn ℝ 1 g O)
    (hdet : ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ g z).toLinearMap)
    (w : DiskDegreePlane) (hboundary : ∀ z ∈ sphere c r, g z ≠ w)
    (d : ℤ) :
    let gB := diskDegreeRestriction c r g (hg.continuousOn.mono hBO)
    let hboundaryB : ∀ z : closedBall c r,
        dist (z : DiskDegreePlane) c = r → gB z ≠ w := fun z hz ↦ hboundary z hz
    HasDiskDegree c r hr gB w hboundaryB d →
    ∀ (V W : Set DiskDegreePlane), IsOpen V → IsOpen W →
      ∀ (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V),
        (∃ z : V, (z : DiskDegreePlane) ∈ ball c r ∧ (h z : DiskDegreePlane) = w) →
        BoundaryAvoidingDiskHomotopy c r gB
          (diskDegreeHomeomorphRestriction c r V W h hBV) w →
        ∃! z : DiskDegreePlane, z ∈ ball c r ∧ g z = w := by
  dsimp only
  let gB := diskDegreeRestriction c r g (hg.continuousOn.mono hBO)
  let hboundaryB : ∀ z : closedBall c r,
      dist (z : DiskDegreePlane) c = r → gB z ≠ w := fun z hz ↦ hboundary z hz
  intro hd V W hV hW h hBV hpre H
  obtain ⟨d₀, hd₀, huniq₀, hcount₀⟩ :=
    disk_degree_local_degree_count c r hr O hO hBO g hg hdet w hboundary
  obtain ⟨Hmap, hH⟩ := H
  have hfboundary : ∀ z : closedBall c r,
      dist (z : DiskDegreePlane) c = r →
        diskDegreeHomeomorphRestriction c r V W h hBV z ≠ w := by
    intro z hz hzero
    have havoid := hH (1 : unitInterval) z hz
    exact havoid (by simpa using hzero)
  obtain ⟨ε, hε, hεf⟩ := disk_degree_homeomorph_restriction_degree_sign
    c r hr w V W hV hW h hBV hpre hfboundary
  have heq := singularSubspacePairMap_homology_eq_of_avoiding_homotopy
    (diskDegreeBoundary c r) gB
      (diskDegreeHomeomorphRestriction c r V W h hBV) w hboundaryB hfboundary Hmap hH 2
  change diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ gB z - w, gB.continuous.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr (hboundaryB z hz)) =
      diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (diskDegreeHomeomorphRestriction c r V W h hBV) z - w,
          (diskDegreeHomeomorphRestriction c r V W h hBV).continuous.sub continuous_const⟩
        (fun z hz ↦ sub_ne_zero.mpr (hfboundary z hz)) at heq
  change diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ (diskDegreeHomeomorphRestriction c r V W h hBV) z - w,
        (diskDegreeHomeomorphRestriction c r V W h hBV).continuous.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr (hfboundary z hz)) =
      ε • diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (z : DiskDegreePlane) - c,
          continuous_subtype_val.sub continuous_const⟩
        (by
          intro z hz
          change (z : DiskDegreePlane) - c ≠ 0
          intro hzero
          have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
          have hrad : r = 0 := by simpa [hzc] using hz.symm
          exact (ne_of_gt hr) hrad) at hεf
  have hεg : HasDiskDegree c r hr gB w hboundaryB ε := by
    change diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ gB z - w, gB.continuous.sub continuous_const⟩
        (fun z hz ↦ sub_ne_zero.mpr (hboundaryB z hz)) =
      ε • diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ (z : DiskDegreePlane) - c,
          continuous_subtype_val.sub continuous_const⟩
        (by
          intro z hz
          change (z : DiskDegreePlane) - c ≠ 0
          intro hzero
          have hzc : (z : DiskDegreePlane) = c := sub_eq_zero.mp hzero
          have hrad : r = 0 := by simpa [hzc] using hz.symm
          exact (ne_of_gt hr) hrad)
    exact heq.trans hεf
  have hεd₀ : ε = d₀ := huniq₀ ε hεg
  have hd₀' : d = d₀ := huniq₀ d hd
  have hcast : ({z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}.ncard : ℤ) = ε :=
    hcount₀.symm.trans hεd₀.symm
  have hncard : {z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}.ncard = 1 := by
    rcases hε with hε1 | hεm1
    · rw [hε1] at hcast
      exact_mod_cast hcast
    · rw [hεm1] at hcast
      have hnonneg : (0 : ℤ) ≤
          ({z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}.ncard : ℤ) := by
        exact_mod_cast (Nat.zero_le _)
      omega
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hncard
  refine ⟨z, ?_, ?_⟩
  · change z ∈ ({z : DiskDegreePlane | z ∈ ball c r ∧ g z = w} : Set DiskDegreePlane)
    rw [hz]
    simp
  · intro y hy
    have hy' : y ∈ ({z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}) := hy
    rw [hz] at hy'
    simpa using hy'

/--
The relative homological degree of an orientation-preserving local C¹ plane map
on a round disk equals its finite interior preimage count. It is the unique integer
in `HasDiskDegree`, hence precisely the coefficient on the oriented fundamental
class. Its defining map is homotopy-invariant under every continuous boundary-avoiding
homotopy on the actual disk. The final homeomorphism comparison asserts a unique
interior preimage without an orientation hypothesis on that homeomorphism.

The ambient representative g is required C¹ only on O; its values outside O have no
role. The determinant uses the real derivative on the original Euclidean plane.
The finite set and its `Set.ncard` both refer only to preimages inside the given disk.

Source:
Hatcher, Algebraic Topology, §2.2 Degree pp.134–136: degree homotopy invariance p.134(c), local
degree and Proposition2.30 with excision proof p.136; relative homotopy invariance Proposition2.19
p.118, excision Theorem2.20 p.119, exact sequence of pairs pp.116–118. PDF145/printed136 visually
checked. This is the same local-relative degree proof for a disk pair, with all properness and
boundary conditions written explicitly.

Complete current natural-language proof:

1. Use the orientation of R² to choose the fundamental class in H₂(B,∂B;Z)≃Z. Radial contraction
   and the exact sequence of the disk pair identify it with the positive circle class. Excision
   identifies H₂(R²,R²∖{w};Z) with H₂(D,D∖{w};Z) for a small disk D centered at w; its generator
   is the positive local orientation class. The map of pairs g:(B,∂B)→(R²,R²∖{w}) is valid exactly
   because w avoids g(∂B), and its homomorphism is multiplication by an integer.

2. The fibre g⁻¹({w})∩B is closed in compact B, hence compact, and disjoint from ∂B. The
   inverse-function theorem makes every fibre point isolated because det Dg is nonzero. The
   isolated-point neighborhoods induce DiscreteTopology on this fibre subspace. A compact discrete
   space is finite. Choose pairwise disjoint open inverse neighborhoods around its points, contained in
   int(B), on which g is a diffeomorphism onto a neighborhood of w.

3. Apply the excision diagram of Hatcher Proposition2.30 p.136 to H₂(B,B∖g⁻¹({w});Z). It is the
   direct sum of the local H₂ groups at the finitely many preimages. The fundamental class maps to
   the tuple (1,…,1) in their compatible local orientations. The map g sends each summand
   generator to its local degree times the target generator. Consequently the relative degree is
   the sum of these local degrees; if the fibre is empty the direct sum is zero and the degree is
   zero.

4. At a fibre point a, write g(a+v)−w=Dg_a(v)+R(v), where ‖R(v)‖/‖v‖→0. On a small sphere the
   segment Dg_a(v)+tR(v) never vanishes, because the least singular value of Dg_a is positive and
   the remainder is smaller than it. Thus the local degree equals that of Dg_a. An
   orientation-preserving invertible real2×2 matrix is joined through invertible matrices to the
   identity (orthogonalization gives a rotation times a positive triangular matrix; contract the
   rotation angle and positive diagonal entries). Hence its local degree is +1. Every summand
   above is +1, giving the displayed finite count.

5. A boundary-avoiding homotopy is a homotopy of the exact pairs (B,∂B)→(R²,R²∖{w}); relative
   homotopy invariance makes its induced maps equal. If h is a homeomorphism between the stated
   open neighborhoods and w∈h(int B), it has one preimage in B and its restriction to a small open
   neighborhood of that interior point is a homeomorphism onto an open neighborhood of w, so its
   induced local-orientation map is an isomorphism and its degree is ±1, as in Hatcher p.136.
   Equal degree for g is a nonnegative finite count; since ±1 is nonzero, that count is1. This
   proves the final assertion without assuming h orientation beforehand. Compactness and exclusion
   of the boundary account for every preimage inside B; no claim is made about preimages elsewhere
   in O.
-/
theorem disk_degree_local_homeomorphism_count
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (O : Set DiskDegreePlane) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (g : DiskDegreePlane → DiskDegreePlane) (hg : ContDiffOn ℝ 1 g O)
    (hdet : ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ g z).toLinearMap)
    (w : DiskDegreePlane) (hboundary : ∀ z ∈ sphere c r, g z ≠ w) :
    let gB := diskDegreeRestriction c r g (hg.continuousOn.mono hBO)
    let hboundaryB : ∀ z : closedBall c r, dist (z : DiskDegreePlane) c = r → gB z ≠ w :=
      fun z hz ↦ hboundary z hz
    {z : DiskDegreePlane | z ∈ closedBall c r ∧ g z = w}.Finite ∧
    {z : DiskDegreePlane | z ∈ closedBall c r ∧ g z = w} ⊆ ball c r ∧
    ∃ d : ℤ,
      HasDiskDegree c r hr gB w hboundaryB d ∧
      (∀ e : ℤ, HasDiskDegree c r hr gB w hboundaryB e → e = d) ∧
      d = ({z : DiskDegreePlane | z ∈ ball c r ∧ g z = w}.ncard : ℤ) ∧
      (∀ (f : C(closedBall c r, DiskDegreePlane))
        (hfboundary : ∀ z : closedBall c r, dist (z : DiskDegreePlane) c = r → f z ≠ w),
        BoundaryAvoidingDiskHomotopy c r gB f w →
          HasDiskDegree c r hr f w hfboundary d) ∧
      (∀ (V W : Set DiskDegreePlane), IsOpen V → IsOpen W →
        ∀ (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V),
          (∃ z : V, (z : DiskDegreePlane) ∈ ball c r ∧ (h z : DiskDegreePlane) = w) →
          BoundaryAvoidingDiskHomotopy c r gB
            (diskDegreeHomeomorphRestriction c r V W h hBV) w →
          ∃! z : DiskDegreePlane, z ∈ ball c r ∧ g z = w) := by
  dsimp only
  let gB := diskDegreeRestriction c r g (hg.continuousOn.mono hBO)
  let hboundaryB : ∀ z : closedBall c r,
      dist (z : DiskDegreePlane) c = r → gB z ≠ w := fun z hz ↦ hboundary z hz
  have hfinite := disk_degree_fibre_finite c r O hO hBO g hg hdet w hboundary
  have hinside := (disk_degree_fibre_compact_buffer c r g
    (hg.continuousOn.mono hBO) w hboundary).2.1
  refine ⟨hfinite, hinside, ?_⟩
  have hhomotopy (d : ℤ) (hd : HasDiskDegree c r hr gB w hboundaryB d)
      (f : C(closedBall c r, DiskDegreePlane))
      (hfboundary : ∀ z : closedBall c r,
        dist (z : DiskDegreePlane) c = r → f z ≠ w)
      (H : BoundaryAvoidingDiskHomotopy c r gB f w) :
      HasDiskDegree c r hr f w hfboundary d := by
    obtain ⟨H, hH⟩ := H
    have heq := singularSubspacePairMap_homology_eq_of_avoiding_homotopy
      (diskDegreeBoundary c r) gB f w hboundaryB hfboundary H hH 2
    change diskDegreeRelativeH2Map (diskDegreeBoundary c r)
      ({0}ᶜ : Set DiskDegreePlane)
      ⟨fun z ↦ gB z - w, gB.continuous.sub continuous_const⟩
      (fun z hz ↦ sub_ne_zero.mpr (hboundaryB z hz)) =
      diskDegreeRelativeH2Map (diskDegreeBoundary c r)
        ({0}ᶜ : Set DiskDegreePlane)
        ⟨fun z ↦ f z - w, f.continuous.sub continuous_const⟩
        (fun z hz ↦ sub_ne_zero.mpr (hfboundary z hz)) at heq
    exact heq.symm.trans hd
  obtain ⟨d, hd, huniq, hcount⟩ :=
    disk_degree_local_degree_count c r hr O hO hBO g hg hdet w hboundary
  have hcompare :
      ∀ (V W : Set DiskDegreePlane), IsOpen V → IsOpen W →
        ∀ (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V),
          (∃ z : V, (z : DiskDegreePlane) ∈ ball c r ∧ (h z : DiskDegreePlane) = w) →
          BoundaryAvoidingDiskHomotopy c r gB
            (diskDegreeHomeomorphRestriction c r V W h hBV) w →
          ∃! z : DiskDegreePlane, z ∈ ball c r ∧ g z = w := by
    intro V W hV' hW' h hBV hpre H
    exact disk_degree_homeomorph_unique_preimage c r hr O hO hBO g hg hdet w hboundary d
      hd V W hV' hW' h hBV hpre H
  exact ⟨d, hd, huniq, hcount, hhomotopy d hd, hcompare⟩


end HolomorphicAnosov.Topology
