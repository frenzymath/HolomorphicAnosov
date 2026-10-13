import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import HolomorphicAnosov.Topology.Homology.IntegralRelativeProductData
import HolomorphicAnosov.Topology.SignedCrossProductLeftSubspaceVanishes
import HolomorphicAnosov.Topology.SignedCrossProductRightSubspaceVanishes
import HolomorphicAnosov.Topology.Homology.IntegralCrossProductPositiveBoundary



noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- Integer linearity of an additive map for the native module structures. -/
def integralLinear (C D : ModuleCat.{u} ℤ) (f : C →+ D) : C →ₗ[ℤ] D :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro r a
      change f (C.isModule.smul r a) = D.isModule.smul r (f a)
      rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
      exact f.map_zsmul r a }

/-- Exchange the inputs while retaining the native integer module instances. -/
def integralFlip (C D E : ModuleCat.{u} ℤ) (f : C →ₗ[ℤ] D →ₗ[ℤ] E) :
    D →ₗ[ℤ] C →ₗ[ℤ] E :=
  integralLinear D (ModuleCat.of ℤ (C →ₗ[ℤ] E))
    { toFun := fun b => integralLinear C E
        { toFun := fun a => f a b
          map_zero' := by simp
          map_add' := by intro a a'; simp }
      map_zero' := by ext a; exact (f a).map_zero
      map_add' := by intro b b'; ext a; exact (f a).map_add b b' }

/-- Project the prescribed integral product to the product pair; Bredon IV.16.3. -/
def integralProjectedProduct (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ) :
    Chain X p →ₗ[ℤ] Chain Y q →ₗ[ℤ]
      (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).X (p + q) := by
  let post : (Chain Y q →ₗ[ℤ] Chain (TopCat.of (X × Y)) (p + q)) →+
      (Chain Y q →ₗ[ℤ] (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).X (p + q)) :=
    { toFun := fun k => (relativeProjection (TopCat.of (X × Y))
        (ProductSubspace A B) (p + q)).hom.comp k
      map_zero' := by
        apply LinearMap.ext; intro b
        exact (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q)).hom.map_zero
      map_add' := by
        intro k l; apply LinearMap.ext; intro b
        exact (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q)).hom.map_add (k b) (l b) }
  exact post.toIntLinearMap.comp (signedSingularCrossProduct X Y p q)

/-- Support in the first subspace is annihilated by the projected bilinear map. -/
theorem integralProjectedProduct_left_zero (X Y : TopCat.{u})
    (A : Set X) (B : Set Y) (p q : ℕ) :
    (SSet.chainComplexMap (singularSubspacePair X A).hom singularIntegralCoefficients).f p ≫
      ModuleCat.ofHom (integralProjectedProduct X Y A B p q) = 0 := by
  ext a b
  exact signedCrossProduct_left_subspace_vanishes A B p q a b

/-- Descend through the first native relative-chain cokernel, Bredon IV.16.3. -/
def integralLeftRelativeProduct (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ) :
    (RelativeComplex X A).X p →ₗ[ℤ] Chain Y q →ₗ[ℤ]
      (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).X (p + q) :=
  (CokernelCofork.IsColimit.desc'
    ((singularSubspacePair X A).isColimitCokernelCoforkChainComplexX singularIntegralCoefficients p)
    (ModuleCat.ofHom (integralProjectedProduct X Y A B p q))
    (integralProjectedProduct_left_zero X Y A B p q)).val.hom

@[simp] theorem integralLeftRelativeProduct_projection (X Y : TopCat.{u})
    (A : Set X) (B : Set Y) (p q : ℕ) (a : Chain X p) (b : Chain Y q) :
    integralLeftRelativeProduct X Y A B p q (relativeProjection X A p a) b =
      relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q)
        (signedSingularCrossProduct X Y p q a b) := by
  have h := (CokernelCofork.IsColimit.desc'
    ((singularSubspacePair X A).isColimitCokernelCoforkChainComplexX singularIntegralCoefficients p)
    (ModuleCat.ofHom (integralProjectedProduct X Y A B p q))
    (integralProjectedProduct_left_zero X Y A B p q)).property
  exact congrArg (fun f ↦ f.hom a b) h

/-- Support in the second subspace vanishes after the first cokernel descent. -/
theorem integralLeftRelativeProduct_right_zero (X Y : TopCat.{u})
    (A : Set X) (B : Set Y) (p q : ℕ) :
    (SSet.chainComplexMap (singularSubspacePair Y B).hom singularIntegralCoefficients).f q ≫
      ModuleCat.ofHom (integralFlip _ _ _ (integralLeftRelativeProduct X Y A B p q)) = 0 := by
  ext b a
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (relativeProjection X A p)).mp
    (Cofork.IsColimit.epi ((singularSubspacePair X A).isColimitCokernelCoforkChainComplexX
      singularIntegralCoefficients p)) a
  change integralLeftRelativeProduct X Y A B p q (relativeProjection X A p c)
    ((SSet.chainComplexMap (singularSubspacePair Y B).hom singularIntegralCoefficients).f q b) = 0
  exact (integralLeftRelativeProduct_projection X Y A B p q c
    ((SSet.chainComplexMap (singularSubspacePair Y B).hom singularIntegralCoefficients).f q b)).trans
      (signedCrossProduct_right_subspace_vanishes A B p q c b)

/-- The prescribed product on both relative chain quotients, Bredon IV.16.3. -/
def integralRelativeChainProduct (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ) :
    (RelativeComplex X A).X p →ₗ[ℤ] (RelativeComplex Y B).X q →ₗ[ℤ]
      (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).X (p + q) :=
  integralFlip _ _ _ ((CokernelCofork.IsColimit.desc'
    ((singularSubspacePair Y B).isColimitCokernelCoforkChainComplexX singularIntegralCoefficients q)
    (ModuleCat.ofHom (integralFlip _ _ _ (integralLeftRelativeProduct X Y A B p q)))
    (integralLeftRelativeProduct_right_zero X Y A B p q)).val.hom)

/-- Both native quotient projections preserve the prescribed product formula. -/
@[simp] theorem integralRelativeChainProduct_projection (X Y : TopCat.{u})
    (A : Set X) (B : Set Y) (p q : ℕ) (a : Chain X p) (b : Chain Y q) :
    integralRelativeChainProduct X Y A B p q
      (relativeProjection X A p a) (relativeProjection Y B q b) =
      relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q)
        (signedSingularCrossProduct X Y p q a b) := by
  have h := (CokernelCofork.IsColimit.desc'
    ((singularSubspacePair Y B).isColimitCokernelCoforkChainComplexX singularIntegralCoefficients q)
    (ModuleCat.ofHom (integralFlip _ _ _ (integralLeftRelativeProduct X Y A B p q)))
    (integralLeftRelativeProduct_right_zero X Y A B p q)).property
  have hh := congrArg (fun f ↦ f.hom b (relativeProjection X A p a)) h
  exact hh.trans (integralLeftRelativeProduct_projection X Y A B p q a b)


/-- Every native relative cycle lifts to an ambient chain whose differential is carried by the subspace chain complex. -/
theorem integral_relative_cycle_ambient_boundary_lift (X : TopCat.{u})
    (A : Set X) (p : ℕ) (a : (RelativeComplex X A).cycles p) :
    ∃ c : Chain X p, relativeProjection X A p c = (RelativeComplex X A).iCycles p a ∧
      ∃ u : Chain (TopCat.of A) (p - 1),
        (SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A))
          singularIntegralCoefficients).f (p - 1) u =
          ((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d p (p - 1) c := by
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
    (((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).f p)).mp
    (Cofork.IsColimit.epi
      ((singularSubspacePair X A).isColimitCokernelCoforkChainComplexX
        singularIntegralCoefficients p))
    ((RelativeComplex X A).iCycles p a)
  have hzero :
      ((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).f (p - 1)
        (((singularSubspacePair X A).right.chainComplex singularIntegralCoefficients).d p (p - 1) c) = 0 := by
    have hcomm := congrArg (fun f ↦ f.hom c)
      (((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).comm p (p - 1))
    change (RelativeComplex X A).d p (p - 1)
        (((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).f p c) =
      ((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).f (p - 1)
        (((singularSubspacePair X A).right.chainComplex singularIntegralCoefficients).d p (p - 1) c) at hcomm
    calc
      ((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).f (p - 1)
          (((singularSubspacePair X A).right.chainComplex singularIntegralCoefficients).d p (p - 1) c) =
          (RelativeComplex X A).d p (p - 1)
            (((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).f p c) := hcomm.symm
      _ = (RelativeComplex X A).d p (p - 1)
            ((RelativeComplex X A).iCycles p a) := by rw [hc]
      _ = 0 := congrArg (fun f ↦ f a) ((RelativeComplex X A).iCycles_d p (p - 1))
  obtain ⟨u, hu⟩ := by
    have hex := (HomologicalComplex.shortExact_iff_degreewise_shortExact
      ((singularSubspacePair X A).chainComplexShortComplex singularIntegralCoefficients)).mp
      ((singularSubspacePair X A).shortExact_chainComplexShortComplex singularIntegralCoefficients) (p - 1)
    exact (ShortComplex.moduleCat_exact_iff _).mp hex.exact _ hzero
  exact ⟨c, hc, u, hu⟩


/-- The target pair quotient commutes with the ambient differential in each natural degree.  -/
theorem integral_relative_projection_differential_comm
    (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (n : ℕ) (c : Chain (TopCat.of (X × Y)) n) :
    ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).d n (n - 1)).hom
      (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) n c) =
      relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (n - 1)
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d n (n - 1) c) := by
  have h := ((singularSubspacePair (TopCat.of (X × Y)) (ProductSubspace A B)).chainComplexπ
      singularIntegralCoefficients).comm n (n - 1)
  exact congrArg (fun f ↦ f.hom c) h

theorem integralRelativeChainProduct_castChain_proof_irrel {X : TopCat.{u}} {m n : ℕ} (h h' : m = n)
    (a : Chain X m) : castChain X h a = castChain X h' a := by
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  rfl

def integralRelativeChainProduct_castRelativeChain {X : TopCat.{u}} {A : Set X} {m n : ℕ} (h : m = n)
    (a : (RelativeComplex X A).X m) : (RelativeComplex X A).X n := h ▸ a

theorem integralRelativeChainProduct_relativeProjection_cast {X : TopCat.{u}} {A : Set X} {m n : ℕ} (h : m = n)
    (a : Chain X m) :
    relativeProjection X A n (castChain X h a) = integralRelativeChainProduct_castRelativeChain h (relativeProjection X A m a) := by
  subst n
  rfl

theorem integralRelativeChainProduct_castRelativeChain_zero {X : TopCat.{u}} {A : Set X} {m n : ℕ} (h : m = n) :
    integralRelativeChainProduct_castRelativeChain h (0 : (RelativeComplex X A).X m) = 0 := by
  subst n
  rfl

theorem integralRelativeChainProduct_castRelativeChain_zero_iff {X : TopCat.{u}} {A : Set X} {m n : ℕ}
    (h : m = n) (a : (RelativeComplex X A).X m) :
    integralRelativeChainProduct_castRelativeChain h a = 0 ↔ a = 0 := by
  subst n
  rfl

/-- Positive-degree relative products are cycles. -/
theorem integralRelativeChainProduct_positive_cycles (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ)
    (a : (RelativeComplex X A).cycles (p+1)) (b : (RelativeComplex Y B).cycles (q+1)) :
    ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).dFrom ((p+1)+(q+1))).hom
      (integralRelativeChainProduct X Y A B (p+1) (q+1)
        ((RelativeComplex X A).iCycles (p+1) a) ((RelativeComplex Y B).iCycles (q+1) b)) = 0 := by
  obtain ⟨c, hc, uc, huc⟩ := integral_relative_cycle_ambient_boundary_lift X A (p+1) a
  obtain ⟨d, hd, ud, hud⟩ := integral_relative_cycle_ambient_boundary_lift Y B (q+1) b
  let T := (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B))
  let n := (p+1) + (q+1)
  have hrel := integralRelativeChainProduct_projection X Y A B (p+1) (q+1) c d
  rw [← hc, ← hd]
  convert hrel using 1; simp
  change (T.dFrom n).hom _ = 0
  rw [T.dFrom_eq (show (ComplexShape.down ℕ).Rel n (n-1) by
      simp only [ComplexShape.down_Rel]
      omega)]
  change (T.xNextIso _).inv.hom
    ((T.d n (n-1)).hom
      (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B)
        (p+1 + (q+1)) (signedSingularCrossProduct X Y (p+1) (q+1) c d))) = 0
  rw [integral_relative_projection_differential_comm]
  have hdeg : n - 1 = p + q + 1 := by simp [n]; omega
  have hb := integral_cross_product_positive_boundary X Y p q c d
  have huc' :
      ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A))
        singularIntegralCoefficients).f p) uc =
        ((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p+1) p c := by
    simpa using huc
  have hud' :
      ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion Y B))
        singularIntegralCoefficients).f q) ud =
        ((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q+1) q d := by
    simpa using hud
  have hb' : castChain (TopCat.of (X × Y)) hdeg
          (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d n (n - 1)
            (signedSingularCrossProduct X Y (p+1) (q+1) c d)) =
        castChain (TopCat.of (X × Y)) (by omega)
          (signedSingularCrossProduct X Y p (q+1)
            (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p+1) p c) d) +
          (-1 : ℤ) ^ (p+1) • castChain (TopCat.of (X × Y)) (by omega)
            (signedSingularCrossProduct X Y (p+1) q c
              (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q+1) q d)) := by
      simpa [n] using hb
  simp [n] at hdeg
  have hproj' :
      relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (n - 1)
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d n (n - 1)
          (signedSingularCrossProduct X Y (p+1) (q+1) c d)) = 0 := by
    have hp := congrArg (fun z :
        ((singularSubspacePair (TopCat.of (X × Y)) (ProductSubspace A B)).right.chainComplex
          singularIntegralCoefficients).X (p + q + 1) =>
      relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q + 1) z) hb
    have hl := signedCrossProduct_left_subspace_vanishes A B p (q+1) uc d
    have hr := signedCrossProduct_right_subspace_vanishes A B (p+1) q c ud
    change relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + (q + 1))
      (signedSingularCrossProduct X Y p (q+1)
        (((SSet.chainComplexMap (TopCat.toSSet.map
          (singularSubspaceInclusion X A)) singularIntegralCoefficients).f p) uc) d) = 0 at hl
    change relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) ((p+1) + q)
      (signedSingularCrossProduct X Y (p+1) q c
        (((SSet.chainComplexMap (TopCat.toSSet.map
          (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q) ud)) = 0 at hr
    have hl' :
        relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (n - 1)
          (castChain (TopCat.of (X × Y)) (by omega)
            (signedSingularCrossProduct X Y p (q+1)
              (((SSet.chainComplexMap (TopCat.toSSet.map
                (singularSubspaceInclusion X A)) singularIntegralCoefficients).f p) uc) d)) = 0 := by
      let he : p + (q + 1) = n - 1 := by dsimp [n]; omega
      have hs := integralRelativeChainProduct_relativeProjection_cast (X := TopCat.of (X × Y))
        (A := ProductSubspace A B) he
        (signedSingularCrossProduct X Y p (q+1)
          (((SSet.chainComplexMap (TopCat.toSSet.map
            (singularSubspaceInclusion X A)) singularIntegralCoefficients).f p) uc) d)
      rw [integralRelativeChainProduct_castChain_proof_irrel (by omega) he]
      rw [hs, hl]
      exact integralRelativeChainProduct_castRelativeChain_zero he
    have hr' :
        relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (n - 1)
          (castChain (TopCat.of (X × Y)) (by omega)
            (signedSingularCrossProduct X Y (p+1) q c
              (((SSet.chainComplexMap (TopCat.toSSet.map
                (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q) ud))) = 0 := by
      let he : (p+1) + q = n - 1 := by dsimp [n]
      have hs := integralRelativeChainProduct_relativeProjection_cast (X := TopCat.of (X × Y))
        (A := ProductSubspace A B) he
        (signedSingularCrossProduct X Y (p+1) q c
          (((SSet.chainComplexMap (TopCat.toSSet.map
            (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q) ud))
      rw [integralRelativeChainProduct_castChain_proof_irrel (by omega) he]
      rw [hs, hr]
      exact integralRelativeChainProduct_castRelativeChain_zero he
    have hl0 :
        relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q + 1)
          (castChain (TopCat.of (X × Y)) (by omega)
            (signedSingularCrossProduct X Y p (q+1)
              (((SSet.chainComplexMap (TopCat.toSSet.map
                (singularSubspaceInclusion X A)) singularIntegralCoefficients).f p) uc) d)) = 0 := by
      let he : p + (q+1) = p + q + 1 := by omega
      have hs := integralRelativeChainProduct_relativeProjection_cast (X := TopCat.of (X × Y))
        (A := ProductSubspace A B) he
        (signedSingularCrossProduct X Y p (q+1)
          (((SSet.chainComplexMap (TopCat.toSSet.map
            (singularSubspaceInclusion X A)) singularIntegralCoefficients).f p) uc) d)
      rw [integralRelativeChainProduct_castChain_proof_irrel (by omega) he]
      rw [hs, hl]
      exact integralRelativeChainProduct_castRelativeChain_zero he
    have hr0 :
        relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q + 1)
          (castChain (TopCat.of (X × Y)) (by omega)
            (signedSingularCrossProduct X Y (p+1) q c
              (((SSet.chainComplexMap (TopCat.toSSet.map
                (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q) ud))) = 0 := by
      let he : (p+1) + q = p + q + 1 := by omega
      have hs := integralRelativeChainProduct_relativeProjection_cast (X := TopCat.of (X × Y))
        (A := ProductSubspace A B) he
        (signedSingularCrossProduct X Y (p+1) q c
          (((SSet.chainComplexMap (TopCat.toSSet.map
            (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q) ud))
      rw [integralRelativeChainProduct_castChain_proof_irrel (by omega) he]
      rw [hs, hr]
      exact integralRelativeChainProduct_castRelativeChain_zero he
    rw [← huc', ← hud'] at hp
    let P := relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q + 1)
    have hl0P : P.hom
        (castChain (TopCat.of (X × Y)) (by omega)
          (signedSingularCrossProduct X Y p (q+1)
            (((SSet.chainComplexMap (TopCat.toSSet.map
              (singularSubspaceInclusion X A)) singularIntegralCoefficients).f p) uc) d)) = 0 := by
      simpa [P] using hl0
    have hr0P : P.hom
        (castChain (TopCat.of (X × Y)) (by omega)
          (signedSingularCrossProduct X Y (p+1) q c
            (((SSet.chainComplexMap (TopCat.toSSet.map
              (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q) ud))) = 0 := by
      simpa [P] using hr0
    let hleft : p + (q+1) = p + q + 1 := by omega
    let hright : (p+1) + q = p + q + 1 := by omega
    let u := castChain (TopCat.of (X × Y)) hleft
      (signedSingularCrossProduct X Y p (q+1)
        (((SSet.chainComplexMap (TopCat.toSSet.map
          (singularSubspaceInclusion X A)) singularIntegralCoefficients).f p) uc) d)
    let v := castChain (TopCat.of (X × Y)) hright
      (signedSingularCrossProduct X Y (p+1) q c
        (((SSet.chainComplexMap (TopCat.toSSet.map
          (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q) ud))
    have hl0U : P.hom u = 0 := by simpa [u, P] using hl0
    have hr0V : P.hom v = 0 := by simpa [v, P] using hr0
    have hzero : P
        (u + (-1 : ℤ) ^ (p+1) • v) = 0 := by
      have hv : P.hom ((-1 : ℤ) ^ (p+1) • v) =
          (-1 : ℤ) ^ (p+1) • P.hom v := by
        exact P.hom.toAddMonoidHom.map_zsmul _ _
      calc
        P.hom (u + (-1 : ℤ) ^ (p+1) • v) = P.hom u + P.hom ((-1 : ℤ) ^ (p+1) • v) := P.hom.map_add _ _
        _ = P.hom u + (-1 : ℤ) ^ (p+1) • P.hom v := by rw [hv]
        _ = 0 + (-1 : ℤ) ^ (p+1) • 0 := by rw [hl0U, hr0V]
        _ = 0 := by
          simp only [zsmul_zero, add_zero]
    change P.hom _ = P.hom _ at hp
    rw [hzero] at hp
    have htarget : n - 1 = p + 1 + q := by omega
    have hrotate : p + 1 + q = p + q + 1 := by omega
    let z := (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d n (n - 1)
      (signedSingularCrossProduct X Y (p+1) (q+1) c d))
    have hz : P (castChain (TopCat.of (X × Y)) hrotate z) = 0 := by
      simpa [P, z, castChain, n] using hp
    have hrelcast := integralRelativeChainProduct_relativeProjection_cast (X := TopCat.of (X × Y))
      (A := ProductSubspace A B) hrotate z
    have hz' : integralRelativeChainProduct_castRelativeChain hrotate
        (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + 1 + q) z) = 0 := by
      rw [← hrelcast]
      exact hz
    have hzTarget : relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + 1 + q) z = 0 := by
      exact (integralRelativeChainProduct_castRelativeChain_zero_iff hrotate _).mp hz'
    have htarget' : integralRelativeChainProduct_castRelativeChain htarget
        (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (n - 1) z) = 0 := by
      have hpc := integralRelativeChainProduct_relativeProjection_cast (X := TopCat.of (X × Y))
        (A := ProductSubspace A B) htarget z
      rw [← hpc]
      simpa [castChain] using hzTarget
    exact (integralRelativeChainProduct_castRelativeChain_zero_iff htarget _).mp htarget'
  have hproj := hproj'
  rw [hproj]
  simp


/-- The integral zero-left row commutes with the second differential. -/
theorem integralRelativeChainProduct_zero_left_boundary (X Y : TopCat.{u}) (q : ℕ) (a : Chain X 0) (b : Chain Y (q + 1)) :
((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
    (0 + (q + 1)) (0 + q) (signedSingularCrossProduct X Y 0 (q + 1) a b) =
  signedSingularCrossProduct X Y 0 q a
    (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q + 1) q b) := by
  let Z := TopCat.of (X × Y)
  let dZ := ((TopCat.toSSet.obj Z).chainComplex singularIntegralCoefficients).d
    (0 + (q + 1)) (0 + q)
  let dY := ((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d
    (q + 1) q
  let L : Chain X 0 →+ Chain Z (0 + q) :=
    { toFun := fun a => dZ.hom (signedSingularCrossProduct X Y 0 (q + 1) a b)
      map_zero' := by
        simp only [map_zero, LinearMap.zero_apply]
        exact dZ.hom.map_zero
      map_add' := by intro a a'; simp only [map_add, LinearMap.add_apply] }
  let R : Chain X 0 →+ Chain Z (0 + q) :=
    { toFun := fun a => signedSingularCrossProduct X Y 0 q a (dY b)
      map_zero' := by
        rw [(signedSingularCrossProduct X Y 0 q).map_zero]
        rfl
      map_add' := by intro a a'; simp only [map_add, LinearMap.add_apply] }
  let integerLinear (C D : ModuleCat.{u} ℤ) (f : C →+ D) : C →ₗ[ℤ] D :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro r a
        change f (C.isModule.smul r a) = D.isModule.smul r (f a)
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
        exact f.map_zsmul r a }
  have hh : ModuleCat.ofHom (integerLinear _ _ L) =
      ModuleCat.ofHom (integerLinear _ _ R) := by
    apply singularChain_unitGenerator_ext X 0
    intro σ
    rw [SignedShuffle.OneOne.zero_simplex_eq_point X σ]
    change dZ (signedSingularCrossProduct X Y 0 (q + 1) (pointChain X _) b) =
      signedSingularCrossProduct X Y 0 q (pointChain X _) (dY b)
    have cast_inj (Z : TopCat.{u}) {m n : ℕ} (h : m = n) :
        Function.Injective (castChain Z h) := by
      subst n
      exact fun _ _ h => h
    have cast_d (Z : TopCat.{u}) {i j k l : ℕ} (hi : i = k) (hj : j = l)
        (a : Chain Z i) :
        castChain Z hj
          (((TopCat.toSSet.obj Z).chainComplex singularIntegralCoefficients).d i j a) =
        ((TopCat.toSSet.obj Z).chainComplex singularIntegralCoefficients).d k l
          (castChain Z hi a) := by
      subst k l
      rfl
    apply cast_inj Z (Nat.zero_add q)
    rw [cast_d Z (Nat.zero_add (q + 1)), integral_cross_product_positive_boundary_generator_left_row_chain, integral_cross_product_positive_boundary_generator_left_row_chain]
    exact (congrArg (fun k => k b)
      ((SSet.chainComplexMap (TopCat.toSSet.map (insertLeft X Y _))
        singularIntegralCoefficients).comm (q + 1) q))
  exact congrArg (fun k => k a) hh



/-- The integral zero-right column commutes with the first differential. -/
theorem integralRelativeChainProduct_zero_right_boundary (X Y : TopCat.{u}) (p : ℕ) (a : Chain X (p + 1)) (b : Chain Y 0) :
((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
    ((p + 1) + 0) (p + 0) (signedSingularCrossProduct X Y (p + 1) 0 a b) =
  signedSingularCrossProduct X Y p 0
    (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p a) b := by
  let Z := TopCat.of (X × Y)
  let dZ := ((TopCat.toSSet.obj Z).chainComplex singularIntegralCoefficients).d
    ((p + 1) + 0) (p + 0)
  let dX := ((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d
    (p + 1) p
  let L := dZ.hom.comp (signedSingularCrossProduct X Y (p + 1) 0 a)
  let R := signedSingularCrossProduct X Y p 0 (dX a)
  have hh : ModuleCat.ofHom L = ModuleCat.ofHom R := by
    apply singularChain_unitGenerator_ext Y 0
    intro τ
    rw [SignedShuffle.OneOne.zero_simplex_eq_point Y τ]
    change dZ (signedSingularCrossProduct X Y (p + 1) 0 a (pointChain Y _)) =
      signedSingularCrossProduct X Y p 0 (dX a) (pointChain Y _)
    rw [integral_cross_product_positive_boundary_generator_right_row_chain, integral_cross_product_positive_boundary_generator_right_row_chain]
    exact (congrArg (fun k => k a)
      ((SSet.chainComplexMap (TopCat.toSSet.map (insertRight X Y _))
        singularIntegralCoefficients).comm (p + 1) p))
  exact congrArg (fun k => k b) hh


/-- A degree-zero relative cycle times a positive-degree relative cycle is a relative cycle. -/
theorem integralRelativeChainProduct_zero_left_cycles (X Y : TopCat.{u})
    (A : Set X) (B : Set Y) (q : ℕ)
    (a : (RelativeComplex X A).cycles 0)
    (b : (RelativeComplex Y B).cycles (q+1)) :
    ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).dFrom (0 + (q+1))).hom
      (integralRelativeChainProduct X Y A B 0 (q+1)
        ((RelativeComplex X A).iCycles 0 a)
        ((RelativeComplex Y B).iCycles (q+1) b)) = 0 := by
  obtain ⟨c, hc, uc, huc⟩ := integral_relative_cycle_ambient_boundary_lift X A 0 a
  obtain ⟨d, hd, ud, hud⟩ := integral_relative_cycle_ambient_boundary_lift Y B (q+1) b
  rw [← hc, ← hd]
  rw [integralRelativeChainProduct_projection]
  rw [(RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).dFrom_eq
    (show (ComplexShape.down ℕ).Rel (0 + (q+1)) (0+q) by simp only [ComplexShape.down_Rel]; omega)]
  simp only at *
  let T := (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B))
  change (T.xNextIso _).inv.hom
    ((T.d (0+(q+1)) (0+q)).hom
      (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0+(q+1))
        (signedSingularCrossProduct X Y 0 (q+1) c d))) = 0
  have hcomm := congrArg (fun f => f.hom (signedSingularCrossProduct X Y 0 (q+1) c d))
    (((singularSubspacePair (TopCat.of (X × Y)) (ProductSubspace A B)).chainComplexπ
      singularIntegralCoefficients).comm (0+(q+1)) (0+q))
  change (T.d (0+(q+1)) (0+q)).hom
      (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0+(q+1))
        (signedSingularCrossProduct X Y 0 (q+1) c d)) =
    relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0+q)
      (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
        (0+(q+1)) (0+q) (signedSingularCrossProduct X Y 0 (q+1) c d)) at hcomm
  rw [hcomm, integralRelativeChainProduct_zero_left_boundary]
  have hud' :
      ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q) ud =
        ((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q+1) q d := by simpa using hud
  rw [← hud']
  have hs := signedCrossProduct_right_subspace_vanishes A B 0 q c ud
  have hs' := congrArg (fun z =>
      (T.xNextIso (show (ComplexShape.down ℕ).Rel (0+(q+1)) (0+q) by
        simp only [ComplexShape.down_Rel]; omega)).inv.hom z) hs
  convert hs' using 1
  · rfl
  · exact ((T.xNextIso (show (ComplexShape.down ℕ).Rel (0+(q+1)) (0+q) by simp only [ComplexShape.down_Rel]; omega)).inv.hom.map_zero).symm



/-- A positive-degree relative cycle times a degree-zero relative cycle is a relative cycle. -/
theorem integralRelativeChainProduct_zero_right_cycles (X Y : TopCat.{u})
    (A : Set X) (B : Set Y) (p : ℕ)
    (a : (RelativeComplex X A).cycles (p+1))
    (b : (RelativeComplex Y B).cycles 0) :
    ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).dFrom ((p+1) + 0)).hom
      (integralRelativeChainProduct X Y A B (p+1) 0
        ((RelativeComplex X A).iCycles (p+1) a)
        ((RelativeComplex Y B).iCycles 0 b)) = 0 := by
  obtain ⟨c, hc, uc, huc⟩ := integral_relative_cycle_ambient_boundary_lift X A (p+1) a
  obtain ⟨d, hd, ud, hud⟩ := integral_relative_cycle_ambient_boundary_lift Y B 0 b
  rw [← hc, ← hd]
  have hprod := integralRelativeChainProduct_projection X Y A B (p+1) 0 c d
  convert hprod using 1; simp
  change ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).dFrom ((p+1)+0)).hom _ = 0
  rw [(RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).dFrom_eq
    (show (ComplexShape.down ℕ).Rel ((p+1)+0) (p+0) by simp only [ComplexShape.down_Rel]; omega)]
  let T := (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B))
  change (T.xNextIso _).inv.hom
    ((T.d ((p+1)+0) (p+0)).hom
      (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) ((p+1)+0)
        (signedSingularCrossProduct X Y (p+1) 0 c d))) = 0
  have hcomm := congrArg (fun f => f.hom (signedSingularCrossProduct X Y (p+1) 0 c d))
    (((singularSubspacePair (TopCat.of (X × Y)) (ProductSubspace A B)).chainComplexπ
      singularIntegralCoefficients).comm ((p+1)+0) (p+0))
  change (T.d ((p+1)+0) (p+0)).hom
      (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) ((p+1)+0)
        (signedSingularCrossProduct X Y (p+1) 0 c d)) =
    relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p+0)
      (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
        ((p+1)+0) (p+0) (signedSingularCrossProduct X Y (p+1) 0 c d)) at hcomm
  rw [hcomm, integralRelativeChainProduct_zero_right_boundary]
  have huc' :
      ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A)) singularIntegralCoefficients).f p) uc =
        ((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p+1) p c := by simpa using huc
  rw [← huc']
  have hs := signedCrossProduct_left_subspace_vanishes A B p 0 uc d
  have hs' := congrArg (fun z =>
      (T.xNextIso (show (ComplexShape.down ℕ).Rel ((p+1)+0) (p+0) by
        simp only [ComplexShape.down_Rel]; omega)).inv.hom z) hs
  convert hs' using 1
  · rfl
  · exact ((T.xNextIso (show (ComplexShape.down ℕ).Rel ((p+1)+0) (p+0) by simp only [ComplexShape.down_Rel]; omega)).inv.hom.map_zero).symm


/-- The relative chain product sends two native relative cycles to a target relative cycle. -/
theorem integralRelativeChainProduct_cycles (X Y : TopCat.{u})
    (A : Set X) (B : Set Y) (p q : ℕ)
    (a : (RelativeComplex X A).cycles p)
    (b : (RelativeComplex Y B).cycles q) :
    ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).dFrom (p + q)).hom
      (integralRelativeChainProduct X Y A B p q ((RelativeComplex X A).iCycles p a)
        ((RelativeComplex Y B).iCycles q b)) = 0 := by
  cases p with
  | zero =>
      cases q with
      | zero =>
          simp
      | succ q =>
          exact integralRelativeChainProduct_zero_left_cycles X Y A B q a b
  | succ p =>
      cases q with
      | zero =>
          exact integralRelativeChainProduct_zero_right_cycles X Y A B p a b
      | succ q =>
          exact integralRelativeChainProduct_positive_cycles X Y A B p q a b

end HolomorphicAnosov.Topology
