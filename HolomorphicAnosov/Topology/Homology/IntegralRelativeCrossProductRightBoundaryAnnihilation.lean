import HolomorphicAnosov.Topology.Homology.IntegralRelativeChainProduct
import HolomorphicAnosov.Topology.Homology.IntegralRelativeCrossProductLeftBoundaryAnnihilation
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- Positive-degree source boundary transport for the right boundary interface.  -/
theorem integral_relative_cross_product_right_positive_boundary_source
    (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ)
    (ca : (RelativeComplex X A).cycles (p + 1))
    (cb : (RelativeComplex Y B).cycles q)
    (y : (RelativeComplex Y B).X (q + 1))
    (hy : (RelativeComplex Y B).iCycles q cb = (RelativeComplex Y B).d (q + 1) q y)
    (c : Chain X (p + 1))
    (hc : relativeProjection X A (p + 1) c = (RelativeComplex X A).iCycles (p + 1) ca)
    (d : Chain Y (q + 1))
    (hd : relativeProjection Y B (q + 1) d = y)
    (ua : Chain (TopCat.of A) p)
    (hua :
      (SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A))
        singularIntegralCoefficients).f p ua =
        ((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d
          (p + 1) p c)
    (hm : (p + 1) + q = (p + 1) + (q + 1) - 1) :
    ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).d
      ((p + 1) + (q + 1)) (((p + 1) + (q + 1)) - 1)).hom
        (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B)
          ((p + 1) + (q + 1))
          (signedSingularCrossProduct X Y (p + 1) (q + 1) c d)) =
      integralRelativeChainProduct_castRelativeChain hm
        ((-1 : ℤ) ^ (p + 1) • integralRelativeChainProduct X Y A B (p + 1) q
          ((RelativeComplex X A).iCycles (p + 1) ca)
          ((RelativeComplex Y B).iCycles q cb)) := by
  rw [integral_relative_projection_differential_comm]
  have hdy : relativeProjection Y B q
      (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q + 1) q d) =
      (RelativeComplex Y B).iCycles q cb := by
    have h := congrArg (fun f ↦ f.hom d)
      (((singularSubspacePair Y B).chainComplexπ singularIntegralCoefficients).comm
        (q + 1) q)
    change (RelativeComplex Y B).d (q + 1) q
        (relativeProjection Y B (q + 1) d) = _ at h
    rw [hd, ← hy] at h
    exact h.symm
  have hl := signedCrossProduct_left_subspace_vanishes A B p (q + 1) ua d
  change relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + (q + 1))
      (signedSingularCrossProduct X Y p (q + 1)
        ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A))
          singularIntegralCoefficients).f p ua) d) = 0 at hl
  rw [hua] at hl
  have hb := integral_cross_product_positive_boundary X Y p q c d
  let P : Chain (TopCat.of (X × Y)) (p + q + 1) →ₗ[ℤ]
      (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).X (p + q + 1) :=
    (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q + 1)).hom
  have hp := congrArg P hb
  erw [P.map_add, P.toAddMonoidHom.map_zsmul] at hp
  dsimp only [P, LinearMap.toAddMonoidHom_coe] at hp
  erw [integralRelativeChainProduct_relativeProjection_cast,
    integralRelativeChainProduct_relativeProjection_cast,
    integralRelativeChainProduct_relativeProjection_cast] at hp
  erw [hl, integralRelativeChainProduct_castRelativeChain_zero, zero_add,
    ← integralRelativeChainProduct_projection, hc, hdy] at hp
  have cast_smul {m n : ℕ} (h : m = n) (r : ℤ)
      (a : (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).X m) :
      integralRelativeChainProduct_castRelativeChain h (r • a) =
        r • integralRelativeChainProduct_castRelativeChain h a := by
    subst n
    rfl
  have cast_injective {m n : ℕ} (h : m = n) : Function.Injective
      (integralRelativeChainProduct_castRelativeChain
        (X := TopCat.of (X × Y)) (A := ProductSubspace A B) h) := by
    subst n
    exact Function.injective_id
  apply cast_injective (show (p + 1) + (q + 1) - 1 = p + q + 1 by omega)
  rw [integral_relative_cross_product_cast_chain_comp, cast_smul]
  exact hp
/-- Boundary annihilation in the right variable for the relative signed chain product. -/
theorem integral_relative_cross_product_right_boundary_annihilation :
    ∀ (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ)
      (ca : (RelativeComplex X A).cycles p)
      (cb : (RelativeComplex Y B).cycles q),
      (∃ y : (RelativeComplex Y B).X (q + 1),
        (RelativeComplex Y B).iCycles q cb =
          (RelativeComplex Y B).d (q + 1) q y) →
      ∃ z : (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).X (p + q + 1),
        (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).d (p + q + 1) (p + q) z =
          integralRelativeChainProduct X Y A B p q
            ((RelativeComplex X A).iCycles p ca)
            ((RelativeComplex Y B).iCycles q cb) := by
  intro X Y A B p q ca cb hcb
  cases p with
  | zero =>
      obtain ⟨y, hy⟩ := hcb
      obtain ⟨c, hc, uc, huc⟩ := integral_relative_cycle_ambient_boundary_lift X A 0 ca
      obtain ⟨(d : Chain Y (q + 1)), hd⟩ :=
        (ModuleCat.epi_iff_surjective (relativeProjection Y B (q + 1))).mp
          (Cofork.IsColimit.epi
            ((singularSubspacePair Y B).isColimitCokernelCoforkChainComplexX
              singularIntegralCoefficients (q + 1))) y
      let T := (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B))
      let z := relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0 + (q + 1))
        (signedSingularCrossProduct X Y 0 (q + 1) c d)
      refine ⟨z, ?_⟩
      change (T.d (0 + (q + 1)) (0 + q)).hom z = _
      have hcomm := congrArg (fun f => f.hom
          (signedSingularCrossProduct X Y 0 (q + 1) c d))
        (((singularSubspacePair (TopCat.of (X × Y)) (ProductSubspace A B)).chainComplexπ
          singularIntegralCoefficients).comm (0 + (q + 1)) (0 + q))
      change (T.d (0 + (q + 1)) (0 + q)).hom z =
        relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0 + q)
          (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
            (0 + (q + 1)) (0 + q) (signedSingularCrossProduct X Y 0 (q + 1) c d)) at hcomm
      rw [hcomm]
      have hbd := integralRelativeChainProduct_zero_left_boundary X Y q c d
      have hbd' :
          relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0 + q)
              (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
                (0 + (q + 1)) (0 + q) (signedSingularCrossProduct X Y 0 (q + 1) c d)) =
            relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0 + q)
              (signedSingularCrossProduct X Y 0 q c
                (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d
                  (q + 1) q d)) := by
        simpa only [Nat.zero_add] using congrArg
          (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0 + q)).hom hbd
      rw [hbd']
      have hdy :
          relativeProjection Y B q
              (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q + 1) q d) =
            (RelativeComplex Y B).iCycles q cb := by
        have hcommY := congrArg (fun f => f.hom d)
          (((singularSubspacePair Y B).chainComplexπ singularIntegralCoefficients).comm
            (q + 1) q)
        change (RelativeComplex Y B).d (q + 1) q
            (relativeProjection Y B (q + 1) d) =
          relativeProjection Y B q
            (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q + 1) q d) at hcommY
        rw [hd, ← hy] at hcommY
        exact hcommY.symm
      have hprod := integralRelativeChainProduct_projection X Y A B 0 q c
        (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q + 1) q d)
      have hprod' :
          relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (0 + q)
              (signedSingularCrossProduct X Y 0 q c
                (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d
                  (q + 1) q d)) =
            integralRelativeChainProduct X Y A B 0 q
              (relativeProjection X A 0 c)
              (relativeProjection Y B q
                (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d
                  (q + 1) q d)) := by
        exact hprod.symm
      rw [hprod', hc, hdy]
  | succ p =>
      obtain ⟨y, hy⟩ := hcb
      obtain ⟨c, hc, ua, hua⟩ := integral_relative_cycle_ambient_boundary_lift X A (p + 1) ca
      obtain ⟨(d : Chain Y (q + 1)), hd⟩ :=
        (ModuleCat.epi_iff_surjective (relativeProjection Y B (q + 1))).mp
          (Cofork.IsColimit.epi
            ((singularSubspacePair Y B).isColimitCokernelCoforkChainComplexX
              singularIntegralCoefficients (q + 1))) y
      let T := (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B))
      let he : (p + 1) + (q + 1) = (p + 1) + q + 1 := by omega
      let z0 := integralRelativeChainProduct_castRelativeChain he
        (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B)
          ((p + 1) + (q + 1))
          (signedSingularCrossProduct X Y (p + 1) (q + 1) c d))
      have hz0 :
          (T.d ((p + 1) + q + 1) ((p + 1) + q)).hom z0 =
            (-1 : ℤ) ^ (p + 1) • integralRelativeChainProduct X Y A B (p + 1) q
              ((RelativeComplex X A).iCycles (p + 1) ca)
              ((RelativeComplex Y B).iCycles q cb) := by
        let zsrc := relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B)
          ((p + 1) + (q + 1))
          (signedSingularCrossProduct X Y (p + 1) (q + 1) c d)
        have hcast := integral_relative_cross_product_cast_differential_target
          (X := TopCat.of (X × Y)) (A := ProductSubspace A B)
          he (by omega : (p + 1) + (q + 1) - 1 = (p + 1) + q) zsrc
        change (T.d ((p + 1) + q + 1) ((p + 1) + q)).hom
            (integralRelativeChainProduct_castRelativeChain he zsrc) = _
        rw [hcast]
        let hm : (p + 1) + q = (p + 1) + (q + 1) - 1 := by omega
        have hsource := integral_relative_cross_product_right_positive_boundary_source
          X Y A B p q ca cb y hy c hc d hd ua hua hm
        rw [hsource]
        rw [integral_relative_cross_product_cast_chain_comp]
        let hdeg : (p + 1) + q = (p + 1) + q := rfl
        change integralRelativeChainProduct_castRelativeChain _
            ((-1 : ℤ) ^ (p + 1) • integralRelativeChainProduct X Y A B (p + 1) q
              ((RelativeComplex X A).iCycles (p + 1) ca)
              ((RelativeComplex Y B).iCycles q cb)) =
          integralRelativeChainProduct_castRelativeChain hdeg
            ((-1 : ℤ) ^ (p + 1) • integralRelativeChainProduct X Y A B (p + 1) q
              ((RelativeComplex X A).iCycles (p + 1) ca)
              ((RelativeComplex Y B).iCycles q cb))
        exact integral_relative_cross_product_cast_relative_proof_irrel _ _ _
      refine ⟨(-1 : ℤ) ^ (p + 1) • z0, ?_⟩
      change (T.d ((p + 1) + q + 1) ((p + 1) + q)).hom
        ((-1 : ℤ) ^ (p + 1) • z0) = _
      rw [map_zsmul, hz0, smul_smul, ← mul_pow]
      simp
end HolomorphicAnosov.Topology

