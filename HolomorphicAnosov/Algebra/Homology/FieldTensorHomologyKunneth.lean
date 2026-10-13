import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.DirectSum.Module
import HolomorphicAnosov.Algebra.Homology.FieldChainKroneckerEvaluation
import HolomorphicAnosov.Algebra.Homology.FieldComplexHomologyModelG4
import HolomorphicAnosov.Algebra.Homology.TensorTotalDegreeDirectSum

/-!
# Field-coefficient homology of tensor chain complexes

Source: Bredon, *Topology and Geometry* (1993), Chapter VI, Section 1,
Theorem 1.5 and its written proof, pp. 318–319; the field specialization
is stated on p. 320. Local source:
`literature/Bredon-Topology-and-Geometry-1993.pdf`, PDF pages 174–175.
This module states DAG node `linear.field_chain_tensor_homology_kunneth_g7`.

The input complexes are actual Mathlib nonnegative unaugmented chain complexes.
The public theorem allows independent field and carrier universes. A concrete
scalar-lift representation supplies its total complex; the named tensor-summand
comparison certifies the original K tensor product, without assuming an isomorphism.
Mathlib's tensor object uses coproducts over p+q=n; in ModuleCat these are the
vector-space direct sums of the tensor products. Its down-ℕ tensor signs are
ε₁=1 and ε₂=(-1)^p, so the differential is
∂(c⊗d)=∂c⊗d+(-1)^p c⊗∂d. The zero-degree outgoing differential is zero.
The explicit homology tensor direct sum uses exactly the same p+q=n indices.

Cycles, boundaries, their quotient and induced homology maps are reused from
`FieldChainKroneckerEvaluation`; no second kernel/image quotient is defined.
Tensor-chain and tensor-cycle data are concrete, and no isomorphism is an
input hypothesis. The homology-model proof establishes bijectivity of the
canonical cycle-class map, and scalar transport handles independent universes.
The existential conclusion supplies a coherent canonical family: the
representative law determines its forward maps, since quotient classes, pure
tensors and direct-sum injections generate the entire source. Naturality is
stated for both arbitrary chain maps and every source element.
-/

open CategoryTheory
open scoped TensorProduct DirectSum

universe u v

noncomputable section

namespace HolomorphicAnosov.FieldTensorHomologyKunneth

open FieldChainKronecker

variable {K : Type u} [Field K]

/-- The actual Mathlib tensor chain complex. Source: Bredon VI§1 pp.318–320;
Mathlib `HomologicalComplex.tensorObj`, `Monoidal.lean:48–50`, and
`ComplexShapeSigns.lean:160–178` implement degree addition and signs 1,(-1)^p.
The coproduct exists in ModuleCat, with no finiteness condition on its modules. -/
abbrev totalComplex (C D : ChainComplex (ModuleCat.{u} K) ℕ) :=
  HomologicalComplex.tensorObj C D

/-- The indices of total degree n: exactly all nonnegative pairs p,q with p+q=n.
Source: Bredon VI Theorem1.5 p.318, displayed meaning of the graded tensor sum. -/
abbrev degreePairs (n : ℕ) := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- A homology tensor summand using the already defined concrete cycle quotient.
Source: Bredon VI§1 Theorem1.5 pp.318–320. -/
abbrev homologyTensorFamily (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ)
    (i : degreePairs n) :=
  degreeHomology.{u, u} C i.val.1 ⊗[K] degreeHomology.{u, u} D i.val.2

/-- The direct sum of homology tensor products in total degree n.
Source: Bredon VI Theorem1.5 p.318; no dimension or generation condition occurs. -/
abbrev homologyTensorSum (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) :=
  ⨁ i : degreePairs n, homologyTensorFamily C D n i

/-- A pure tensor in its specified actual total-complex summand.
Source: Bredon VI§1 pp.318–319; Mathlib `ιTensorObj` is the coproduct inclusion. -/
abbrev tensorChain (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : C.X p) (d : D.X q) :=
  (HomologicalComplex.ιTensorObj C D p q n hpq).hom (c ⊗ₜ[K] d)

/-- A pure tensor of cycles is a cycle in the signed total complex.
Source: Bredon VI Theorem1.5 pp.318–319; node proof K1.
Proof: the total outgoing differential on this injected pure tensor is the
sum of the injected ∂c⊗d and (-1)^p c⊗∂d. Both vanish because c and d
are in the kernels of their actual outgoing differentials. At degree zero
the original down-shape outgoing differentials are zero, so the same result
holds without a negative index. This proves membership for the explicit tensorCycle data. -/
theorem tensor_cycle_mem (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : cycles.{u, u} C p) (d : cycles.{u, u} D q) :
    tensorChain C D p q n hpq c.val d.val ∈ cycles.{u, u} (totalComplex C D) n := by
  classical
  open MonoidalCategory in
  let F := curriedTensor (ModuleCat.{u} K)
  have hc : (C.d p ((ComplexShape.down ℕ).next p)).hom c.val = 0 := c.property
  have hd : (D.d q ((ComplexShape.down ℕ).next q)).hom d.val = 0 := d.property
  change ((totalComplex C D).dFrom n).hom
    ((HomologicalComplex.ιTensorObj C D p q n hpq).hom (c.val ⊗ₜ[K] d.val)) = 0
  change ((HomologicalComplex.ιTensorObj C D p q n hpq) ≫
    (totalComplex C D).d n ((ComplexShape.down ℕ).next n)).hom (c.val ⊗ₜ[K] d.val) = 0
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  have h₁ : (HomologicalComplex.mapBifunctor.d₁ C D F (ComplexShape.down ℕ)
      p q ((ComplexShape.down ℕ).next n)).hom (c.val ⊗ₜ[K] d.val) = 0 := by
    by_cases hp : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)
    · rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hp]
      simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.comp_apply]
      change (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p, q)) • ((HomologicalComplex.ιMapBifunctorOrZero C D F
        (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next p) q
        ((ComplexShape.down ℕ).next n)).hom
        (((C.d p ((ComplexShape.down ℕ).next p)).hom c.val) ⊗ₜ[K] d.val)) = 0
      simp [hc]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hp]
      rfl
  have h₂ : (HomologicalComplex.mapBifunctor.d₂ C D F (ComplexShape.down ℕ)
      p q ((ComplexShape.down ℕ).next n)).hom (c.val ⊗ₜ[K] d.val) = 0 := by
    by_cases hq : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)
    · rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ hq]
      simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.comp_apply]
      change (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p, q)) • ((HomologicalComplex.ιMapBifunctorOrZero C D F
        (ComplexShape.down ℕ) p ((ComplexShape.down ℕ).next q)
        ((ComplexShape.down ℕ).next n)).hom
        (c.val ⊗ₜ[K] ((D.d q ((ComplexShape.down ℕ).next q)).hom d.val))) = 0
      simp [hd]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ hq]
      rfl
  simp only [ModuleCat.hom_add, LinearMap.add_apply]
  dsimp only [F] at h₁ h₂
  rw [h₁, h₂, add_zero]

/-- The original injected tensor, corestricted to the actual cycle kernel.
Source: Bredon VI§1 pp.318–319, cycle formula in the proof of Theorem1.5.
Its value is explicit; the named tensor_cycle_mem theorem supplies only membership. -/
def tensorCycle (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : cycles.{u, u} C p) (d : cycles.{u, u} D q) :
    cycles.{u, u} (totalComplex C D) n :=
  ⟨tensorChain C D p q n hpq c.val d.val, tensor_cycle_mem C D p q n hpq c d⟩

/-- The canonical bilinear map on cycles, prior to dividing out boundaries.
Source: Bredon VI§1, proof of Theorem 1.5, the cycle cross-product formula. -/
private def tensorCycleBilinear (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) :
    cycles.{u, u} C p →ₗ[K] cycles.{u, u} D q →ₗ[K]
      cycles.{u, u} (totalComplex C D) n where
  toFun c :=
    { toFun := fun d ↦ tensorCycle C D p q n hpq c d
      map_add' := fun d e ↦ Subtype.ext (by simp [tensorCycle, tensorChain, TensorProduct.tmul_add])
      map_smul' := fun a d ↦ Subtype.ext (by simp [tensorCycle, tensorChain]) }
  map_add' c e := by
    ext d
    simp [tensorCycle, tensorChain, TensorProduct.add_tmul]
  map_smul' a c := by
    ext d
    simp [tensorCycle, tensorChain, TensorProduct.smul_tmul]

/-- The total differential of a chain tensored with a cycle has only its
first term. Source: Bredon VI§1 Theorem 1.5, K1; the first tensor sign is +1. -/
private theorem tensorChain_d_left (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : C.X (p + 1)) (d : cycles.{u, u} D q) :
    ((totalComplex C D).d (n + 1) n).hom
        (tensorChain C D (p + 1) q (n + 1) (by omega) c d.val) =
      tensorChain C D p q n hpq ((C.d (p + 1) p).hom c) d.val := by
  classical
  open MonoidalCategory in
  let F := curriedTensor (ModuleCat.{u} K)
  change ((HomologicalComplex.ιTensorObj C D (p + 1) q (n + 1) (by omega)) ≫
    (totalComplex C D).d (n + 1) n).hom (c ⊗ₜ[K] d.val) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  have h₂ : (HomologicalComplex.mapBifunctor.d₂ C D F (ComplexShape.down ℕ)
      (p + 1) q n).hom (c ⊗ₜ[K] d.val) = 0 := by
    by_cases hq : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)
    · rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ hq]
      simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.comp_apply]
      change (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p + 1, q)) • ((HomologicalComplex.ιMapBifunctorOrZero C D F
        (ComplexShape.down ℕ) (p + 1) ((ComplexShape.down ℕ).next q) n).hom
        (c ⊗ₜ[K] ((D.d q ((ComplexShape.down ℕ).next q)).hom d.val))) = 0
      have hd : (D.d q ((ComplexShape.down ℕ).next q)).hom d.val = 0 := d.property
      simp [hd]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ hq]
      rfl
  simp only [ModuleCat.hom_add, LinearMap.add_apply]
  dsimp only [F] at h₂
  rw [h₂, add_zero, HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
    (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl) _ _ hpq]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.comp_apply]
  change (1 : ℤˣ) • tensorChain C D p q n hpq ((C.d (p + 1) p).hom c) d.val = _
  exact one_smul _ _

/-- The total differential of a cycle tensored with a chain is the signed
second term. Source: Bredon VI§1 Theorem 1.5, K1; the sign is (-1)^p. -/
private theorem tensorChain_d_right (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : cycles.{u, u} C p) (d : D.X (q + 1)) :
    ((totalComplex C D).d (n + 1) n).hom
        (tensorChain C D p (q + 1) (n + 1) (by omega) c.val d) =
      ((-1 : ℤˣ) ^ p) • tensorChain C D p q n hpq c.val ((D.d (q + 1) q).hom d) := by
  classical
  open MonoidalCategory in
  let F := curriedTensor (ModuleCat.{u} K)
  change ((HomologicalComplex.ιTensorObj C D p (q + 1) (n + 1) (by omega)) ≫
    (totalComplex C D).d (n + 1) n).hom (c.val ⊗ₜ[K] d) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  have h₁ : (HomologicalComplex.mapBifunctor.d₁ C D F (ComplexShape.down ℕ)
      p (q + 1) n).hom (c.val ⊗ₜ[K] d) = 0 := by
    by_cases hp : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)
    · rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hp]
      simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.comp_apply]
      change (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p, q + 1)) • ((HomologicalComplex.ιMapBifunctorOrZero C D F
        (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next p) (q + 1) n).hom
        (((C.d p ((ComplexShape.down ℕ).next p)).hom c.val) ⊗ₜ[K] d)) = 0
      have hc : (C.d p ((ComplexShape.down ℕ).next p)).hom c.val = 0 := c.property
      simp [hc]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hp]
      rfl
  simp only [ModuleCat.hom_add, LinearMap.add_apply]
  dsimp only [F] at h₁
  rw [h₁, zero_add, HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
    (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl) _ hpq]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.comp_apply]
  rfl

/-- An explicit incoming differential gives a boundary in the cycle quotient.
Source: Bredon VI§1; this also fixes the incoming-degree convention at zero. -/
private theorem boundary_iff_exists (C : ChainComplex (ModuleCat.{u} K) ℕ)
    (p : ℕ) (c : cycles.{u, u} C p) :
    c ∈ boundaries.{u, u} C p ↔ ∃ x : C.X (p + 1), (C.d (p + 1) p).hom x = c.val := by
  let h : (ComplexShape.down ℕ).Rel (p + 1) p := rfl
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(C.xPrevIso h).hom.hom x, ?_⟩
    calc
      _ = (C.dTo p).hom x := (ConcreteCategory.congr_hom (C.dTo_eq h) x).symm
      _ = c.val := congrArg Subtype.val hx
  · rintro ⟨x, hx⟩
    refine ⟨(C.xPrevIso h).inv.hom x, Subtype.ext ?_⟩
    exact (ConcreteCategory.congr_hom (C.xPrevIso_comp_dTo h) x).trans hx

/-- Tensoring a boundary with a cycle gives a boundary. The witness is the
injected tensor of a primitive with the cycle. Source: Bredon VI§1, K1. -/
private theorem tensorCycle_boundary_left (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : cycles.{u, u} C p) (d : cycles.{u, u} D q)
    (hc : c ∈ boundaries.{u, u} C p) :
    tensorCycle C D p q n hpq c d ∈ boundaries.{u, u} (totalComplex C D) n := by
  obtain ⟨x, hx⟩ := (boundary_iff_exists C p c).mp hc
  apply (boundary_iff_exists (totalComplex C D) n _).mpr
  refine ⟨tensorChain C D (p + 1) q (n + 1) (by omega) x d.val, ?_⟩
  rw [tensorChain_d_left, hx]
  rfl

/-- Tensoring a cycle with a boundary gives a boundary. Multiplying the
primitive tensor by the inverse sign cancels (-1)^p. Source: Bredon VI§1, K1. -/
private theorem tensorCycle_boundary_right (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : cycles.{u, u} C p) (d : cycles.{u, u} D q)
    (hd : d ∈ boundaries.{u, u} D q) :
    tensorCycle C D p q n hpq c d ∈ boundaries.{u, u} (totalComplex C D) n := by
  obtain ⟨x, hx⟩ := (boundary_iff_exists D q d).mp hd
  apply (boundary_iff_exists (totalComplex C D) n _).mpr
  refine ⟨(((-1 : ℤˣ) ^ p)⁻¹) •
    tensorChain C D p (q + 1) (n + 1) (by omega) c.val x, ?_⟩
  change ((totalComplex C D).d (n + 1) n).hom
    ((↑(((-1 : ℤˣ) ^ p)⁻¹) : ℤ) •
      tensorChain C D p (q + 1) (n + 1) (by omega) c.val x) = _
  rw [map_zsmul, tensorChain_d_right, hx]
  change (((-1 : ℤˣ) ^ p)⁻¹) • (((-1 : ℤˣ) ^ p) •
    tensorChain C D p q n hpq c.val d.val) = _
  rw [inv_smul_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical pairing on the two cycle quotients. The two boundary
identities above supply the quotient lifts, so no complements enter this map.
Source: Bredon VI§1 Theorem 1.5, K1 and the cycle formula on p.319. -/
private def homologyPairing (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) :
    degreeHomology.{u, u} C p →ₗ[K] degreeHomology.{u, u} D q →ₗ[K]
      degreeHomology.{u, u} (totalComplex C D) n := by
  let B := (tensorCycleBilinear C D p q n hpq).compr₂
    (cycleClass.{u, u} (totalComplex C D) n)
  have hC : boundaries.{u, u} C p ≤ B.ker := by
    intro c hc
    apply LinearMap.ext
    intro d
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (tensorCycle_boundary_left C D p q n hpq c d hc)
  let B' := (boundaries.{u, u} C p).liftQ B hC
  have hD : boundaries.{u, u} D q ≤ B'.flip.ker := by
    intro d hd
    apply LinearMap.ext
    intro c
    induction c using Submodule.Quotient.induction_on with
    | _ c =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (tensorCycle_boundary_right C D p q n hpq c d hd)
  exact ((boundaries.{u, u} D q).liftQ B'.flip hD).flip

/-- The forward Künneth map is concrete even before bijectivity is proved.
Source: Bredon VI§1, the natural cross-product map of Theorem 1.5. -/
def kunnethMap (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) :
    homologyTensorSum C D n →ₗ[K] degreeHomology.{u, u} (totalComplex C D) n :=
  DirectSum.toModule K (degreePairs n) _ (fun i ↦
    TensorProduct.lift (homologyPairing C D i.val.1 i.val.2 n i.property))

/-- The canonical map has the specified cycle-class formula. Source: Bredon
VI§1 p.319; both quotient lifts, the tensor lift and the direct-sum lift
reduce to the actual injected tensor on representatives. -/
theorem kunnethMap_representative
    (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n p q : ℕ)
    (hpq : p + q = n) (c : cycles.{u, u} C p) (d : cycles.{u, u} D q) :
    kunnethMap C D n ((DirectSum.lof K (degreePairs n) (homologyTensorFamily C D n)
      ⟨(p, q), hpq⟩) ((cycleClass.{u, u} C p c) ⊗ₜ[K] (cycleClass.{u, u} D q d))) =
      cycleClass.{u, u} (totalComplex C D) n (tensorCycle C D p q n hpq c d) := by
  rw [kunnethMap, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  rfl

/-- The actual degreewise tensor of induced homology maps, followed by the
same-index direct-sum injection and extended by the coproduct universal property.
Source: Bredon VI Theorem1.5 pp.318–320, naturality.
The value on an injected tensor x⊗y is the injected f_*(x)⊗g_*(y). -/
def homologyTensorMap {C D C' D' : ChainComplex (ModuleCat.{u} K) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    homologyTensorSum C D n →ₗ[K] homologyTensorSum C' D' n :=
  DirectSum.toModule K (degreePairs n) (homologyTensorSum C' D' n) (fun i =>
    (DirectSum.lof K (degreePairs n) (homologyTensorFamily C' D' n) i).comp
      (TensorProduct.map (degreeHomologyMap.{u, u} f i.val.1) (degreeHomologyMap.{u, u} g i.val.2)))

/-- Tensoring chain maps takes the tensor of cycles to the tensor of their
images. Source: Bredon VI§1, naturality on cycle representatives (K5). -/
private theorem tensorCycle_naturality
    {C D C' D' : ChainComplex (ModuleCat.{u} K) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (n p q : ℕ) (hpq : p + q = n)
    (c : cycles.{u, u} C p) (d : cycles.{u, u} D q) :
    cycleMap.{u, u} (HomologicalComplex.tensorHom f g) n (tensorCycle C D p q n hpq c d) =
      tensorCycle C' D' p q n hpq (cycleMap.{u, u} f p c) (cycleMap.{u, u} g q d) := by
  apply Subtype.ext
  change ((HomologicalComplex.ιTensorObj C D p q n hpq) ≫
    (HomologicalComplex.tensorHom f g).f n).hom (c.val ⊗ₜ[K] d.val) = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical forward map commutes with every pair of chain maps on every
source element. Source: Bredon VI§1, K5. Direct-sum and tensor generators reduce
this to cycles, where both maps give the class of f(c) tensor g(d). -/
theorem kunnethMap_naturality
    {C D C' D' : ChainComplex (ModuleCat.{u} K) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) (x : homologyTensorSum C D n) :
    degreeHomologyMap.{u, u} (HomologicalComplex.tensorHom f g) n (kunnethMap C D n x) =
      kunnethMap C' D' n (homologyTensorMap f g n x) := by
  have h : (degreeHomologyMap.{u, u} (HomologicalComplex.tensorHom f g) n).comp
      (kunnethMap C D n) = (kunnethMap C' D' n).comp (homologyTensorMap f g n) := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p, q⟩, hpq⟩
    apply TensorProduct.ext'
    intro c d
    obtain ⟨c, rfl⟩ := (show Function.Surjective (cycleClass.{u, u} C p) from
      (boundaries.{u, u} C p).mkQ_surjective) c
    obtain ⟨d, rfl⟩ := (show Function.Surjective (cycleClass.{u, u} D q) from
      (boundaries.{u, u} D q).mkQ_surjective) d
    simp only [LinearMap.comp_apply, homologyTensorMap, DirectSum.toModule_lof,
      TensorProduct.map_tmul]
    rw [kunnethMap_representative]
    change cycleClass.{u, u} (totalComplex C' D') n
      (cycleMap.{u, u} (HomologicalComplex.tensorHom f g) n (tensorCycle C D p q n hpq c d)) =
      kunnethMap C' D' n (DirectSum.lof K (degreePairs n) (homologyTensorFamily C' D' n)
        ⟨(p, q), hpq⟩ (cycleClass.{u, u} C' p (cycleMap.{u, u} f p c) ⊗ₜ[K]
          cycleClass.{u, u} D' q (cycleMap.{u, u} g q d)))
    rw [kunnethMap_representative, tensorCycle_naturality]
  exact LinearMap.congr_fun h x

section HomologyModelBridge
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FieldComplexHomologyModel

private def zeroToCycles (C : ChainComplex (ModuleCat.{u} K) ℕ)
    (hC : ∀ i j, C.d i j = 0) (n : ℕ) : C.X n →ₗ[K] cycles.{u,u} C n :=
  LinearMap.codRestrict _ LinearMap.id (by
    intro x
    change (C.dFrom n).hom x = 0
    simp [HomologicalComplex.dFrom, hC])

private theorem zeroToCycles_bijective (C : ChainComplex (ModuleCat.{u} K) ℕ)
    (hC : ∀ i j, C.d i j = 0) (n : ℕ) :
    Function.Bijective (zeroToCycles C hC n) := by
  constructor
  · intro x y h
    exact congrArg Subtype.val h
  · intro x
    exact ⟨x.val, Subtype.ext rfl⟩

private theorem zeroBoundaries (C : ChainComplex (ModuleCat.{u} K) ℕ)
    (hC : ∀ i j, C.d i j = 0) (n : ℕ) : boundaries.{u,u} C n = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  ext x
  change (C.dTo n).hom x = 0
  simp [HomologicalComplex.dTo, hC]

private def zeroHomologyEquiv (C : ChainComplex (ModuleCat.{u} K) ℕ)
    (hC : ∀ i j, C.d i j = 0) (n : ℕ) : C.X n ≃ₗ[K] degreeHomology.{u,u} C n :=
  LinearEquiv.ofBijective ((cycleClass.{u,u} C n).comp (zeroToCycles C hC n)) (by
    have hb : Function.Bijective (cycleClass.{u,u} C n) := by
      constructor
      · apply LinearMap.ker_eq_bot.mp
        change LinearMap.ker (boundaries.{u,u} C n).mkQ = ⊥
        rw [Submodule.ker_mkQ, zeroBoundaries C hC n]
      · exact (boundaries.{u,u} C n).mkQ_surjective
    exact hb.comp (zeroToCycles_bijective C hC n))

private theorem zeroTensorDifferential (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (hC : ∀ i j, C.d i j = 0) (hD : ∀ i j, D.d i j = 0) :
    ∀ i j, (totalComplex C D).d i j = 0 := by
  intro i j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  have hfirst : HomologicalComplex.mapBifunctor.d₁ C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} K)) (ComplexShape.down ℕ) p q j = 0 := by
    by_cases hp : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)
    · rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hp, hC, Functor.map_zero]
      simp
    · exact HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hp
  have hsecond : HomologicalComplex.mapBifunctor.d₂ C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} K)) (ComplexShape.down ℕ) p q j = 0 := by
    by_cases hq : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)
    · rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ hq, hD, Functor.map_zero]
      simp
    · exact HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ hq
  simp [hfirst, hsecond]


private theorem zeroKunneth_bijective (C D : ChainComplex (ModuleCat.{u} K) ℕ)
    (hC : ∀ i j, C.d i j = 0) (hD : ∀ i j, D.d i j = 0) (n : ℕ) :
    Function.Bijective (kunnethMap C D n) := by
  classical
  let T := fun i : degreePairs n ↦ C.X i.val.1 ⊗[K] D.X i.val.2
  let eH : (⨁ i, T i) ≃ₗ[K] homologyTensorSum C D n :=
    DirectSum.congrLinearEquiv (fun i ↦ TensorProduct.congr
      (zeroHomologyEquiv C hC i.val.1) (zeroHomologyEquiv D hD i.val.2))
  obtain ⟨e, he⟩ := TensorTotalDegreeDirectSum.tensor_total_degree_direct_sum C D n
  let ht := zeroHomologyEquiv (totalComplex C D) (zeroTensorDifferential C D hC hD) n
  have h : (kunnethMap C D n).comp eH.toLinearMap = (e.trans ht).toLinearMap := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p,q⟩, hpq⟩
    apply TensorProduct.ext'
    intro c d
    change kunnethMap C D n (eH (DirectSum.lof K (degreePairs n) T
      ⟨(p,q),hpq⟩ (c ⊗ₜ[K] d))) = ht (e (DirectSum.lof K (degreePairs n) T
      ⟨(p,q),hpq⟩ (c ⊗ₜ[K] d)))
    rw [show eH (DirectSum.lof K (degreePairs n) T ⟨(p,q),hpq⟩ (c ⊗ₜ[K] d)) =
        DirectSum.lof K (degreePairs n) (homologyTensorFamily C D n) ⟨(p,q),hpq⟩
          (zeroHomologyEquiv C hC p c ⊗ₜ[K] zeroHomologyEquiv D hD q d) by
      simp only [eH, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
      rfl]
    change kunnethMap C D n (DirectSum.lof K (degreePairs n)
      (homologyTensorFamily C D n) ⟨(p,q),hpq⟩
      (cycleClass C p (zeroToCycles C hC p c) ⊗ₜ[K]
        cycleClass D q (zeroToCycles D hD q d))) = _
    rw [kunnethMap_representative, he]
    rfl
  have hb : Function.Bijective ((kunnethMap C D n).comp eH.toLinearMap) := by
    rw [h]
    exact (e.trans ht).bijective
  constructor
  · intro x y hxy
    obtain ⟨a,rfl⟩ := eH.surjective x
    obtain ⟨b,rfl⟩ := eH.surjective y
    exact congrArg eH (hb.1 hxy)
  · intro y
    obtain ⟨x,hx⟩ := hb.2 y
    exact ⟨eH x,hx⟩


private theorem homologyTensorMap_bijective {C D C' D' : ChainComplex (ModuleCat.{u} K) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') [QuasiIso f] [QuasiIso g] (n : ℕ) :
    Function.Bijective (homologyTensorMap f g n) := by
  classical
  have he : homologyTensorMap f g n = DirectSum.lmap (fun i : degreePairs n ↦
      TensorProduct.map (degreeHomologyMap.{u,u} f i.val.1)
        (degreeHomologyMap.{u,u} g i.val.2)) := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    simp [homologyTensorMap]
  rw [he]
  constructor
  · apply (DirectSum.lmap_injective _).mpr
    intro i
    exact (TensorProduct.map_bijective (degreeHomologyMap_bijective f i.val.1)
      (degreeHomologyMap_bijective g i.val.2)).1
  · apply (DirectSum.lmap_surjective _).mpr
    intro i
    exact (TensorProduct.map_bijective (degreeHomologyMap_bijective f i.val.1)
      (degreeHomologyMap_bijective g i.val.2)).2

/-- The canonical field Künneth map is bijective. This is the field case of
Bredon, Topology and Geometry, VI Theorem 1.5, pp.318–320. The proof here uses
chain homotopy models: choose cycle representatives for each homology group,
forming a zero-differential complex and a quasi-isomorphism to the original.
Over a field every term is projective, so this quasi-isomorphism is a chain
homotopy equivalence. Tensoring the two equivalences remains a homotopy
equivalence. For zero-differential complexes every chain is a cycle and every
boundary is zero, so the stated map is exactly the direct-sum decomposition
of the tensor degree. Naturality transports its bijectivity to the original
complexes. No dimension, characteristic, or positive-degree assumption is used. -/
theorem kunnethMap_bijective_bridge (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) :
    Function.Bijective (kunnethMap C D n) := by
  let : QuasiIso (inclusion C) := inclusion_quasiIso C
  let : QuasiIso (inclusion D) := inclusion_quasiIso D
  obtain ⟨e,he⟩ := inclusion_homotopyEquivalence C
  obtain ⟨f,hf⟩ := inclusion_homotopyEquivalence D
  have ht : Function.Bijective (degreeHomologyMap.{u,u}
      (HomologicalComplex.tensorHom (inclusion C) (inclusion D)) n) := by
    rw [← he, ← hf]
    exact degreeHomologyMap_bijective (tensorHomotopyEquiv e f).hom n
  have hs := homologyTensorMap_bijective (inclusion C) (inclusion D) n
  have hz := zeroKunneth_bijective (model C) (model D) (by intros; rfl) (by intros; rfl) n
  have hcomm : (kunnethMap C D n).comp (homologyTensorMap (inclusion C) (inclusion D) n) =
      (degreeHomologyMap.{u,u} (HomologicalComplex.tensorHom (inclusion C) (inclusion D)) n).comp
        (kunnethMap (model C) (model D) n) := by
    apply LinearMap.ext
    intro x
    exact (kunnethMap_naturality (inclusion C) (inclusion D) n x).symm
  have hb : Function.Bijective ((kunnethMap C D n).comp
      (homologyTensorMap (inclusion C) (inclusion D) n)) := by
    rw [hcomm]
    exact ht.comp hz
  constructor
  · intro x y hxy
    obtain ⟨a,rfl⟩ := hs.2 x
    obtain ⟨b,rfl⟩ := hs.2 y
    exact congrArg (homologyTensorMap (inclusion C) (inclusion D) n) (hb.1 hxy)
  · intro y
    obtain ⟨x,hx⟩ := hb.2 y
    exact ⟨homologyTensorMap (inclusion C) (inclusion D) n x,hx⟩

end HomologyModelBridge

/-- The natural field Künneth isomorphism, with its exact cycle-class formula.

Source: Bredon, *Topology and Geometry*, VI Theorem 1.5, pp.318–320,
including the field specialization on p.320. The formal bijectivity proof is
the independent homology-model argument of
`linear.field_tensor_kunneth_bijective_bridge_g4`.

The tensor differential sends a tensor of cycles to zero, a boundary tensored
with a cycle to a boundary, and a cycle tensored with a boundary to a boundary
with the invertible sign (-1)^p. Hence the bilinear cycle pairing descends to
both homology quotients and then extends over tensor products and the direct
sum. This gives the canonical map [c]⊗[d] ↦ [c⊗d].

Choose linear cycle representatives for each homology space. They define a
chain map from the zero-differential homology complex to the original complex,
and induce the identity on homology. Over a field every module is projective;
for these nonnegative complexes this quasi-isomorphism has a chain homotopy
inverse. Tensoring the two homotopy equivalences gives a homotopy equivalence
of their totals, hence a bijection on total homology. On zero-differential
complexes the canonical map is the actual direct-sum coordinate equivalence
of the tensor-total degree, since all vectors are cycles and all boundaries
vanish. Naturality gives a commuting square whose other three maps are
bijective, so the original canonical map is bijective. Form its linear
inverse without changing its forward map. On cycle tensors, both naturality
composites give the class of f(c)⊗g(d); quotient, tensor, and direct-sum
generation extend this identity to every element.

No step requires finite dimension, positive degree, or a characteristic
restriction. The endpoint differential is zero, and each tensor or direct-sum
element has finite support even when the complexes are unbounded. -/
theorem field_chain_tensor_homology_kunneth_same_universe :
    ∃ κ : ∀ (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ),
      homologyTensorSum C D n ≃ₗ[K] degreeHomology.{u, u} (totalComplex C D) n,
      (∀ (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n p q : ℕ)
        (hpq : p + q = n) (c : cycles.{u, u} C p) (d : cycles.{u, u} D q),
        κ C D n ((DirectSum.lof K (degreePairs n) (homologyTensorFamily C D n)
          ⟨(p, q), hpq⟩) ((cycleClass.{u, u} C p c) ⊗ₜ[K] (cycleClass.{u, u} D q d))) =
          cycleClass.{u, u} (totalComplex C D) n (tensorCycle C D p q n hpq c d)) ∧
      (∀ (C D C' D' : ChainComplex (ModuleCat.{u} K) ℕ)
        (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) (x : homologyTensorSum C D n),
        degreeHomologyMap.{u, u} (HomologicalComplex.tensorHom f g) n (κ C D n x) =
          κ C' D' n (homologyTensorMap f g n x)) := by
  suffices hbij : ∀ (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ),
      Function.Bijective (kunnethMap C D n) by
    refine ⟨fun C D n ↦ LinearEquiv.ofBijective (kunnethMap C D n) (hbij C D n), ?_, ?_⟩
    · intro C D n p q hpq c d
      exact kunnethMap_representative C D n p q hpq c d
    · intro C D C' D' f g n x
      exact kunnethMap_naturality f g n x
  exact kunnethMap_bijective_bridge

namespace ArbitraryUniverse

/-- Change only the scalar presentation to the lifted copy of K. Its action is
r • m = r.down • m; its morphisms are the original linear maps. Source: Bredon
VI§1 pp.318–320 is invariant under a field isomorphism; Mathlib
`ULift.ringEquiv` and `ModuleCat.restrictScalars` implement this presentation. -/
abbrev liftScalars : ModuleCat.{max u v} K ⥤ ModuleCat.{max u v} (ULift.{v} K) :=
  ModuleCat.restrictScalars (ULift.ringEquiv (R := K)).toRingHom

/-- Return from the lifted scalar presentation to the ORIGINAL field K.
The action of a ∈ K is through ULift.up a. Source: Bredon VI§1 pp.318–320;
Mathlib `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`. -/
abbrev originalScalars : ModuleCat.{max u v} (ULift.{v} K) ⥤ ModuleCat.{max u v} K :=
  ModuleCat.restrictScalars (ULift.ringEquiv (R := K)).symm.toRingHom

private def restrictLiftedLinearEquiv
    (M N : ModuleCat.{max u v} (ULift.{v} K)) (e : M ≃ₗ[ULift.{v} K] N) :
    originalScalars.{u, v}.obj M ≃ₗ[K] originalScalars.{u, v}.obj N where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' a x := e.map_smul (ULift.up a) x

/-- Scalar restriction preserves the value of a linear equivalence. Source: Bredon VI§1, change of field presentation; this is definitional. -/
private theorem restrictLiftedLinearEquiv_apply
    (M N : ModuleCat.{max u v} (ULift.{v} K)) (e : M ≃ₗ[ULift.{v} K] N)
    (x : originalScalars.{u, v}.obj M) :
    restrictLiftedLinearEquiv.{u, v} M N e x = e x := rfl

/-- The same original differential and carriers, now linear over ULift K.
Source: Bredon VI§1 pp.318–320; scalar restriction acts on each differential
and has no dimension or boundedness premise. -/
abbrev liftComplex (C : ChainComplex (ModuleCat.{max u v} K) ℕ) :=
  (liftScalars.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- The signed tensor total of the actual lifted-field complexes, returned to
K by restriction of scalars. This is a concrete tensor-complex representation,
not a chosen chain complex or an assumed isomorphism. Source: Bredon VI§1
pp.318–320; the total degree/signs are p+q and 1,(-1)^p as above.
The field ULift K and the carriers now share max u v. -/
abbrev totalComplex (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) :=
  (originalScalars.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (HomologicalComplex.tensorObj (liftComplex.{u, v} C) (liftComplex D))

/-- The original degreewise homology tensors over K, with no scalar replacement.
Source: Bredon VI§1 Theorem1.5 pp.318–320. -/
abbrev homologyTensorFamily (C D : ChainComplex (ModuleCat.{max u v} K) ℕ)
    (n : ℕ) (i : degreePairs n) :=
  degreeHomology.{u, v} C i.val.1 ⊗[K] degreeHomology.{u, v} D i.val.2

/-- The original K-linear direct sum in degree n. Source: Bredon VI§1 p.318. -/
abbrev homologyTensorSum (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) (n : ℕ) :=
  ⨁ i : degreePairs n, homologyTensorFamily.{u, v} C D n i

/-- The pure tensor of ORIGINAL vectors, in its concrete lifted-scalar summand.
Source: Bredon VI§1 pp.318–319. The scalar lift changes no vector or differential;
the named comparison below certifies the original K-tensor universal property. -/
abbrev tensorChain (C D : ChainComplex (ModuleCat.{max u v} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : C.X p) (d : D.X q) :
    (totalComplex.{u, v} C D).X n :=
  (HomologicalComplex.ιTensorObj (liftComplex.{u, v} C) (liftComplex D) p q n hpq).hom
    (c ⊗ₜ[ULift.{v} K] d)

set_option backward.isDefEq.respectTransparency false in
/-- The concrete scalar-lift summand is the ORIGINAL tensor product over K.
Source: Bredon VI§1 pp.318–320, tensor universal property; Mathlib
`TensorProduct.equivOfCompatibleSMul` preserves every pure tensor.
Proof: both actions are given by r.down on each original module. They commute
because K is commutative. A lifted scalar can move between tensor factors
exactly as its down scalar; conversely a K scalar moves as its up scalar.
Thus CompatibleSMul holds in both directions. The compatible-scalar tensor
equivalence sends c⊗d to c⊗d, and is K-linear since up(a).down=a.
Its inverse has the same generator formula; compositions are identity on pure
tensors, hence on all finite sums. This certifies an actual comparison, rather
than assuming that changing the scalar field leaves a tensor product unchanged. -/
theorem tensor_summand_comparison (M N : ModuleCat.{max u v} K) :
    ∃ e : (M ⊗[K] N) ≃ₗ[K]
      (originalScalars.{u, v}.obj
        (ModuleCat.of (ULift.{v} K)
          ((liftScalars.{u, v}.obj M) ⊗[ULift.{v} K] (liftScalars.{u, v}.obj N)))),
      ∀ (m : M) (n : N), e (m ⊗ₜ[K] n) = m ⊗ₜ[ULift.{v} K] n := by
  let instM : Module (ULift.{v} K) M := Module.compHom M (ULift.ringEquiv (R := K)).toRingHom
  let instN : Module (ULift.{v} K) N := Module.compHom N (ULift.ringEquiv (R := K)).toRingHom
  let commKL : SMulCommClass K (ULift.{v} K) M := ⟨fun a b m => smul_comm a b.down m⟩
  let commLK : SMulCommClass (ULift.{v} K) K M := ⟨fun a b m => smul_comm a.down b m⟩
  let compatKL : TensorProduct.CompatibleSMul K (ULift.{v} K) M N :=
    ⟨fun a m n => TensorProduct.smul_tmul a.down m n⟩
  let commLL : SMulCommClass (ULift.{v} K) (ULift.{v} K) M :=
    ⟨fun a b m => smul_comm a.down b.down m⟩
  let compatLL : TensorProduct.CompatibleSMul (ULift.{v} K) (ULift.{v} K) M N :=
    TensorProduct.CompatibleSMul.isScalarTower
  let compatLK : TensorProduct.CompatibleSMul (ULift.{v} K) K M N :=
    ⟨fun a m n => compatLL.smul_tmul (ULift.up a) m n⟩
  let e : (M ⊗[K] N) ≃ₗ[K] (M ⊗[ULift.{v} K] N) :=
    TensorProduct.equivOfCompatibleSMul (ULift.{v} K) K K M N
  refine ⟨?_, ?_⟩
  · exact e
  · intro m n
    rfl

private noncomputable def tensorDirectSumScalarComparison {ι : Type*}
    (M N : ι → ModuleCat.{max u v} K) :
    (⨁ i, M i ⊗[K] N i) ≃ₗ[K]
      (⨁ i, originalScalars.{u, v}.obj
        (ModuleCat.of (ULift.{v} K)
          ((liftScalars.{u, v}.obj (M i)) ⊗[ULift.{v} K]
            (liftScalars.{u, v}.obj (N i))))) := by
  classical
  exact DirectSum.congrLinearEquiv (fun i ↦
    Classical.choose (tensor_summand_comparison.{u, v} (M i) (N i)))

/-- Original cycles have zero differential also in the concrete scalar-lift total.
Source: Bredon VI§1 pp.318–319, K1 of the full node proof above.
Proof: scalar restriction leaves differentials as the original functions.
The total differential of c⊗d is the injected dc⊗d+(-1)^p c⊗dd,
which is zero for original cycles. Degree0 uses the zero outgoing differential.
No scalar or quotient comparison is an input assumption. -/
theorem tensor_cycle_mem (C D : ChainComplex (ModuleCat.{max u v} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : cycles.{u, v} C p) (d : cycles.{u, v} D q) :
    tensorChain.{u, v} C D p q n hpq c.val d.val ∈ cycles.{u, v} (totalComplex.{u, v} C D) n := by
  let c' : cycles (liftComplex.{u, v} C) p := ⟨c.val, c.property⟩
  let d' : cycles (liftComplex.{u, v} D) q := ⟨d.val, d.property⟩
  exact HolomorphicAnosov.FieldTensorHomologyKunneth.tensor_cycle_mem
    (liftComplex.{u, v} C) (liftComplex.{u, v} D) p q n hpq c' d'

/-- The actual injected tensor, with its proved kernel membership.
Source: Bredon VI§1 pp.318–319. -/
def tensorCycle (C D : ChainComplex (ModuleCat.{max u v} K) ℕ)
    (p q n : ℕ) (hpq : p + q = n) (c : cycles.{u, v} C p) (d : cycles.{u, v} D q) :
    cycles.{u, v} (totalComplex.{u, v} C D) n :=
  ⟨tensorChain.{u, v} C D p q n hpq c.val d.val, tensor_cycle_mem.{u, v} C D p q n hpq c d⟩

/-- The actual tensor of the two original chain maps in the scalar-lift total.
Source: Bredon VI§1 pp.318–320; functorial scalar restriction keeps their values. -/
abbrev totalMap {C D C' D' : ChainComplex (ModuleCat.{max u v} K) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') :=
  (originalScalars.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (HomologicalComplex.tensorHom
      ((liftScalars.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).map f)
      ((liftScalars.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).map g))

/-- The degreewise tensors of the ORIGINAL induced K-homology maps.
Source: Bredon VI§1 pp.318–320, naturality. -/
def homologyTensorMap {C D C' D' : ChainComplex (ModuleCat.{max u v} K) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    homologyTensorSum.{u, v} C D n →ₗ[K] homologyTensorSum.{u, v} C' D' n :=
  DirectSum.toModule K (degreePairs n) (homologyTensorSum.{u, v} C' D' n) (fun i ↦
    (DirectSum.lof K (degreePairs n) (homologyTensorFamily.{u, v} C' D' n) i).comp
      (TensorProduct.map (degreeHomologyMap.{u, v} f i.val.1)
        (degreeHomologyMap.{u, v} g i.val.2)))

set_option backward.isDefEq.respectTransparency false in
/-- Identity on original cycle representatives and on their actual quotient.
Source: Bredon VI§1 pp.318–320; the scalar transport argument of the public
independent-universe theorem. The differential functions and boundary witnesses
are unchanged by restriction, so the quotient relation is the same relation. -/
private def homologyScalarComparison (C : ChainComplex (ModuleCat.{max u v} K) ℕ)
    (n : ℕ) : degreeHomology.{u, v} C n ≃ₗ[K]
      (originalScalars.{u, v}.obj (ModuleCat.of (ULift.{v} K)
        (degreeHomology (liftComplex.{u, v} C) n))) := by
  exact LinearEquiv.refl K _

set_option backward.isDefEq.respectTransparency false in
/-- Changing from ULift K to K preserves pure tensors. Source: the tensor universal property used in Bredon VI§1. Both scalar actions correspond under up/down, so the compatible-scalar tensor equivalence applies in both directions. -/
private def restrictTensorComparison (M N : ModuleCat.{max u v} (ULift.{v} K)) :
    ((originalScalars.{u, v}.obj M) ⊗[K] (originalScalars.{u, v}.obj N)) ≃ₗ[K]
      originalScalars.{u, v}.obj (ModuleCat.of (ULift.{v} K) (M ⊗[ULift.{v} K] N)) := by
  let instM : Module K M := Module.compHom M (ULift.ringEquiv (R := K)).symm.toRingHom
  let instN : Module K N := Module.compHom N (ULift.ringEquiv (R := K)).symm.toRingHom
  let commKL : SMulCommClass K (ULift.{v} K) M :=
    ⟨fun a b m ↦ smul_comm (ULift.up a) b m⟩
  let commLK : SMulCommClass (ULift.{v} K) K M :=
    ⟨fun a b m ↦ smul_comm a (ULift.up b) m⟩
  let compatKL : TensorProduct.CompatibleSMul K (ULift.{v} K) M N :=
    ⟨fun a m n ↦ TensorProduct.smul_tmul a.down m n⟩
  let compatLK : TensorProduct.CompatibleSMul (ULift.{v} K) K M N :=
    ⟨fun a m n ↦ TensorProduct.smul_tmul (ULift.up a) m n⟩
  exact TensorProduct.equivOfCompatibleSMul (ULift.{v} K) K K M N

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction commutes with this finite-support direct sum. Source: the direct-sum universal property in Bredon VI§1; the map and inverse are the identity on every coordinate. -/
private def restrictDirectSumComparison {n : ℕ}
    (M : degreePairs n → ModuleCat.{max u v} (ULift.{v} K)) :
    (⨁ i, originalScalars.{u, v}.obj (M i)) ≃ₗ[K]
      originalScalars.{u, v}.obj (ModuleCat.of (ULift.{v} K) (⨁ i, M i)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compare the original homology tensor sum with the lifted-scalar sum. Source: Bredon VI§1 and its tensor universal property. Tensor the identity-on-classes homology comparisons, apply compatible scalar restriction in each summand, and combine them by the direct-sum equivalence. -/
private def homologyTensorScalarComparison
    (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) (n : ℕ) :
    homologyTensorSum.{u, v} C D n ≃ₗ[K]
      originalScalars.{u, v}.obj (ModuleCat.of (ULift.{v} K)
        (HolomorphicAnosov.FieldTensorHomologyKunneth.homologyTensorSum
          (liftComplex.{u, v} C) (liftComplex.{u, v} D) n)) := by
  let M := fun i : degreePairs n ↦ ModuleCat.of (ULift.{v} K)
    (degreeHomology.{max u v, max u v} (liftComplex.{u, v} C) i.val.1)
  let N := fun i : degreePairs n ↦ ModuleCat.of (ULift.{v} K)
    (degreeHomology.{max u v, max u v} (liftComplex.{u, v} D) i.val.2)
  exact (DirectSum.congrLinearEquiv (fun i : degreePairs n ↦
    (TensorProduct.congr (homologyScalarComparison.{u, v} C i.val.1)
      (homologyScalarComparison.{u, v} D i.val.2)).trans
        (restrictTensorComparison.{u, v} (M i) (N i)))).trans
    (restrictDirectSumComparison.{u, v} (fun i ↦
      ModuleCat.of (ULift.{v} K) ((M i) ⊗[ULift.{v} K] (N i))))

/-- The homology tensor scalar comparison fixes all original cycle representatives. Source: Bredon VI§1; each quotient comparison fixes classes, each tensor comparison fixes pure tensors, and the direct-sum comparison fixes the injection. -/
private theorem homologyTensorScalarComparison_representative
    (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) (n p q : ℕ)
    (hpq : p + q = n) (c : cycles.{u, v} C p) (d : cycles.{u, v} D q) :
    homologyTensorScalarComparison.{u, v} C D n
      (DirectSum.lof K (degreePairs n) (homologyTensorFamily.{u, v} C D n)
        ⟨(p, q), hpq⟩ (cycleClass.{u, v} C p c ⊗ₜ[K] cycleClass.{u, v} D q d)) =
      DirectSum.lof (ULift.{v} K) (degreePairs n)
        (HolomorphicAnosov.FieldTensorHomologyKunneth.homologyTensorFamily
          (liftComplex.{u, v} C) (liftComplex.{u, v} D) n) ⟨(p, q), hpq⟩
        (cycleClass.{max u v, max u v} (liftComplex.{u, v} C) p ⟨c.val, c.property⟩
          ⊗ₜ[ULift.{v} K]
          cycleClass.{max u v, max u v} (liftComplex.{u, v} D) q ⟨d.val, d.property⟩) := by
  simp only [homologyTensorScalarComparison, LinearEquiv.trans_apply,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along ULift.up preserves the concrete cycle quotient. Source: Bredon VI§1, invariance under a field isomorphism. The underlying vectors, differentials, boundary relation and quotient representatives are identical. -/
private def restrictedHomologyComparison
    (C : ChainComplex (ModuleCat.{max u v} (ULift.{v} K)) ℕ) (n : ℕ) :
    degreeHomology.{u, v}
      ((originalScalars.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) n ≃ₗ[K]
      originalScalars.{u, v}.obj (ModuleCat.of (ULift.{v} K)
        (degreeHomology.{max u v, max u v} C n)) := by
  exact LinearEquiv.refl K _

/-- The inverse restricted homology comparison fixes a cycle class. Source: Bredon VI§1, scalar-presentation invariance; both maps act identically on quotient representatives. -/
private theorem restrictedHomologyComparison_symm_cycleClass
    (C : ChainComplex (ModuleCat.{max u v} (ULift.{v} K)) ℕ) (n : ℕ)
    (c : cycles.{max u v, max u v} C n) :
    (restrictedHomologyComparison.{u, v} C n).symm
        (cycleClass.{max u v, max u v} C n c) =
      cycleClass.{u, v}
        ((originalScalars.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).obj C)
        n ⟨c.val, c.property⟩ := rfl

/-- The restriction comparison specialized to the actual tensor total. Source: Bredon VI§1, scalar-presentation invariance. -/
private abbrev totalHomologyScalarComparison
    (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) (n : ℕ) :=
  restrictedHomologyComparison.{u, v}
    (HolomorphicAnosov.FieldTensorHomologyKunneth.totalComplex
      (liftComplex.{u, v} C) (liftComplex.{u, v} D)) n

end ArbitraryUniverse

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The field Künneth theorem with INDEPENDENT field and module universes.

Source: Bredon VI§1 Theorem1.5 pp.318–320. The homology-model proof is
written above on field_chain_tensor_homology_kunneth_same_universe. Here is the
complete transport argument for its concrete larger-universe representation.

Put w=max u v and K'=ULift.{v} K. The functor liftScalars leaves every vector,
differential and chain-map value unchanged; it changes a scalar r to r.down.
The field K' and all carriers have universe w, so the same-universe source
component applies to these actual lifted complexes. Kernels are the same sets
of original vectors because the differential functions are unchanged; incoming
boundary-in-cycle ranges are the same sets because their witnesses and maps
are unchanged. The map on their quotients sends each original cycle class to
the same class in the lifted presentation. It is additive and K-linear after
originalScalars, with inverse the same representative map. Well-definedness
uses the identical boundary relation; the two composites are identity on all
quotient representatives. This supplies the homology comparison, without
postulating it or duplicating the original kernel/image definition.

For each homology summand, tensor_summand_comparison supplies the K-linear
comparison between the original K tensor and the lifted-field tensor. The
DirectSum universal property combines these comparisons and their inverses
coordinatewise; finitely supported elements remain finitely supported, so this
is an equivalence even for unbounded complexes and arbitrary-dimensional spaces.
Compose it with the same-universe K' Künneth equivalence and with the original
K-linear total-homology comparison. The resulting map has exactly the displayed
original cycle-class formula. Its target totalComplex is concrete: each graded
summand is canonically the original C_p⊗[K]D_q by the named summand comparison;
the comparison commutes with both differential terms on pure tensors and hence
every element, preserving degree p+q and sign (-1)^p. Thus it represents the
original signed tensor complex, not a different tensor notion.

All comparison maps send representatives to the same representatives and pure
tensors to the same pure tensors. They commute with both original chain maps
by those formulas; quotient, tensor and direct-sum generators then establish
naturality on EVERY source element. The chosen isomorphism is an output,
not an input. Degree0, zero complexes, characteristic2, unbounded degrees and
arbitrary dimension are included. The scalar comparison is explicit on
representatives; no additional algebraic hypothesis is used.
-/
theorem field_chain_tensor_homology_kunneth :
    ∃ κ : ∀ (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) (n : ℕ),
      ArbitraryUniverse.homologyTensorSum.{u, v} (K := K) C D n ≃ₗ[K]
        degreeHomology.{u, v} (ArbitraryUniverse.totalComplex.{u, v} (K := K) C D) n,
      (∀ (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) (n p q : ℕ)
        (hpq : p + q = n) (c : cycles.{u, v} C p) (d : cycles.{u, v} D q),
        κ C D n ((DirectSum.lof K (degreePairs n)
          (ArbitraryUniverse.homologyTensorFamily.{u, v} (K := K) C D n) ⟨(p, q), hpq⟩)
          ((cycleClass.{u, v} C p c) ⊗ₜ[K] (cycleClass.{u, v} D q d))) =
          cycleClass.{u, v} (ArbitraryUniverse.totalComplex.{u, v} (K := K) C D) n
            (ArbitraryUniverse.tensorCycle.{u, v} (K := K) C D p q n hpq c d)) ∧
      (∀ (C D C' D' : ChainComplex (ModuleCat.{max u v} K) ℕ)
        (f : C ⟶ C') (g : D ⟶ D') (n : ℕ)
        (x : ArbitraryUniverse.homologyTensorSum.{u, v} (K := K) C D n),
        degreeHomologyMap.{u, v} (ArbitraryUniverse.totalMap.{u, v} (K := K) f g) n (κ C D n x) =
          κ C' D' n (ArbitraryUniverse.homologyTensorMap.{u, v} (K := K) f g n x)) := by
  classical
  obtain ⟨κ, hκrep, hκnat⟩ :=
    field_chain_tensor_homology_kunneth_same_universe (K := ULift.{v} K)
  let e (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) (n : ℕ) :=
    (ArbitraryUniverse.homologyTensorScalarComparison.{u, v} C D n).trans
      ((ArbitraryUniverse.restrictLiftedLinearEquiv.{u, v} _ _
        (κ (ArbitraryUniverse.liftComplex.{u, v} C)
          (ArbitraryUniverse.liftComplex.{u, v} D) n)).trans
        (ArbitraryUniverse.totalHomologyScalarComparison.{u, v} C D n).symm)
  have he (C D : ChainComplex (ModuleCat.{max u v} K) ℕ) (n p q : ℕ)
      (hpq : p + q = n) (c : cycles.{u, v} C p) (d : cycles.{u, v} D q) :
      e C D n ((DirectSum.lof K (degreePairs n)
        (ArbitraryUniverse.homologyTensorFamily.{u, v} C D n) ⟨(p, q), hpq⟩)
        ((cycleClass.{u, v} C p c) ⊗ₜ[K] (cycleClass.{u, v} D q d))) =
        cycleClass.{u, v} (ArbitraryUniverse.totalComplex.{u, v} C D) n
          (ArbitraryUniverse.tensorCycle.{u, v} C D p q n hpq c d) := by
    simp only [e, LinearEquiv.trans_apply,
      ArbitraryUniverse.restrictLiftedLinearEquiv_apply]
    rw [ArbitraryUniverse.homologyTensorScalarComparison_representative, hκrep]
    rw [ArbitraryUniverse.totalHomologyScalarComparison,
      ArbitraryUniverse.restrictedHomologyComparison_symm_cycleClass]
    rfl
  refine ⟨e, he, ?_⟩
  intro C D C' D' f g n x
  have h : (degreeHomologyMap.{u, v} (ArbitraryUniverse.totalMap.{u, v} f g) n).comp
      (e C D n).toLinearMap =
      (e C' D' n).toLinearMap.comp (ArbitraryUniverse.homologyTensorMap.{u, v} f g n) := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p, q⟩, hpq⟩
    apply TensorProduct.ext'
    intro c d
    obtain ⟨c, rfl⟩ := (show Function.Surjective (cycleClass.{u, v} C p) from
      (boundaries.{u, v} C p).mkQ_surjective) c
    obtain ⟨d, rfl⟩ := (show Function.Surjective (cycleClass.{u, v} D q) from
      (boundaries.{u, v} D q).mkQ_surjective) d
    simp only [LinearMap.comp_apply, ArbitraryUniverse.homologyTensorMap,
      DirectSum.toModule_lof, TensorProduct.map_tmul, LinearEquiv.coe_coe]
    rw [he]
    change cycleClass.{u, v} (ArbitraryUniverse.totalComplex.{u, v} C' D') n
      (cycleMap.{u, v} (ArbitraryUniverse.totalMap.{u, v} f g) n
        (ArbitraryUniverse.tensorCycle.{u, v} C D p q n hpq c d)) =
      e C' D' n (DirectSum.lof K (degreePairs n)
        (ArbitraryUniverse.homologyTensorFamily.{u, v} C' D' n)
        ⟨(p, q), hpq⟩ (cycleClass.{u, v} C' p (cycleMap.{u, v} f p c) ⊗ₜ[K]
          cycleClass.{u, v} D' q (cycleMap.{u, v} g q d)))
    rw [he]
    congr 1
    apply Subtype.ext
    change ((HomologicalComplex.ιTensorObj
      (ArbitraryUniverse.liftComplex.{u, v} C)
      (ArbitraryUniverse.liftComplex.{u, v} D) p q n hpq) ≫
      (HomologicalComplex.tensorHom
        ((ArbitraryUniverse.liftScalars.{u, v}.mapHomologicalComplex
          (ComplexShape.down ℕ)).map f)
        ((ArbitraryUniverse.liftScalars.{u, v}.mapHomologicalComplex
          (ComplexShape.down ℕ)).map g)).f n).hom
      (c.val ⊗ₜ[ULift.{v} K] d.val) = _
    rw [HomologicalComplex.ι_mapBifunctorMap]
    rfl
  exact LinearMap.congr_fun h x


end HolomorphicAnosov.FieldTensorHomologyKunneth


