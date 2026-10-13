import HolomorphicAnosov.Topology.Homology.SingularProductTensorConstruction
import HolomorphicAnosov.Topology.Homology.RationalScalarTransport
import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Natural comparison from product singular chains to tensor chains

Source: Bredon, *Topology and Geometry* (1993), VI Theorems 1.2 and 1.3,
pp.316–318. This is the product-source, tensor-target case whose induction
is written in full, independently of the signed shuffle.
DAG node: `topo.singular_product_tensor_comparison_g19`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped Simplicial TensorProduct
noncomputable section
universe u
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.RationalScalarTransport

/-- The natural product-to-tensor comparison exists, and any two normalized
natural comparisons in this direction are naturally chain homotopic.

Source: Bredon (1993), VI1.2 pp.316–317 and the fully written case of VI1.3
pp.317–318; local `literature/Bredon-Topology-and-Geometry-1993.txt`,
lines 9297–9348. The native lifted rational coefficient retains coefficient one.

Proof: put θ₀[(x,y)]=[x]⊗[y]. Suppose θ is natural and commutes with the
differential below n>0. On the diagonal model simplex dₙ:Δⁿ→Δⁿ×Δⁿ,
the chain z=θₙ₋₁(∂dₙ) is a cycle, since the lower differential identity
and ∂²=0 give ∂z=0. If n=1 its augmentation is zero: the two boundary
vertices each have coefficient one and occur with opposite signs. The
tensor contraction on the convex model therefore fills z. Choose its
contraction image cₙ with ∂cₙ=z. Every singular simplex σ:Δⁿ→X×Y
is the pushforward of dₙ under (πₓσ,πᵧσ). Define θₙσ by the corresponding
tensor pushforward of cₙ and extend linearly. Composition of pushforwards
gives naturality. Commuting the differential with pushforward and applying
lower-degree naturality to the individual faces gives ∂θₙσ=θₙ₋₁∂σ.

For uniqueness, naturality under point inclusions makes the two normalized
maps agree on every degree-zero generator, so start H₀=0. Assuming the
homotopy identity below n>0, evaluate z=(Φ−Ψ−H∂)(dₙ). Its boundary is
zero: the chain-map identities replace ∂(Φ−Ψ) by (Φ−Ψ)∂, and the previous
homotopy equation cancels this against ∂H∂, with the remaining term H∂²=0.
The positive-degree tensor-model contraction fills z. Define Hₙ on the
model by this filling and on every σ by its two coordinate pushforwards.
Linearity and pushforward composition prove the homotopy identity and its
all-degree naturality. Put off-shape homotopy components equal to zero.
These constructions are on fixed convex models only, so arbitrary spaces
need no contractibility, separation, finiteness, or nonemptiness assumption.
The construction is proved directly for every commutative coefficient ring
in the same universe as the spaces. The convex models are lifted by ULift;
the original continuous cone is conjugated by ULift.up and ULift.down, so its
face identities are unchanged. Specializing the coefficient ring to LiftQ
gives precisely the native complexes displayed below.
-/
theorem singular_product_tensor_comparison :
    let C : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ :=
      (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} LiftQ.{u})).obj
        (ModuleCat.of LiftQ.{u} LiftQ.{u})
    let A := tensor TopCat.{u} ⋙ C
    let T := (C.prod C) ⋙ tensor (ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ)
    let point : TopCat.{u} := TopCat.of PUnit
    let pp := (point, point)
    let g := ((TopCat.toSSet.obj point).ιChainComplex (R := ModuleCat.of LiftQ.{u} LiftQ.{u})
      ((TopCat.toSSetObjEquiv point (Opposite.op ⦋0⦌)).symm
        (ContinuousMap.const _ PUnit.unit))).hom (ULift.up 1 : LiftQ.{u})
    let gA := ((TopCat.toSSet.obj (TopCat.of (point × point))).ιChainComplex (R := ModuleCat.of LiftQ.{u} LiftQ.{u})
      ((TopCat.toSSetObjEquiv (TopCat.of (point × point)) (Opposite.op ⦋0⦌)).symm
        (ContinuousMap.const _ (PUnit.unit, PUnit.unit)))).hom (ULift.up 1 : LiftQ.{u})
    let gT := (HomologicalComplex.ιTensorObj (C.obj point) (C.obj point) 0 0 0 rfl)
      (g ⊗ₜ[LiftQ.{u}] g)
    (∃ θ : A ⟶ T, (θ.app pp).f 0 gA = gT) ∧
    (∀ (Φ Ψ : A ⟶ T),
      (Φ.app pp).f 0 gA = gT → (Ψ.app pp).f 0 gA = gT →
      ∃ H : ∀ xy, _root_.Homotopy (Φ.app xy) (Ψ.app xy),
        (∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
          (A.map f).f i ≫ (H xy').hom i j = (H xy).hom i j ≫ (T.map f).f j) ∧
        (∀ xy, (H xy).hom 0 1 = 0)) := by
  dsimp only
  constructor
  · obtain ⟨θ, hθ⟩ := SingularProductTensor.exists_comparison LiftQ.{u}
    refine ⟨θ, ?_⟩
    change (θ.app SingularProductGenerator.pointPair).f 0
      ((TopCat.toSSet.obj (SingularProductGenerator.point ⊗ SingularProductGenerator.point)).ιChainComplex
        (R := SingularProductGenerator.coeff LiftQ.{u})
        SingularProductGenerator.pointSimplex (1 : LiftQ.{u})) = _
    rw [hθ]
    have h := congrArg (fun f ↦ f (1 : LiftQ.{u}))
      (SingularProductTensor.ι_zero LiftQ.{u} SingularProductGenerator.pointPair
        SingularProductGenerator.pointSimplex)
    exact h
  · intro Φ Ψ hΦ hΨ
    apply SingularProductTensor.unique_comparison LiftQ.{u} Φ Ψ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact hΦ.trans hΨ.symm

end HolomorphicAnosov.Topology

