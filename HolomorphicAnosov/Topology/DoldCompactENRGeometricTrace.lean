import HolomorphicAnosov.Topology.ENRRetractionRepresentation
import HolomorphicAnosov.Topology.FiniteFixedPointIndexSum
import HolomorphicAnosov.Topology.FunctorialTraceConjugacy
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.LinearAlgebra.Trace
import HolomorphicAnosov.Topology.DoldGradedTraceContraction
import HolomorphicAnosov.Topology.DoldGeometricTraceBridgeG10
import HolomorphicAnosov.Topology.DoldGeometricTensorConstruction

/-!
# Dold's compact-image geometric trace step

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), equations (4.1), (4.3), and (4.4), pp.5--6,
with the diagonal-difference lemma (4.2) and its reductions in §5, pp.6--8.

This helper isolates the remaining geometric step in the compact ENR proof. The
preceding parent module supplies the actual retracted map, the homeomorphic compact
image, and the signed dual tensors. The missing argument is Dold's support-operator
calculation identifying contraction of those tensors with the finite local displacement
index sum. The theorem is intentionally named so a later worker can replace this
source-backed provider. The parent uses ordinary rational singular homology explicitly.

Historical counterexample to the former arbitrary-functor statement: let X=Y be a
singleton, f=g=id, E=id, and let every H k be the zero functor. Take a k=0.
All former hypotheses hold, but contraction is zero while the unique local index
is one. The explicit hSingular identification below excludes that false case;
the sole caller already uses exactly this singular homology functor.
-/

noncomputable section
open CategoryTheory TopologicalSpace TensorProduct
open scoped TensorProduct

namespace HolomorphicAnosov.FixedPointIndexInterface

universe u

/-- Dold's compact-image geometric calculation: the signed tensors obtained from the
actual compact retract evaluate to the finite local displacement-index sum.

The hypotheses retain the ordinary singular rational homology functor, the literal
homeomorphic compact image `E`, its conjugate map `g`, finite-dimensional degreewise
homology, and vanishing above `d`. The source proof constructs Dold's diagonal,
middle-factor transposition, difference map, positive local sphere generator, and
finite cubical support reduction, then uses (4.3)--(4.4) to identify the resulting
contraction with the ENR local indices. No derivative, orientation choice, or extra
isolating hypothesis is introduced.

Source-backed proof obligation: Dold (1965), (4.1)--(4.4), pp.5--6, and §5,
pp.6--8. -/
theorem dold_compact_enr_geometric_trace_step
    (X : Type u) [TopologicalSpace X] [MetrizableSpace X] [CompactSpace X]
    (e : ENRRepresentation X) (f : C(X, X)) (d : ℕ)
    (hfinite : {x : X | f x = x}.Finite)
    (Y : Type u) [TopologicalSpace Y]
    (E : X ≃ₜ Y)
    (H : ℕ → TopCat.{u} ⥤ ModuleCat.{u} ℚ)
    (hSingular : H = fun k ↦
      (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj
        (ModuleCat.of ℚ (ULift.{u} ℚ)))
    (g : C(Y, Y))
    (hconj : TopCat.ofHom f ≫ (TopCat.isoOfHomeo E).hom =
      (TopCat.isoOfHomeo E).hom ≫ TopCat.ofHom g)
    (hH : ∀ k, FiniteDimensional ℚ ((H k).obj (TopCat.of Y) : Type u))
    (hvanish : ∀ k, d < k → Subsingleton ((H k).obj (TopCat.of Y) : Type u))
    (a : ∀ k, Module.Dual ℚ ((H k).obj (TopCat.of Y) : Type u) ⊗[ℚ]
      ((H k).obj (TopCat.of Y) : Type u))
    (ha : ∀ k, a k = (-1 : ℚ)^(k*k) •
      (dualTensorHomEquiv ℚ ((H k).obj (TopCat.of Y) : Type u)
        ((H k).obj (TopCat.of Y) : Type u)).symm
        ((H k).map (TopCat.ofHom g)).hom) :
    (∑ k ∈ Finset.range (d + 1),
      contractLeft ℚ ((H k).obj (TopCat.of Y) : Type u) (a k)) =
      ∑ x ∈ hfinite.toFinset,
        (finiteFixedPointLocalIndex e f hfinite x : ℚ) := by
  obtain ⟨b, hb, hsum⟩ := dold_geometric_tensor_exists X e f d hfinite Y E H
    hSingular g hconj hH hvanish
  have hab (k : ℕ) : a k = b k := by
    let := hH k
    apply (dualTensorHomEquiv ℚ ((H k).obj (TopCat.of Y) : Type u)
      ((H k).obj (TopCat.of Y) : Type u)).injective
    change dualTensorHom ℚ _ _ (a k) = dualTensorHom ℚ _ _ (b k)
    rw [hb k, ha k, map_smul]
    change (-1 : ℚ)^(k*k) •
      (dualTensorHomEquiv ℚ _ _)
        ((dualTensorHomEquiv ℚ _ _).symm ((H k).map (TopCat.ofHom g)).hom) = _
    rw [LinearEquiv.apply_symm_apply]
  simpa only [hab] using hsum

end HolomorphicAnosov.FixedPointIndexInterface
