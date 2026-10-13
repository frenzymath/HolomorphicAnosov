import HolomorphicAnosov.Targets.Theorem11Support.Surface.lattice_rank_four
import HolomorphicAnosov.Targets.Theorem11Support.Surface.lattice_basis_coordinates
import HolomorphicAnosov.Targets.Theorem11Support.Surface.latticeEquiv
import HolomorphicAnosov.Targets.Theorem11Support.Surface.latticeEquiv_apply
import HolomorphicAnosov.Targets.Theorem11Support.Surface.integerMatrix
import HolomorphicAnosov.Targets.Theorem11Support.Surface.integerMatrix_apply
import HolomorphicAnosov.Targets.Theorem11Support.Surface.integerMatrix_real_coordinates
import HolomorphicAnosov.Targets.Theorem11Support.Surface.coordinateProjection
import HolomorphicAnosov.Targets.Theorem11Support.Surface.lattice_quotient_homeomorph
import HolomorphicAnosov.Targets.Theorem11Support.Surface.quotient_covariance
import HolomorphicAnosov.Targets.Theorem11Support.Surface.compose_source_conjugacy
import HolomorphicAnosov.Targets.Theorem11Support.Surface.toral_conjugacy_of_surface_coordinates
import HolomorphicAnosov.Targets.Theorem11Support.Surface.hyperbolic_integer_coordinates
import HolomorphicAnosov.Targets.Theorem11Support.Surface.surface_model_real_toral_conjugacy
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.GlobalUnstableHolonomy
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import HolomorphicAnosov.Paper.Zhang.Proposition29
import HolomorphicAnosov.Paper.Zhang.RankOneStableHolomorphicUnstable
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Targets.GhysTheoremA
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.HyperbolicRealToralConjugacy
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Lemmas
import HolomorphicAnosov.Geometry.ComplexToRealMap
import Mathlib.Topology.Separation.Basic
import HolomorphicAnosov.Geometry.GlobalHolonomy
import HolomorphicAnosov.Geometry.OriginalAnosovGlobalUnstableHolonomy
import HolomorphicAnosov.Paper.Zhang.TorusModel
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Defs
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import Mathlib.Tactic

/-! Toral classification of holomorphic Anosov diffeomorphisms with stable complex rank one, under
homotopy-torus rigidity, together with lattice coordinates and intrinsic leaf identifications.
(Zhang, Thm 1.1, p. 2; §2, pp. 4–10) -/


namespace HolomorphicAnosov.Theorem11SupportW02

open Module


/-- A full lattice in `ℂ²` admits real linear coordinates taking it exactly to the standard integer
lattice. -/
theorem lattice_coordinates (L : FullComplexLattice 2) :
    ∃ P : ComplexModel 2 ≃L[ℝ] (Fin 4 → ℝ),
      ∀ v, v ∈ L.lattice ↔ ∀ i, ∃ z : ℤ, P v i = (z : ℝ) := by
  obtain ⟨b, P, _, hP⟩ := lattice_basis_coordinates L
  exact ⟨P, hP⟩


end HolomorphicAnosov.Theorem11SupportW02


/-! Integer matrix coordinates for a lattice-preserving complex-linear automorphism and its inverse.
(Zhang, Thm 1.1, surface reduction, p. 4) -/

namespace HolomorphicAnosov.Theorem11SupportW10

noncomputable section

@[simp] theorem latticeEquiv_symm_apply (L : FullComplexLattice 2)
    (B : LatticeLinearEquiv L) (v : L.lattice) :
    ((latticeEquiv L B).symm v : ComplexModel 2) = B.linear.symm v := rfl

/-- The matrix of the inverse lattice automorphism has columns given by the inverse images of the
chosen basis vectors. -/
theorem integerMatrix_inv_apply (L : FullComplexLattice 2)
    (B : LatticeLinearEquiv L) (b : Module.Basis (Fin 4) ℤ L.lattice)
    (i j : Fin 4) :
    (integerMatrix L B b)⁻¹ i j = b.repr ((latticeEquiv L B).symm (b j)) i :=
  LinearMap.toMatrix_apply b b _ i j

/-- Multiplication by the integer matrix gives the lattice coordinates of the image under the
lattice automorphism. -/
theorem integerMatrix_mulVec (L : FullComplexLattice 2) (B : LatticeLinearEquiv L)
    (b : Module.Basis (Fin 4) ℤ L.lattice) (v : L.lattice) :
    (integerMatrix L B b : Matrix (Fin 4) (Fin 4) ℤ).mulVec (b.repr v) =
      b.repr (latticeEquiv L B v) :=
  LinearMap.toMatrix_mulVec_repr b b _ v

end
end HolomorphicAnosov.Theorem11SupportW10



/-! Real lattice coordinates identify the additive lattice quotient with a product of real circles.
(Zhang, Thm 1.1, p. 2; Ghys, Thm A) -/

namespace HolomorphicAnosov.Theorem11SupportW03

open Set Function

noncomputable section

/-- The inverse quotient homeomorphism sends a tuple of real circle representatives to the lattice
class of its inverse-coordinate vector. -/
theorem lattice_quotient_inverse_on_representatives {d n : ℕ} (L : FullComplexLattice d)
    (P : ComplexModel d ≃L[ℝ] (Fin n → ℝ))
    (q : ComplexTorus L ≃ₜ UnitAddTorus (Fin n))
    (hq : ∀ v : ComplexModel d, ∀ i : Fin n,
      q (QuotientAddGroup.mk v) i = (P v i : AddCircle (1 : ℝ)))
    (x : Fin n → ℝ) :
    q.symm (fun i ↦ (x i : AddCircle (1 : ℝ))) = QuotientAddGroup.mk (P.symm x) := by
  apply q.injective
  rw [q.apply_symm_apply]
  funext i
  rw [hq]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

end

end HolomorphicAnosov.Theorem11SupportW03




/-! Real coordinates descend a lattice automorphism to an integer torus action and transport its
biholomorphic conjugacy. (Zhang, Thm 1.1, p. 2) -/

namespace HolomorphicAnosov.Surface11SupportW06

noncomputable section

end
end HolomorphicAnosov.Surface11SupportW06

/-! Transport of intrinsic leaf topologies and atlases along equality of partition classes and
asymptotic leaf sets. (Zhang, Lemma 2.10) -/

open Set _root_.Topology
open scoped Manifold ContDiff

namespace HolomorphicAnosov.Theorem11Support
noncomputable section
universe u v

/-- A partition class defined by forward asymptoticity equals the corresponding asymptotic leaf set. -/
theorem class_set_eq_asymptotic {M : Type u} [MetricSpace M]
    (R : Setoid M) (g : M ≃ₜ M)
    (hR : ∀ x y, R x y ↔ ForwardAsymptotic g x y) (x : M) :
    {y : M | Quotient.mk R y = Quotient.mk R x} =
      {y : M | ForwardAsymptotic g x y} := by
  ext y
  change (Quotient.mk R y = Quotient.mk R x) ↔ ForwardAsymptotic g x y
  rw [eq_comm, Quotient.eq_iff_equiv]
  exact hR x y

/-- The topology transported along equality of two subsets. -/
@[instance_reducible]
def sameSetTopology {M : Type u} {P Q : Set M} [TopologicalSpace P]
    (h : P = Q) : TopologicalSpace Q := by
  cases h
  infer_instance

/-- The charted-space structure transported along equality of two subsets, with the transported
topology. -/
@[instance_reducible]
def sameSetCharts {M : Type u} {P Q : Set M} {H : Type v} [TopologicalSpace H]
    [TopologicalSpace P] [ChartedSpace H P] (h : P = Q) :
    letI := sameSetTopology h
    ChartedSpace H Q := by
  cases h
  infer_instance

/-- The point-preserving diffeomorphism between equal subsets with transported real atlases. -/
def sameSetDiffeomorph {M : Type u} {P Q : Set M} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace P] [ChartedSpace E P] (h : P = Q) :
    letI := sameSetTopology h
    letI := sameSetCharts (H := E) h
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) P Q ∞ := by
  cases h
  exact Diffeomorph.refl _ _ _

@[simp] theorem sameSetDiffeomorph_points {M : Type u} {P Q : Set M} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace P] [ChartedSpace E P] (h : P = Q) (z : P) :
    (sameSetDiffeomorph (E := E) h z).val = z.val := by
  cases h
  simp [sameSetDiffeomorph]

/-- Connectedness is preserved by transport along equality of subsets. -/
theorem sameSet_connected {M : Type u} {P Q : Set M} [TopologicalSpace P]
    [ConnectedSpace P] (h : P = Q) :
    letI := sameSetTopology h
    ConnectedSpace Q := by
  cases h
  infer_instance

/-- An intrinsic topology with a continuous injective inclusion into a Hausdorff space is Hausdorff. -/
theorem intrinsic_t2 {M : Type u} [TopologicalSpace M] [T2Space M]
    (P : Set M) [tP : TopologicalSpace P] (hP : Continuous (Subtype.val : P → M)) :
    T2Space P := by
  exact .of_injective_continuous Subtype.val_injective hP

/-- The tangent-range equation is preserved by transport along equality of leaf subsets. -/
theorem sameSet_tangent {M : Type u} {P Q : Set M} {r : ℕ} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace P] [ChartedSpace (Fin r → ℝ) P]
    (I : ModelWithCorners ℝ E E) (D : RealTangentDistribution I M) (h : P = Q)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) I
      (Subtype.val : P → M) z).range = D z.val) :
    letI := sameSetTopology h
    letI := sameSetCharts (H := Fin r → ℝ) h
    ∀ z : Q, (mfderiv 𝓘(ℝ, Fin r → ℝ) I
      (Subtype.val : Q → M) z).range = D z.val := by
  cases h
  exact ht

/-- The native asymptotic-leaf datum obtained from an equal partition class with its intrinsic
topology, atlas, and tangent data. -/
def nativeFromEqualSet {M : Type u} [MetricSpace M] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] (I : ModelWithCorners ℝ E E) [IsManifold I ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution I M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) I ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) I ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) I
      (Subtype.val : P → M) z).range = D z.val) :
    NativeAsymptoticLeafDatum I g D x := by
  cases h
  exact {
    rank := r
    topology := tP
    charts := cP
    hausdorff := hhP
    secondCountable := scP
    connected := connP
    smoothAtlas := smP
    inclusion_smooth := hsmooth
    inclusion_immersion := himm
    tangent_image := ht }

/-- Transport from an equal partition class preserves the leaf rank. -/
@[simp] theorem nativeFromEqualSet_rank {M : Type u} [MetricSpace M] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] (I : ModelWithCorners ℝ E E) [IsManifold I ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution I M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) I ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) I ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) I
      (Subtype.val : P → M) z).range = D z.val) :
    (nativeFromEqualSet I g D x h hsmooth himm ht).rank = r := by
  cases h
  rfl

/-- The native leaf topology is the transported intrinsic topology of the partition class. -/
theorem nativeFromEqualSet_topology {M : Type u} [MetricSpace M] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] (I : ModelWithCorners ℝ E E) [IsManifold I ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution I M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) I ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) I ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) I
      (Subtype.val : P → M) z).range = D z.val) :
    (nativeFromEqualSet I g D x h hsmooth himm ht).topology = sameSetTopology h := by
  cases h
  rfl

/-- The native stable asymptotic-leaf datum associated to a stable partition class and its
regularity data. -/
def nativeStableFromF {d s t : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (g : M ≃ₜ M) (D : RealTangentDistribution (realModel d) M)
    (F : TransverseContinuousFoliations.{u, u} s t M)
    (hR : ∀ x y, F.stablePartition x y ↔ ForwardAsymptotic g x y)
    (hsc : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SecondCountableTopology (IntrinsicFoliationLeaf F.stablePartition q))
    (hsm : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (IntrinsicFoliationLeaf F.stablePartition q))
    (hi : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        Manifold.IsImmersionAt 𝓘(ℝ, Fin s → ℝ) (realModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) z)
    (ht : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) z).range = D z.val) :
    ∀ x, NativeAsymptoticLeafDatum (realModel d) g D x := by
  intro x
  let q := Quotient.mk F.stablePartition x
  letI := F.stableTopology q
  letI := F.stableCharts q
  letI := F.stable_connected q
  letI := hsc q
  letI := hsm q
  letI : T2Space (IntrinsicFoliationLeaf F.stablePartition q) :=
    intrinsic_t2 (tP := F.stableTopology q) _ (F.stable_inclusion q)
  have hsmooth : ContMDiff 𝓘(ℝ, Fin s → ℝ) (realModel d) ∞
      (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) := by
    exact fun z ↦ (hi q z).contMDiffAt
  exact nativeFromEqualSet (tP := F.stableTopology q) (cP := F.stableCharts q)
    (hhP := intrinsic_t2 (tP := F.stableTopology q) _ (F.stable_inclusion q))
    (connP := F.stable_connected q) (scP := hsc q) (smP := hsm q)
    (realModel d) g D x
    (class_set_eq_asymptotic F.stablePartition g hR x) hsmooth (hi q) (ht q)

/-- The native unstable asymptotic-leaf datum associated to an unstable partition class and its
regularity data. -/
def nativeUnstableFromF {d s t : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (g : M ≃ₜ M) (D : RealTangentDistribution (realModel d) M)
    (F : TransverseContinuousFoliations.{u, u} s t M)
    (hR : ∀ x y, F.unstablePartition x y ↔ ForwardAsymptotic g x y)
    (hsc : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      SecondCountableTopology (IntrinsicFoliationLeaf F.unstablePartition q))
    (hsm : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      IsManifold 𝓘(ℝ, Fin t → ℝ) ∞ (IntrinsicFoliationLeaf F.unstablePartition q))
    (hi : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
        Manifold.IsImmersionAt 𝓘(ℝ, Fin t → ℝ) (realModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) z)
    (ht : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
        (mfderiv 𝓘(ℝ, Fin t → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) z).range = D z.val) :
    ∀ x, NativeAsymptoticLeafDatum (realModel d) g D x := by
  intro x
  let q := Quotient.mk F.unstablePartition x
  letI := F.unstableTopology q
  letI := F.unstableCharts q
  letI := F.unstable_connected q
  letI := hsc q
  letI := hsm q
  letI : T2Space (IntrinsicFoliationLeaf F.unstablePartition q) :=
    intrinsic_t2 (tP := F.unstableTopology q) _ (F.unstable_inclusion q)
  have hsmooth : ContMDiff 𝓘(ℝ, Fin t → ℝ) (realModel d) ∞
      (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) := by
    exact fun z ↦ (hi q z).contMDiffAt
  exact nativeFromEqualSet (tP := F.unstableTopology q) (cP := F.unstableCharts q)
    (hhP := intrinsic_t2 (tP := F.unstableTopology q) _ (F.unstable_inclusion q))
    (connP := F.unstable_connected q) (scP := hsc q) (smP := hsm q)
    (realModel d) g D x
    (class_set_eq_asymptotic F.unstablePartition g hR x) hsmooth (hi q) (ht q)


/-- The point-preserving identification of a partition class with its native asymptotic leaf, using
the transported atlas. -/
def nativeFromEqualSetIdentification {M : Type u} [MetricSpace M] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] (I : ModelWithCorners ℝ E E) [IsManifold I ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution I M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) I ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) I ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) I
      (Subtype.val : P → M) z).range = D z.val) :
    let N := nativeFromEqualSet I g D x h hsmooth himm ht
    letI := N.topology
    letI := N.charts
    Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin N.rank → ℝ)
      P (StableAsymptoticLeaf g x) ∞ := by
  cases h
  exact Diffeomorph.refl _ _ _


/-- The identification with a native asymptotic leaf preserves every ambient point. -/
theorem nativeFromEqualSetIdentification_points {M : Type u} [MetricSpace M] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] (I : ModelWithCorners ℝ E E) [IsManifold I ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution I M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) I ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) I ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) I
      (Subtype.val : P → M) z).range = D z.val) (z : P) :
    (nativeFromEqualSetIdentification I g D x h hsmooth himm ht z).val = z.val := by
  cases h
  simp only [nativeFromEqualSetIdentification]
  rfl


end
end HolomorphicAnosov.Theorem11Support

open Set _root_.Topology TopologicalSpace
namespace HolomorphicAnosov.Theorem11SupportW09

universe u v

/-- A connected space with a cover by second-countable open sets is second-countable if each cover
member meets only countably many others. -/
theorem secondCountable_of_countable_overlap_cover
    {Y : Type u} [TopologicalSpace Y] [ConnectedSpace Y] {I : Type v}
    (U : I → Set Y) (ho : ∀ i, IsOpen (U i))
    (hsc : ∀ i, SecondCountableTopology (U i))
    (hcover : ∀ y : Y, ∃ i, y ∈ U i)
    (hcount : ∀ i, {j | (U i ∩ U j).Nonempty}.Countable) :
    SecondCountableTopology Y := by
  classical
  let y₀ : Y := Classical.choice inferInstance
  obtain ⟨i₀, hi₀⟩ := hcover y₀
  let N : I → Set I := fun i ↦ {j | (U i ∩ U j).Nonempty}
  let T : ℕ → Set I := Nat.rec {i₀} (fun _ s ↦ s ∪ ⋃ i ∈ s, N i)
  have hT : ∀ n, (T n).Countable := by
    intro n
    induction n with
    | zero => exact countable_singleton i₀
    | succ n ih =>
      change (T n ∪ ⋃ i ∈ T n, N i).Countable
      exact ih.union (ih.biUnion (fun i _ ↦ hcount i))
  let R : Set I := ⋃ n, T n
  have hR : R.Countable := countable_iUnion hT
  have hnext {i j : I} (hi : i ∈ R) (hij : j ∈ N i) : j ∈ R := by
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    apply mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    change j ∈ T n ∪ ⋃ i ∈ T n, N i
    exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hn, hij⟩⟩)
  let W : Set Y := ⋃ i ∈ R, U i
  have hWo : IsOpen W := isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ho i))
  have hcompl : Wᶜ = ⋃ i ∈ Rᶜ, U i := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := hcover y
      have hni : i ∉ R := by
        intro hir
        exact hy (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hir, hi⟩⟩)
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hni, hi⟩⟩
    · intro hy hwy
      obtain ⟨i, hni, hi⟩ := mem_iUnion₂.mp hy
      obtain ⟨j, hjr, hj⟩ := mem_iUnion₂.mp hwy
      exact hni (hnext hjr ⟨y, hj, hi⟩)
  have hWc : IsClosed W := by
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ho i))
  have hWe : W.Nonempty := by
    refine ⟨y₀, mem_iUnion.mpr ⟨i₀, mem_iUnion.mpr ⟨?_, hi₀⟩⟩⟩
    exact mem_iUnion.mpr ⟨0, mem_singleton i₀⟩
  have hWall : W = univ := (show IsClopen W from ⟨hWc, hWo⟩).eq_univ hWe
  let : Countable R := hR.to_subtype
  let : ∀ i : R, SecondCountableTopology (U i.val) := fun i ↦ hsc i.val
  apply secondCountableTopology_of_countable_cover (fun i : R ↦ ho i.val)
  simpa only [iUnion_subtype] using hWall


end HolomorphicAnosov.Theorem11SupportW09

namespace HolomorphicAnosov.Theorem11SupportW09

/-- In countably many boxes with disjoint open plaques, each second-countable source plaque meets
only countably many plaques. -/
theorem countable_plaque_neighbors
    {L D J : Type*} [TopologicalSpace L] [TopologicalSpace D]
    [SecondCountableTopology D] [Countable J] {P : J → Type*}
    (p : (i : Sigma P) → D → L) (hp : ∀ i, IsOpenEmbedding (p i))
    (hdisj : ∀ (j : J), Pairwise (fun a b : P j ↦
      Disjoint (range (p ⟨j, a⟩)) (range (p ⟨j, b⟩)))) (i : Sigma P) :
    {k | (range (p i) ∩ range (p k)).Nonempty}.Countable := by
  classical
  let A : (j : J) → Set (P j) := fun j ↦
    {a | (p i ⁻¹' range (p ⟨j, a⟩)).Nonempty}
  have hA : ∀ j, (A j).Countable := by
    intro j
    apply Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun a : P j ↦ p i ⁻¹' range (p ⟨j, a⟩))
    · intro a _ b _ hab
      exact (hdisj j hab).preimage (p i)
    · intro a _
      exact (hp ⟨j, a⟩).isOpen_range.preimage (hp i).continuous
    · intro a ha
      exact ha
  have hc : (⋃ j, Sigma.mk j '' A j).Countable :=
    countable_iUnion fun j ↦ (hA j).image (Sigma.mk j)
  apply hc.mono
  rintro ⟨j, a⟩ ⟨x, ⟨y, rfl⟩, hx⟩
  exact mem_iUnion.mpr ⟨j, mem_image_of_mem (Sigma.mk j) ⟨y, hx⟩⟩

/-- A connected intrinsic leaf covered by open plaques in countably many boxes is second-countable
under the plaque overlap hypotheses. -/
theorem secondCountable_of_countable_box_plaques
    {L D J : Type*} [TopologicalSpace L] [ConnectedSpace L]
    [TopologicalSpace D] [SecondCountableTopology D] [Countable J]
    {P : J → Type*} (p : (i : Sigma P) → D → L)
    (hp : ∀ i, IsOpenEmbedding (p i))
    (hdisj : ∀ (j : J), Pairwise (fun a b : P j ↦
      Disjoint (range (p ⟨j, a⟩)) (range (p ⟨j, b⟩))))
    (hcover : ∀ x : L, ∃ i, x ∈ range (p i)) : SecondCountableTopology L := by
  apply secondCountable_of_countable_overlap_cover (fun i ↦ range (p i))
    (fun i ↦ (hp i).isOpen_range)
  · intro i
    exact (hp i).isEmbedding.toHomeomorph.symm.secondCountableTopology
  · exact hcover
  · exact countable_plaque_neighbors p hp hdisj

end HolomorphicAnosov.Theorem11SupportW09

namespace HolomorphicAnosov.Theorem11SupportW09

/-- An intrinsic partition leaf covered by product boxes is second-countable under the countability
and plaque topology hypotheses. -/
theorem secondCountable_partition_leaf_from_boxes
    {M D T J : Type*} [TopologicalSpace D] [SecondCountableTopology D]
    [Countable J] (R : Setoid M)
    (τ : ∀ q : Quotient R, TopologicalSpace (IntrinsicFoliationLeaf R q))
    (c : J → D × T → M) (hc : ∀ j, Function.Injective (c j))
    (hcover : ∀ x : M, ∃ j z w, c j (z, w) = x)
    (label : J → T → Quotient R)
    (hl : ∀ j z w, Quotient.mk R (c j (z, w)) = label j w)
    (hp : ∀ j w, letI := τ (label j w)
      IsOpenEmbedding (fun z : D ↦
        (⟨c j (z, w), hl j z w⟩ : IntrinsicFoliationLeaf R (label j w))))
    (q : Quotient R) (hconn : @ConnectedSpace (IntrinsicFoliationLeaf R q) (τ q)) :
    @SecondCountableTopology (IntrinsicFoliationLeaf R q) (τ q) := by
  classical
  let := τ q
  let := hconn
  let P : J → Type _ := fun j ↦ {w : T // label j w = q}
  let p : (i : Sigma P) → D → IntrinsicFoliationLeaf R q := fun i z ↦
    ⟨c i.1 (z, i.2.1), (hl i.1 z i.2.1).trans i.2.2⟩
  have hpo : ∀ i, IsOpenEmbedding (p i) := by
    rintro ⟨j, w, hw⟩
    dsimp [p]
    subst q
    exact hp j w
  apply secondCountable_of_countable_box_plaques p hpo
  · intro j a b hab
    apply Set.disjoint_left.mpr
    rintro x ⟨z, hz⟩ ⟨z', hz'⟩
    apply hab
    apply Subtype.ext
    exact congrArg Prod.snd (hc j (congrArg Subtype.val (hz.trans hz'.symm)))
  · intro x
    obtain ⟨j, z, w, hx⟩ := hcover x.val
    have hw : label j w = q := (hl j z w).symm.trans ((congrArg (Quotient.mk R) hx).trans x.property)
    refine ⟨⟨j, ⟨w, hw⟩⟩, z, ?_⟩
    exact Subtype.ext hx

end HolomorphicAnosov.Theorem11SupportW09

namespace HolomorphicAnosov.Theorem11SupportW09

variable {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]

/-- A transverse foliation on a compact space admits a finite cover by its product boxes. -/
theorem finite_foliation_box_cover [CompactSpace M]
    (F : TransverseContinuousFoliations.{u, v} s t M) :
    ∃ I : Finset F.boxIndex, ∀ x : M, ∃ i ∈ I, x ∈ (F.box i).image := by
  classical
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ (F.box i).image) (fun i ↦ (F.box i).isOpen_image) (by
      intro x _
      obtain ⟨i, hi⟩ := F.cover x
      exact mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨I, fun x ↦ ?_⟩
  obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (hI (mem_univ x))
  exact ⟨i, hi, hx⟩

/-- The intrinsic stable partition leaves of a transverse foliation on a compact space are second-
countable. -/
theorem stable_leaf_secondCountable [CompactSpace M]
    (F : TransverseContinuousFoliations.{u, v} s t M) (q : Quotient F.stablePartition) :
    letI := F.stableTopology q
    SecondCountableTopology (IntrinsicFoliationLeaf F.stablePartition q) := by
  classical
  obtain ⟨I, hI⟩ := finite_foliation_box_cover F
  apply secondCountable_partition_leaf_from_boxes F.stablePartition F.stableTopology
    (fun i : I ↦ fun zw : FoliationCoordinateDisk s × FoliationCoordinateDisk t ↦
      ((F.box i.val).chart zw).val)
    (fun i ↦ fun _ _ h ↦ (F.box i.val).chart.injective (Subtype.ext h))
    (fun x ↦ ?_) (fun i : I ↦ F.stableLabel i.val)
    (fun i z w ↦ F.stable_label i.val z w)
    (fun i w ↦ F.stable_plaque i.val w) q (F.stable_connected q)
  obtain ⟨i, hi, hx⟩ := hI x
  let zw := (F.box i).chart.symm ⟨x, hx⟩
  refine ⟨⟨i, hi⟩, zw.1, zw.2, ?_⟩
  exact congrArg Subtype.val ((F.box i).chart.apply_symm_apply ⟨x, hx⟩)

/-- The intrinsic unstable partition leaves of a transverse foliation on a compact space are second-
countable. -/
theorem unstable_leaf_secondCountable [CompactSpace M]
    (F : TransverseContinuousFoliations.{u, v} s t M) (q : Quotient F.unstablePartition) :
    letI := F.unstableTopology q
    SecondCountableTopology (IntrinsicFoliationLeaf F.unstablePartition q) := by
  classical
  obtain ⟨I, hI⟩ := finite_foliation_box_cover F
  apply secondCountable_partition_leaf_from_boxes F.unstablePartition F.unstableTopology
    (fun i : I ↦ fun wz : FoliationCoordinateDisk t × FoliationCoordinateDisk s ↦
      ((F.box i.val).chart (wz.2, wz.1)).val)
    (fun i ↦ fun a b h ↦ by
      have hab := (F.box i.val).chart.injective (Subtype.ext h)
      exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab))
    (fun x ↦ ?_) (fun i : I ↦ F.unstableLabel i.val)
    (fun i w z ↦ F.unstable_label i.val z w)
    (fun i z ↦ F.unstable_plaque i.val z) q (F.unstable_connected q)
  obtain ⟨i, hi, hx⟩ := hI x
  let zw := (F.box i).chart.symm ⟨x, hx⟩
  refine ⟨⟨i, hi⟩, zw.2, zw.1, ?_⟩
  exact congrArg Subtype.val ((F.box i).chart.apply_symm_apply ⟨x, hx⟩)


end HolomorphicAnosov.Theorem11SupportW09

namespace HolomorphicAnosov.Theorem11Support
noncomputable section
universe u
variable {M : Type u} {P Q : Set M}
/-- The point-preserving homeomorphism between equal subsets with transported topology. -/
def leafHomeomorph (h : P = Q) [TopologicalSpace P] :
    letI := sameSetTopology h
    P ≃ₜ Q := by
  cases h
  exact Homeomorph.refl P

@[simp] theorem leafHomeomorph_val (h : P = Q) [TopologicalSpace P] (p : P) :
    (leafHomeomorph h p).val = p.val := by
  cases h
  rfl

/-- The complex leaf upgrade transported along equality of leaf subsets, including atlas
compatibility and inclusion immersion. -/
def leafComplexUpgrade {r k d : ℕ}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (h : P = Q) [TopologicalSpace P] [ChartedSpace (Fin r → ℝ) P]
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k
      (Subtype.val : P → M)) :
    letI := sameSetTopology h
    letI := sameSetCharts (H := Fin r → ℝ) h
    NativeLeafComplexUpgrade (d := d) (r := r) k
      (Subtype.val : Q → M) := by
  cases h
  exact U

/-- The complex charts of the transported leaf upgrade are the transported source charts. -/
theorem leafComplexUpgrade_charts {r k d : ℕ}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (h : P = Q) [TopologicalSpace P] [ChartedSpace (Fin r → ℝ) P]
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k
      (Subtype.val : P → M)) :
    letI := sameSetTopology h
    letI := sameSetCharts (H := Fin r → ℝ) h
    (leafComplexUpgrade h U).charts =
      @sameSetCharts M P Q (ComplexModel k) _ _ U.charts h := by
  cases h
  rfl

/-- The point-preserving diffeomorphism between equal subsets in a supplied model with transported
charts. -/
def leafDiffeomorph {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (h : P = Q)
    [TopologicalSpace P] [ChartedSpace H P] :
    letI := sameSetTopology h
    letI := sameSetCharts (H := H) h
    Diffeomorph I I P Q ∞ := by
  cases h
  exact Diffeomorph.refl I P ∞

theorem leafDiffeomorph_toHomeomorph {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (h : P = Q)
    [TopologicalSpace P] [ChartedSpace H P] :
    letI := sameSetTopology h
    letI := sameSetCharts (H := H) h
    (leafDiffeomorph I h).toHomeomorph = leafHomeomorph h := by
  cases h
  rfl

/-- The point-preserving complex diffeomorphism associated to a transported leaf upgrade. -/
def leafUpgradeDiffeomorph {r k d : ℕ}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace P] [ChartedSpace (Fin r → ℝ) P] (h : P = Q)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M)) :
    letI := sameSetTopology h
    letI := sameSetCharts (H := Fin r → ℝ) h
    letI := U.charts
    letI := (leafComplexUpgrade h U).charts
    Diffeomorph (complexModel k) (complexModel k) P Q ∞ := by
  cases h
  letI := U.charts
  exact Diffeomorph.refl _ _ _

@[simp] theorem leafUpgradeDiffeomorph_points {r k d : ℕ}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace P] [ChartedSpace (Fin r → ℝ) P] (h : P = Q)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M))
    (p : P) : (leafUpgradeDiffeomorph h U p).val = p.val := by
  cases h
  rfl

/-- The underlying homeomorphism of the transported complex leaf diffeomorphism equals any ambient-
point-preserving homeomorphism between these leaves. -/
theorem leafUpgradeDiffeomorph_eq_homeomorph {r k d : ℕ}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace P] [ChartedSpace (Fin r → ℝ) P] (h : P = Q)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M)) :
    letI := sameSetTopology h
    letI := sameSetCharts (H := Fin r → ℝ) h
    letI := U.charts
    letI := (leafComplexUpgrade h U).charts
    ∀ H : P ≃ₜ Q, (∀ p : P, (H p).val = p.val) →
      (leafUpgradeDiffeomorph h U).toHomeomorph = H := by
  cases h
  let := U.charts
  intro H hH
  apply Homeomorph.ext
  intro p
  exact Subtype.ext ((leafUpgradeDiffeomorph_points rfl U p).trans (hH p).symm)

/-- Transport of a leaf complex upgrade preserves its chosen complex atlas. -/
theorem leafComplexUpgrade_charts_eq {r k d : ℕ}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace P] [ChartedSpace (Fin r → ℝ) P] (h : P = Q)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M))
    (C : ChartedSpace (ComplexModel k) P) (hC : U.charts = C) :
    letI := sameSetTopology h
    letI := sameSetCharts (H := Fin r → ℝ) h
    (leafComplexUpgrade h U).charts =
      @sameSetCharts M P Q (ComplexModel k) _ _ C h := by
  cases hC
  exact leafComplexUpgrade_charts h U

/-- The identity from the real leaf atlas to the real restriction of the complex atlas is smooth. -/
theorem upgrade_real_to_complex {r k d : ℕ} {L : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    (inc : L → M) (U : NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    letI := U.charts
    ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel k) ∞ (id : L → L) := by
  let := U.charts
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_id, ?_⟩
  let e := chartAt (Fin r → ℝ) x
  let c := chartAt (ComplexModel k) x
  have hd := U.real_to_complex e (ChartedSpace.chart_mem_atlas x)
    c (ChartedSpace.chart_mem_atlas x)
  have hx : e x ∈ (e.symm.trans c).source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · exact e.map_source (ChartedSpace.mem_chart_source x)
    · rw [e.left_inv (ChartedSpace.mem_chart_source x)]
      exact ChartedSpace.mem_chart_source x
  have hn : e.target ∩ e.symm ⁻¹' c.source ∈ nhds (e x) :=
    (e.symm.trans c).open_source.mem_nhds hx
  have hda := hd.contDiffAt hn
  simpa only [extChartAt, realModel, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, Function.comp_id, Function.id_comp,
    id_eq, Set.range_id, e, c] using
      hda.contDiffWithinAt

/-- The inclusion of a complex-upgraded leaf is smooth in its original real atlas. -/
theorem upgrade_inclusion_real_smooth {r k d : ℕ} {L : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    (inc : L → M) (U : NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc := by
  let := U.charts
  have hi := contMDiff_complex_to_real U.inclusion_holomorphic
  simpa only [Function.comp_id] using hi.comp (upgrade_real_to_complex inc U)

/-- The identity from the real restriction of the complex atlas to the original real leaf atlas is
smooth. -/
theorem upgrade_complex_to_real {r k d : ℕ} {L : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    (inc : L → M) (U : NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    letI := U.charts
    ContMDiff (realModel k) 𝓘(ℝ, Fin r → ℝ) ∞ (id : L → L) := by
  let := U.charts
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_id, ?_⟩
  let e := chartAt (Fin r → ℝ) x
  let c := chartAt (ComplexModel k) x
  have hd := U.complex_to_real c (ChartedSpace.chart_mem_atlas x)
    e (ChartedSpace.chart_mem_atlas x)
  have hx : c x ∈ (c.symm.trans e).source := by
    change c x ∈ c.target ∧ c.symm (c x) ∈ e.source
    constructor
    · exact c.map_source (ChartedSpace.mem_chart_source x)
    · rw [c.left_inv (ChartedSpace.mem_chart_source x)]
      exact ChartedSpace.mem_chart_source x
  have hn : c.target ∩ c.symm ⁻¹' e.source ∈ nhds (c x) :=
    (c.symm.trans e).open_source.mem_nhds hx
  have hda := hd.contDiffAt hn
  simpa only [extChartAt, realModel, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, Function.comp_id, Function.id_comp,
    id_eq, Set.range_id, e, c] using hda.contDiffWithinAt

/-- The identity diffeomorphism between the real leaf atlas and the complex leaf atlas restricted to
real scalars. -/
def upgradeRealIdentityDiffeomorph {r k d : ℕ} {L : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    (inc : L → M) (U : NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    letI := U.charts
    Diffeomorph 𝓘(ℝ, Fin r → ℝ) (realModel k) L L ∞ := by
  letI := U.charts
  exact
    { toEquiv := Equiv.refl L
      contMDiff_toFun := upgrade_real_to_complex inc U
      contMDiff_invFun := upgrade_complex_to_real inc U }

/-- The compatible complex leaf upgrade makes the original real leaf atlas a smooth manifold atlas. -/
theorem upgrade_original_real_manifold {r k d : ℕ} {L : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    (inc : L → M) (U : NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L := by
  let := U.charts
  apply isManifold_of_contDiffOn
  intro e e' he he' z hz
  have hz' : z ∈ e.target ∩ e.symm ⁻¹' e'.source := by
    simpa only [modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe,
      Set.preimage_id_eq, Set.range_id, Set.inter_univ,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, id_eq] using hz
  let c := chartAt (ComplexModel k) (e.symm z)
  have hc : c ∈ U.charts.atlas := ChartedSpace.chart_mem_atlas _
  have hzinner : z ∈ (e.symm.trans c).source :=
    ⟨hz'.1, ChartedSpace.mem_chart_source _⟩
  have hzouter : c (e.symm z) ∈ (c.symm.trans e').source := by
    change c (e.symm z) ∈ c.target ∧ c.symm (c (e.symm z)) ∈ e'.source
    refine ⟨c.map_source (ChartedSpace.mem_chart_source _), ?_⟩
    rw [c.left_inv (ChartedSpace.mem_chart_source _)]
    exact hz'.2
  have hin := (U.real_to_complex e he c hc).contDiffAt
    ((e.symm.trans c).open_source.mem_nhds hzinner)
  have hout := (U.complex_to_real c hc e' he').contDiffAt
    ((c.symm.trans e').open_source.mem_nhds hzouter)
  have hcomp := hout.comp z hin
  have heq : (e' ∘ e.symm) =ᶠ[nhds z] (e' ∘ c.symm) ∘ (c ∘ e.symm) := by
    filter_upwards [(e.symm.trans c).open_source.mem_nhds hzinner] with w hw
    change w ∈ e.target ∧ e.symm w ∈ c.source at hw
    simp only [Function.comp_apply, c.left_inv hw.2]
  have htransition := hcomp.congr_of_eventuallyEq heq
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, OpenPartialHomeomorph.coe_trans] using
      htransition.contDiffWithinAt

end
end HolomorphicAnosov.Theorem11Support

namespace HolomorphicAnosov.Theorem11Support
noncomputable section
universe u
/-- The complex upgrade of the native asymptotic leaf transported from an equal partition class. -/
def nativeFromEqualSetComplexUpgrade {M : Type u} [MetricSpace M] {d k : ℕ}
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution (realModel d) M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d)
      (Subtype.val : P → M) z).range = D z.val)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M)) :
    let N := nativeFromEqualSet (realModel d) g D x h hsmooth himm ht
    letI := N.topology
    letI := N.charts
    NativeLeafComplexUpgrade (d := d) (r := N.rank) k
      (Subtype.val : StableAsymptoticLeaf g x → M) := by
  cases h
  exact U


/-- The canonical point-preserving complex identification with the native asymptotic leaf. -/
def nativeFromEqualSetComplexIdentification {M : Type u} [MetricSpace M] {d k : ℕ}
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution (realModel d) M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d)
      (Subtype.val : P → M) z).range = D z.val)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M)) :
    let N := nativeFromEqualSet (realModel d) g D x h hsmooth himm ht
    letI := N.topology
    letI := N.charts
    letI := U.charts
    letI := (nativeFromEqualSetComplexUpgrade g D x h hsmooth himm ht U).charts
    Diffeomorph (complexModel k) (complexModel k) P (StableAsymptoticLeaf g x) ∞ := by
  cases h
  letI := U.charts
  exact Diffeomorph.refl _ _ _


end
end HolomorphicAnosov.Theorem11Support

namespace HolomorphicAnosov.Theorem11Support
noncomputable section
universe u

/-- The native transverse leaf identification associated to the foliation and holonomy data, with
supplied real inclusion immersions. (Zhang, Thm 1.1) -/
def nativeTransverseFromF {d s k : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [CompactSpace M] [SecondCountableTopology M]
    (B : ComplexModel d ≃L[ℝ] (Fin (s + 2) → ℝ))
    (g : M ≃ₜ M) (Ps Pu : RealTangentDistribution (realModel d) M) :
    letI := realCoordinateRechart (M := M) B
    ∀ (F : TransverseContinuousFoliations.{u, u} s 2 M)
    (_hS : ∀ x y, F.stablePartition x y ↔ ForwardAsymptotic g x y)
    (_hU : ∀ x y, F.unstablePartition x y ↔ ForwardAsymptotic g.symm x y)
    (_tS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) z).range = Ps z.val)
    (_tU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) z).range = Pu z.val)
    (_uS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := s) k
        (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M)))
    (C : IntrinsicComplexUnstableLeaves F)
    (_uU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∃ U : NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M),
        U.charts = C.charts q)
    (_iS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        Manifold.IsImmersionAt 𝓘(ℝ, Fin s → ℝ) (realModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) z)
    (_iU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
        Manifold.IsImmersionAt 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) z),
    NativeTransverseAsymptoticIdentification.{u, u} g Ps Pu s 2 := by
  letI := realCoordinateRechart (M := M) B
  intro F hS hU tS tU uS C uU iS iU
  classical
  let US q := Classical.choice (uS q)
  let UU q := Classical.choose (uU q)
  have mS (q : Quotient F.stablePartition) :
      letI := F.stableTopology q
      letI := F.stableCharts q
      IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (IntrinsicFoliationLeaf F.stablePartition q) :=
    @upgrade_original_real_manifold M s k d
      (IntrinsicFoliationLeaf F.stablePartition q) _ _
      (F.stableTopology q) (F.stableCharts q) Subtype.val (US q)
  have mU (q : Quotient F.unstablePartition) :
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (IntrinsicFoliationLeaf F.unstablePartition q) :=
    @upgrade_original_real_manifold M 2 1 d
      (IntrinsicFoliationLeaf F.unstablePartition q) _ _
      (F.unstableTopology q) (F.unstableCharts q) Subtype.val (UU q)
  let NS := nativeStableFromF g Ps F hS
    (Theorem11SupportW09.stable_leaf_secondCountable F) mS iS tS
  let NU := nativeUnstableFromF g.symm Pu F hU
    (Theorem11SupportW09.unstable_leaf_secondCountable F) mU iU tU
  refine {
    realCoordinates := B
    F := F
    nativeS := NS
    nativeU := NU
    rankS := ?_
    rankU := ?_
    complexU1 := ?_
    stableIdentification := ?_
    stable_points := ?_
    unstableIdentification := ?_
    unstable_points := ?_ }
  · intro x
    let q := Quotient.mk F.stablePartition x
    let := F.stableTopology q
    let := F.stableCharts q
    exact nativeFromEqualSet_rank (tP := F.stableTopology q) (cP := F.stableCharts q)
      (hhP := intrinsic_t2 (tP := F.stableTopology q) _ (F.stable_inclusion q))
      (connP := F.stable_connected q)
      (scP := Theorem11SupportW09.stable_leaf_secondCountable F q)
      (smP := mS q)
      (realModel d) g Ps x (class_set_eq_asymptotic F.stablePartition g hS x)
      (fun z ↦ (iS q z).contMDiffAt) (iS q) (tS q)
  · intro x
    let q := Quotient.mk F.unstablePartition x
    let := F.unstableTopology q
    let := F.unstableCharts q
    exact nativeFromEqualSet_rank (tP := F.unstableTopology q) (cP := F.unstableCharts q)
      (hhP := intrinsic_t2 (tP := F.unstableTopology q) _ (F.unstable_inclusion q))
      (connP := F.unstable_connected q)
      (scP := Theorem11SupportW09.unstable_leaf_secondCountable F q)
      (smP := mU q)
      (realModel d) g.symm Pu x (class_set_eq_asymptotic F.unstablePartition g.symm hU x)
      (fun z ↦ (iU q z).contMDiffAt) (iU q) (tU q)
  · intro x
    let q := Quotient.mk F.unstablePartition x
    letI := F.unstableTopology q
    letI := F.unstableCharts q
    exact nativeFromEqualSetComplexUpgrade (tP := F.unstableTopology q) (cP := F.unstableCharts q)
      (hhP := intrinsic_t2 (tP := F.unstableTopology q) _ (F.unstable_inclusion q))
      (connP := F.unstable_connected q)
      (scP := Theorem11SupportW09.unstable_leaf_secondCountable F q)
      (smP := mU q)
      g.symm Pu x (class_set_eq_asymptotic F.unstablePartition g.symm hU x)
      (fun z ↦ (iU q z).contMDiffAt) (iU q) (tU q) (UU q)
  · intro x
    let q := Quotient.mk F.stablePartition x
    letI := F.stableTopology q
    letI := F.stableCharts q
    exact nativeFromEqualSetIdentification (tP := F.stableTopology q) (cP := F.stableCharts q)
      (hhP := intrinsic_t2 (tP := F.stableTopology q) _ (F.stable_inclusion q))
      (connP := F.stable_connected q)
      (scP := Theorem11SupportW09.stable_leaf_secondCountable F q)
      (smP := mS q)
      (realModel d) g Ps x (class_set_eq_asymptotic F.stablePartition g hS x)
      (fun z ↦ (iS q z).contMDiffAt) (iS q) (tS q)
  · intro x z
    let q := Quotient.mk F.stablePartition x
    let := F.stableTopology q
    let := F.stableCharts q
    exact nativeFromEqualSetIdentification_points (tP := F.stableTopology q) (cP := F.stableCharts q)
      (hhP := intrinsic_t2 (tP := F.stableTopology q) _ (F.stable_inclusion q))
      (connP := F.stable_connected q)
      (scP := Theorem11SupportW09.stable_leaf_secondCountable F q)
      (smP := mS q)
      (realModel d) g Ps x (class_set_eq_asymptotic F.stablePartition g hS x)
      (fun z ↦ (iS q z).contMDiffAt) (iS q) (tS q) z
  · intro x
    let q := Quotient.mk F.unstablePartition x
    letI := F.unstableTopology q
    letI := F.unstableCharts q
    exact nativeFromEqualSetIdentification (tP := F.unstableTopology q) (cP := F.unstableCharts q)
      (hhP := intrinsic_t2 (tP := F.unstableTopology q) _ (F.unstable_inclusion q))
      (connP := F.unstable_connected q)
      (scP := Theorem11SupportW09.unstable_leaf_secondCountable F q)
      (smP := mU q)
      (realModel d) g.symm Pu x (class_set_eq_asymptotic F.unstablePartition g.symm hU x)
      (fun z ↦ (iU q z).contMDiffAt) (iU q) (tU q)
  · intro x z
    let q := Quotient.mk F.unstablePartition x
    let := F.unstableTopology q
    let := F.unstableCharts q
    exact nativeFromEqualSetIdentification_points (tP := F.unstableTopology q) (cP := F.unstableCharts q)
      (hhP := intrinsic_t2 (tP := F.unstableTopology q) _ (F.unstable_inclusion q))
      (connP := F.unstable_connected q)
      (scP := Theorem11SupportW09.unstable_leaf_secondCountable F q)
      (smP := mU q)
      (realModel d) g.symm Pu x (class_set_eq_asymptotic F.unstablePartition g.symm hU x)
      (fun z ↦ (iU q z).contMDiffAt) (iU q) (tU q) z

end
end HolomorphicAnosov.Theorem11Support


namespace HolomorphicAnosov.Theorem11SupportW05
universe u
variable {M : Type u}
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

/-- An inclusion immersion in the complex leaf atlas viewed over the reals remains an immersion in
the compatible original real atlas. -/
theorem upgrade_original_real_immersion
    {r k d : ℕ} {L : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (realModel d) ∞ M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    (inc : L → M) (U : NativeLeafComplexUpgrade (d := d) (r := r) k inc)
    (hi : letI := U.charts
      ∀ z : L, Manifold.IsImmersionAt (realModel k) (realModel d) ∞ inc z) :
    ∀ z : L, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc z := by
  let := U.charts
  let := U.complex_manifold
  let := Theorem11Support.upgrade_original_real_manifold inc U
  let D := Theorem11Support.upgradeRealIdentityDiffeomorph inc U
  have hr : Module.finrank ℝ (Fin r → ℝ) = Module.finrank ℝ (ComplexModel k) := by
    rw [finrank_real_of_complex (ComplexModel k)]
    simp [ComplexModel, U.real_rank]
  let B : (Fin r → ℝ) ≃L[ℝ] ComplexModel k := ContinuousLinearEquiv.ofFinrankEq hr
  intro z
  let h := hi z
  let e := h.domChart.transHomeomorph B.symm.toHomeomorph
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L := by
    apply e.mem_maximalAtlas_of_contMDiffOn
    · have hc := contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      have hid := D.contMDiff.contMDiffOn (s := e.source)
      have hinner := hc.comp hid (by intro x hx; exact hx)
      convert B.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hinner using 1
      ext x
      rfl
    · have hc := contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      have hinner := hc.comp (B.toContinuousLinearMap.contMDiff.contMDiffOn (s := e.target)) (by intro x hx; exact hx)
      convert D.symm.contMDiff.comp_contMDiffOn hinner using 1
      ext x
      rfl
  apply Manifold.IsImmersionAt.mk_of_continuousAt (h.continuousAt)
    ((B.prodCongr (ContinuousLinearEquiv.refl ℝ h.complement)).trans h.equiv)
    e h.codChart
  · exact h.mem_domChart_source
  · exact h.mem_codChart_source
  · exact he
  · exact h.codChart_mem_maximalAtlas
  · intro v hv
    have hb : B v ∈ (h.domChart.extend (realModel k)).target := by
      simpa [e, OpenPartialHomeomorph.extend_target,
        OpenPartialHomeomorph.transHomeomorph_target,
        ContinuousLinearEquiv.coe_symm_toHomeomorph] using hv
    have hh := h.writtenInCharts hb
    change _ = _
    simpa only [e, Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, OpenPartialHomeomorph.transHomeomorph_symm_apply,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.refl_apply, Function.id_def,
      ContinuousLinearEquiv.coe_symm_toHomeomorph, ContinuousLinearEquiv.symm_symm] using hh

end HolomorphicAnosov.Theorem11SupportW05

namespace HolomorphicAnosov.Theorem11SupportW06
noncomputable section

/-- Complex smooth coordinate changes are real smooth on the same domains. -/
theorem complexGroupoid_le_real {d : ℕ} (n : ℕ∞ω) :
    contDiffGroupoid n (complexModel d) ≤ contDiffGroupoid n (realModel d) := by
  apply groupoid_of_pregroupoid_le
  intro f s hf
  exact hf.restrict_scalars ℝ

/-- A complex immersion is a real immersion after restriction of scalars. (Ghys, §2, pp. 588–589;
Demailly, I §3.C, p. 23) -/
theorem complex_isImmersionAt_real {d e : ℕ} {L M : Type*}
    [TopologicalSpace L] [ChartedSpace (ComplexModel d) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel e) M]
    {n : ℕ∞ω} {f : L → M} {x : L}
    (hf : Manifold.IsImmersionAt (complexModel d) (complexModel e) n f x) :
    Manifold.IsImmersionAt (realModel d) (realModel e) n f x := by
  obtain ⟨F, hF, hFC, h⟩ := hf
  let : NormedAddCommGroup F := hF
  let : NormedSpace ℂ F := hFC
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  let equivR : (ComplexModel d × F) ≃L[ℝ] ComplexModel e :=
    { toLinearEquiv := h.equiv.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := h.equiv.continuous
      continuous_invFun := h.equiv.symm.continuous }
  refine ⟨F, inferInstance, inferInstance, ?_⟩
  apply Manifold.IsImmersionAtOfComplement.mk_of_charts
    equivR h.domChart h.codChart
    h.mem_domChart_source h.mem_codChart_source
  · exact StructureGroupoid.maximalAtlas_mono (complexGroupoid_le_real n)
      h.domChart_mem_maximalAtlas
  · exact StructureGroupoid.maximalAtlas_mono (complexGroupoid_le_real n)
      h.codChart_mem_maximalAtlas
  · exact h.source_subset_preimage_source
  · exact h.writtenInCharts


end
end HolomorphicAnosov.Theorem11SupportW06

namespace HolomorphicAnosov.Theorem11SupportW05
variable {M : Type u}

/-- The inclusion of a complex-upgraded leaf is an immersion in its original real atlas. -/
theorem upgrade_inclusion_original_real_immersion
    {r k d : ℕ} {L : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (realModel d) ∞ M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    (inc : L → M) (U : NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    ∀ z : L, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc z := by
  apply upgrade_original_real_immersion inc U
  let := U.charts
  intro z
  exact Theorem11SupportW06.complex_isImmersionAt_real (U.inclusion_immersion z)

end HolomorphicAnosov.Theorem11SupportW05

namespace HolomorphicAnosov.Theorem11Support
noncomputable section
universe u

/-- The native transverse identification associated to global holonomy data and compatible complex
leaf upgrades. -/
def nativeTransverseFromHolonomy {d s k : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [CompactSpace M] [SecondCountableTopology M]
    (B : ComplexModel d ≃L[ℝ] (Fin (s + 2) → ℝ))
    (g : M ≃ₜ M) (Ps Pu : RealTangentDistribution (realModel d) M) :
    letI := realCoordinateRechart (M := M) B
    ∀ (F : TransverseContinuousFoliations.{u, u} s 2 M)
    (_hS : ∀ x y, F.stablePartition x y ↔ ForwardAsymptotic g x y)
    (_hU : ∀ x y, F.unstablePartition x y ↔ ForwardAsymptotic g.symm x y)
    (_tS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) z).range = Ps z.val)
    (_tU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) z).range = Pu z.val)
    (_uS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := s) k
        (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M)))
    (C : IntrinsicComplexUnstableLeaves F)
    (_uU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∃ U : NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M),
        U.charts = C.charts q),
    NativeTransverseAsymptoticIdentification.{u, u} g Ps Pu s 2 := by
  letI := realCoordinateRechart (M := M) B
  intro F hS hU tS tU uS C uU
  apply nativeTransverseFromF B g Ps Pu F hS hU tS tU uS C uU
  · intro q
    let := F.stableTopology q
    let := F.stableCharts q
    exact Theorem11SupportW05.upgrade_inclusion_original_real_immersion
      (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M)
      (Classical.choice (uS q))
  · intro q
    let := F.unstableTopology q
    let := F.unstableCharts q
    exact Theorem11SupportW05.upgrade_inclusion_original_real_immersion
      (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M)
      (Classical.choose (uU q))

end
end HolomorphicAnosov.Theorem11Support

/-! Transport of global holonomy to native asymptotic leaves by point-preserving intrinsic
identifications. (Zhang, Lemma 2.10, p. 10) -/

noncomputable section
open Filter Set _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov
universe u

/-- Equality of germs is preserved by homeomorphism conjugation. -/
theorem conjugate_germ_eq
    {P Q P' Q' : Type*} [TopologicalSpace P] [TopologicalSpace P']
    (e : P ≃ₜ P') (j : Q → Q') (p : P) (g h : P → Q)
    (H : (Germ.ofFun g : Germ (𝓝 p) Q) = Germ.ofFun h) :
    (Germ.ofFun (fun z : P' ↦ j (g (e.symm z))) : Germ (𝓝 (e p)) Q') =
      Germ.ofFun (fun z : P' ↦ j (h (e.symm z))) := by
  apply Germ.coe_eq.mpr
  have he : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    simpa only [ContinuousAt, Homeomorph.symm_apply_apply] using
      e.symm.continuous.continuousAt (x := e p)
  exact (he.eventually (Germ.coe_eq.mp H)).mono fun z hz ↦ congrArg j hz

section Native
variable {d s t : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
  (B : NativeTransverseAsymptoticIdentification.{u, u} f Ps Pu s t)

/-- Native leaf identifications commute with casts along equality of base points. -/
theorem native_identification_cast {x y : M} (h : x = y) :
    letI := B.realAmbientCharts
    ∀ z : B.F.ULeaf x,
      B.unstableClassHomeomorph y (castIntrinsicULeaf B.F h z) =
        castNativeReceivingLeaf h (B.unstableClassHomeomorph x z) := by
  cases h
  intro z
  rfl

/-- The inverses of native leaf identifications commute with casts along equality of base points. -/
theorem native_identification_symm_cast {x y : M} (h : x = y) :
    letI := B.realAmbientCharts
    letI := B.unstableTopology x
    letI := B.unstableTopology y
    ∀ z : UnstableAsymptoticLeaf f x,
      (B.unstableClassHomeomorph y).symm (castNativeReceivingLeaf h z) =
        castIntrinsicULeaf B.F h ((B.unstableClassHomeomorph x).symm z) := by
  cases h
  intro z
  rfl

/-- A biholomorphic identification from an intrinsic unstable partition leaf to its native
asymptotic leaf in the supplied complex atlases. -/
abbrev ReceivingIdentification
    (C : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F) (x : M) :=
  letI := B.realAmbientCharts
  letI := C.charts (Quotient.mk B.F.unstablePartition x)
  letI := B.unstableTopology x
  letI := B.unstableCharts x
  letI := (B.complexU1 x).charts
  Biholomorph 1 1 (B.F.ULeaf x) (UnstableAsymptoticLeaf f x)

/-- The entire-leaf biholomorphism transported by the receiving leaf identifications. -/
def transportReceivingBiholomorph
    (C : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F)
    (E : ∀ x : M, ReceivingIdentification B C x) {x y : M} :
    letI := B.realAmbientCharts
    IntrinsicLeafBiholomorph B.F C x y → NativeReceivingLeafBiholomorph B x y :=
  letI := B.realAmbientCharts
  letI := C.charts (Quotient.mk B.F.unstablePartition x)
  letI := C.charts (Quotient.mk B.F.unstablePartition y)
  letI := B.unstableTopology x
  letI := B.unstableCharts x
  letI := (B.complexU1 x).charts
  letI := B.unstableTopology y
  letI := B.unstableCharts y
  letI := (B.complexU1 y).charts
  fun g ↦ ((E x).symm.trans g).trans (E y)

/-- The native local holonomy map is the conjugate of the intrinsic local map under the native
identifications, with endpoint casts. -/
theorem native_local_conjugation {x x' y y' : M} (hx : x = x') (hy : y' = y) :
    letI := B.realAmbientCharts
    letI := B.unstableTopology x
    letI := B.unstableTopology y
    letI := B.unstableTopology x'
    letI := B.unstableTopology y'
    ∀ (h : OpenPartialHomeomorph (B.F.ULeaf x') (B.F.ULeaf y'))
      (z : UnstableAsymptoticLeaf f x),
      B.unstableClassHomeomorph y
        (castIntrinsicULeaf B.F hy
          (h (castIntrinsicULeaf B.F hx ((B.unstableClassHomeomorph x).symm z)))) =
        castNativeReceivingLeaf hy
          (B.transportUnstableLocalMap x' y' h (castNativeReceivingLeaf hx z)) := by
  cases hx
  cases hy
  intro h z
  rfl

/-- Global holonomy transported to native asymptotic leaves by point-preserving biholomorphic
identifications. -/
def transportNativeGlobalSHolonomy
    (C : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F)
    (E : ∀ x : M, ReceivingIdentification B C x)
    (hE : letI := B.realAmbientCharts
      ∀ x : M, letI := B.unstableTopology x
        letI := B.unstableCharts x
        letI := (B.complexU1 x).charts
        letI := C.charts (Quotient.mk B.F.unstablePartition x)
        (E x).toHomeomorph = B.unstableClassHomeomorph x)
    (G : letI := B.realAmbientCharts; GlobalSHolonomyData B.F C) :
    NativeGlobalSHolonomyData B := by
  letI := B.realAmbientCharts
  letI : ∀ x : M, TopologicalSpace (UnstableAsymptoticLeaf f x) :=
    fun x ↦ B.unstableTopology x
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f x) :=
    fun x ↦ letI := B.unstableCharts x; (B.complexU1 x).charts
  letI : ∀ q : Quotient B.F.unstablePartition,
      TopologicalSpace (IntrinsicFoliationLeaf B.F.unstablePartition q) :=
    B.F.unstableTopology
  letI : ∀ q : Quotient B.F.unstablePartition,
      ChartedSpace (ComplexModel 1) (IntrinsicFoliationLeaf B.F.unstablePartition q) :=
    C.charts
  exact {
  localContinuation := G.localContinuation
  transport := fun γ ↦ transportReceivingBiholomorph B C E (G.transport γ)
  extends_local := by
    let := B.realAmbientCharts
    intro q x y γ
    let := B.unstableTopology x.val
    let := B.unstableTopology y.val
    let := B.unstableCharts x.val
    let := B.unstableCharts y.val
    let := (B.complexU1 x.val).charts
    let := (B.complexU1 y.val).charts
    let := C.charts (Quotient.mk B.F.unstablePartition x.val)
    let := C.charts (Quotient.mk B.F.unstablePartition y.val)
    have H := conjugate_germ_eq (B.unstableClassHomeomorph x.val)
      (B.unstableClassHomeomorph y.val) (B.F.uPoint x.val)
      (fun z ↦ G.transport γ z)
      (fun z ↦ castIntrinsicULeaf B.F (congrArg Subtype.val γ.target)
        (((G.localContinuation γ).representative 0 1 (by simp)).map
          (castIntrinsicULeaf B.F (congrArg Subtype.val γ.source).symm z)))
      (G.extends_local γ)
    apply Germ.coe_eq.mpr
    have HE := Germ.coe_eq.mp H
    filter_upwards [HE] with z hz
    change E y.val (G.transport γ ((E x.val).symm z)) = _
    have hx : ((E x.val).symm : _ → _) = (B.unstableClassHomeomorph x.val).symm := by
      change ((E x.val).toHomeomorph.symm : _ → _) = _
      rw [hE]
    have hy : (E y.val : _ → _) = B.unstableClassHomeomorph y.val := by
      change ((E y.val).toHomeomorph : _ → _) = _
      rw [hE]
    rw [hx, hy]
    simpa only [native_local_conjugation] using hz
  restriction := by
    let := B.realAmbientCharts
    intro q x y γ a b c hab hbc z
    simpa only [transportReceivingBiholomorph, Diffeomorph.coe_trans,
      Function.comp_apply, Diffeomorph.symm_apply_apply] using
      congrArg (E (γ c).val) (G.restriction γ a b c hab hbc ((E (γ a).val).symm z))
  concatenation := by
    let := B.realAmbientCharts
    intro q x y z γ η w
    simpa only [transportReceivingBiholomorph, Diffeomorph.coe_trans,
      Function.comp_apply, Diffeomorph.symm_apply_apply] using
      congrArg (E z.val) (G.concatenation γ η ((E x.val).symm w))
  reversal := by
    let := B.realAmbientCharts
    intro q x y γ z
    change E x.val (G.transport γ.symm ((E y.val).symm z)) =
      E x.val ((G.transport γ).symm ((E y.val).symm z))
    exact congrArg (E x.val) (G.reversal γ ((E y.val).symm z))

  }

end Native
end HolomorphicAnosov

namespace HolomorphicAnosov.Theorem11Support
noncomputable section
universe u
/-- The complex identification with a native asymptotic leaf preserves ambient points. -/
@[simp] theorem nativeFromEqualSetComplexIdentification_points {M : Type u} [MetricSpace M] {d k : ℕ}
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution (realModel d) M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d)
      (Subtype.val : P → M) z).range = D z.val)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M)) (z : P) :
    (nativeFromEqualSetComplexIdentification g D x h hsmooth himm ht U z).val = z.val := by
  cases h
  rfl

/-- The underlying homeomorphism of the complex native identification equals the identification in
the original real atlas. -/
theorem nativeFromEqualSetComplexIdentification_toHomeomorph {M : Type u} [MetricSpace M] {d k : ℕ}
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution (realModel d) M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d)
      (Subtype.val : P → M) z).range = D z.val)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M)) :
    let N := nativeFromEqualSet (realModel d) g D x h hsmooth himm ht
    letI := N.topology
    letI := N.charts
    letI := U.charts
    letI := (nativeFromEqualSetComplexUpgrade g D x h hsmooth himm ht U).charts
    (nativeFromEqualSetComplexIdentification g D x h hsmooth himm ht U).toHomeomorph =
      (nativeFromEqualSetIdentification (realModel d) g D x h hsmooth himm ht).toHomeomorph := by
  cases h
  let := U.charts
  rfl


/-- There is a point-preserving complex native identification whenever its transported atlas equals
the chosen complex atlas. -/
theorem nativeComplexIdentification_of_charts {M : Type u} [MetricSpace M] {d k : ℕ}
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    (g : M ≃ₜ M) (D : RealTangentDistribution (realModel d) M) (x : M)
    {P : Set M} {r : ℕ} [tP : TopologicalSpace P] [cP : ChartedSpace (Fin r → ℝ) P]
    [hhP : T2Space P] [scP : SecondCountableTopology P] [connP : ConnectedSpace P]
    [smP : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ P]
    (h : P = {y | ForwardAsymptotic g x y})
    (hsmooth : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ (Subtype.val : P → M))
    (himm : ∀ z : P, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞
      (Subtype.val : P → M) z)
    (ht : ∀ z : P, (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d)
      (Subtype.val : P → M) z).range = D z.val)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k (Subtype.val : P → M))
    (C : ChartedSpace (ComplexModel k) P) (hC : U.charts = C) :
    let N := nativeFromEqualSet (realModel d) g D x h hsmooth himm ht
    letI := N.topology
    letI := N.charts
    letI := C
    letI := (nativeFromEqualSetComplexUpgrade g D x h hsmooth himm ht U).charts
    ∃ E : Diffeomorph (complexModel k) (complexModel k) P (StableAsymptoticLeaf g x) ∞,
      ∀ z : P, (E z).val = z.val := by
  cases hC
  refine ⟨nativeFromEqualSetComplexIdentification g D x h hsmooth himm ht U, ?_⟩
  exact nativeFromEqualSetComplexIdentification_points g D x h hsmooth himm ht U

end
end HolomorphicAnosov.Theorem11Support

namespace HolomorphicAnosov.Theorem11Support
noncomputable section
universe u

/-- The transverse identification `nativeTransverseFromF` admits biholomorphic receiving
identifications whose homeomorphisms are the canonical native identifications. -/
theorem nativeTransverseFromF_receiving {d s k : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [CompactSpace M] [SecondCountableTopology M]
    (B : ComplexModel d ≃L[ℝ] (Fin (s + 2) → ℝ))
    (g : M ≃ₜ M) (Ps Pu : RealTangentDistribution (realModel d) M) :
    letI := realCoordinateRechart (M := M) B
    ∀ (F : TransverseContinuousFoliations.{u, u} s 2 M)
    (hS : ∀ x y, F.stablePartition x y ↔ ForwardAsymptotic g x y)
    (hU : ∀ x y, F.unstablePartition x y ↔ ForwardAsymptotic g.symm x y)
    (tS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) z).range = Ps z.val)
    (tU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) z).range = Pu z.val)
    (uS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := s) k
        (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M)))
    (C : IntrinsicComplexUnstableLeaves F)
    (uU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∃ U : NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M),
        U.charts = C.charts q)
    (iS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        Manifold.IsImmersionAt 𝓘(ℝ, Fin s → ℝ) (realModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) z)
    (iU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
        Manifold.IsImmersionAt 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) z),
    let N := nativeTransverseFromF B g Ps Pu F hS hU tS tU uS C uU iS iU
    ∃ E : ∀ x : M, ReceivingIdentification N C x,
      letI := N.realAmbientCharts
      ∀ x : M,
        letI := N.unstableTopology x
        letI := N.unstableCharts x
        letI := (N.complexU1 x).charts
        letI : ChartedSpace (ComplexModel 1) (N.F.ULeaf x) :=
          C.charts (Quotient.mk F.unstablePartition x)
        (E x).toHomeomorph = N.unstableClassHomeomorph x := by
  let := realCoordinateRechart (M := M) B
  intro F hS hU tS tU uS C uU iS iU
  classical
  let N := nativeTransverseFromF B g Ps Pu F hS hU tS tU uS C uU iS iU
  have he (x : M) :
      ∃ E : ReceivingIdentification N C x,
        ∀ z : F.ULeaf x, (E z).val = z.val := by
    let q := Quotient.mk F.unstablePartition x
    let := F.unstableTopology q
    let := F.unstableCharts q
    let UU := Classical.choose (uU q)
    have hC : UU.charts = C.charts q := Classical.choose_spec (uU q)
    exact nativeComplexIdentification_of_charts
      (tP := F.unstableTopology q) (cP := F.unstableCharts q)
      (hhP := intrinsic_t2 (tP := F.unstableTopology q) _ (F.unstable_inclusion q))
      (connP := F.unstable_connected q)
      (scP := Theorem11SupportW09.unstable_leaf_secondCountable F q)
      (smP := @upgrade_original_real_manifold M 2 1 d
        (IntrinsicFoliationLeaf F.unstablePartition q) _ _
        (F.unstableTopology q) (F.unstableCharts q) Subtype.val UU)
      g.symm Pu x (class_set_eq_asymptotic F.unstablePartition g.symm hU x)
      (fun z ↦ (iU q z).contMDiffAt) (iU q) (tU q) UU (C.charts q) hC
  refine ⟨fun x ↦ Classical.choose (he x), ?_⟩
  let := N.realAmbientCharts
  intro x
  let := N.unstableTopology x
  let := N.unstableCharts x
  let := (N.complexU1 x).charts
  let : ChartedSpace (ComplexModel 1) (N.F.ULeaf x) :=
          C.charts (Quotient.mk F.unstablePartition x)
  apply Homeomorph.ext
  intro z
  apply Subtype.ext
  exact (Classical.choose_spec (he x) z).trans (N.unstable_points x z).symm


/-- The transverse identification `nativeTransverseFromHolonomy` admits biholomorphic receiving
identifications whose homeomorphisms are the canonical native identifications. -/
theorem nativeTransverseFromHolonomy_receiving {d s k : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [CompactSpace M] [SecondCountableTopology M]
    (B : ComplexModel d ≃L[ℝ] (Fin (s + 2) → ℝ))
    (g : M ≃ₜ M) (Ps Pu : RealTangentDistribution (realModel d) M) :
    letI := realCoordinateRechart (M := M) B
    ∀ (F : TransverseContinuousFoliations.{u, u} s 2 M)
    (hS : ∀ x y, F.stablePartition x y ↔ ForwardAsymptotic g x y)
    (hU : ∀ x y, F.unstablePartition x y ↔ ForwardAsymptotic g.symm x y)
    (tS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M) z).range = Ps z.val)
    (tU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d)
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) z).range = Pu z.val)
    (uS : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      letI := F.stableCharts q
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := s) k
        (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → M)))
    (C : IntrinsicComplexUnstableLeaves F)
    (uU : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      ∃ U : NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M),
        U.charts = C.charts q),
    let N := nativeTransverseFromHolonomy B g Ps Pu F hS hU tS tU uS C uU
    ∃ E : ∀ x : M, ReceivingIdentification N C x,
      letI := N.realAmbientCharts
      ∀ x : M,
        letI := N.unstableTopology x
        letI := N.unstableCharts x
        letI := (N.complexU1 x).charts
        letI : ChartedSpace (ComplexModel 1) (N.F.ULeaf x) :=
          C.charts (Quotient.mk F.unstablePartition x)
        (E x).toHomeomorph = N.unstableClassHomeomorph x := by
  let := realCoordinateRechart (M := M) B
  intro F hS hU tS tU uS C uU
  apply nativeTransverseFromF_receiving B g Ps Pu F hS hU tS tU uS C uU


end
end HolomorphicAnosov.Theorem11Support

namespace HolomorphicAnosov

universe u

attribute [local instance] complex_isManifold_real


namespace SurfaceSpectral

end SurfaceSpectral


/-- Assuming homotopy-torus rigidity, a holomorphic Anosov diffeomorphism on a compact connected
complex manifold of dimension `d ≥ 2` with stable complex rank one is topologically conjugate to
a hyperbolic automorphism of the real `2 * d`-torus. (Zhang, Thm 1.1, p. 2; §2, p. 4; Prop. 2.9
and Lemma 2.10, p. 10; Ghys, Thm A; Thm B, p. 598) -/
theorem theorem_1_1 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (hd : 2 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    HyperbolicRealToralConjugacy (2 * d) X (fun x ↦ f x) := by
  classical
  by_cases hd2 : d = 2
  · subst d
    exact surface_model_real_toral_conjugacy (fun x ↦ f x) (ghys_theorem_A f a)
  · have hd3 : 3 ≤ d := by omega
    have hholonomy : HasOriginalAnosovGlobalUnstableHolonomy a := by
      let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
      have hrank : ∀ x, Module.finrank ℝ
          (a.splitting.stable.toDistribution x) = 2 := by
        intro x
        obtain ⟨K, hK, hP⟩ := hstable x
        rw [← hP, (complexTangentToReal d x).toLinearEquiv.finrank_map_eq]
        change Module.finrank ℝ K = 2
        rw [finrank_real_of_complex, hK]
      obtain ⟨R, hR⟩ := global_unstable_holonomy hd3 f a hrank
      let := realCoordinateRechart (M := X) R
      obtain ⟨F, hS, hU, tS, tU, uS, C, uU, G, _⟩ := hR
      let N := Theorem11Support.nativeTransverseFromHolonomy R
        f.toHomeomorph.symm a.splitting.unstable.toDistribution
        a.splitting.stable.toDistribution F hS hU tS tU uS C uU
      obtain ⟨E, hE⟩ := Theorem11Support.nativeTransverseFromHolonomy_receiving R
        f.toHomeomorph.symm a.splitting.unstable.toDistribution
        a.splitting.stable.toDistribution F hS hU tS tU uS C uU
      exact ⟨N, ⟨transportNativeGlobalSHolonomy N C E hE G⟩⟩
    exact proposition_2_9 f a hstable hholonomy HS

end HolomorphicAnosov


