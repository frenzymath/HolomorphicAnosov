import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseFibreOpen
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeInclusionRange
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseAnnihilatesLeaf
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseDerivativeSurjective
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseDerivativeKernel
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransversalDerivativeBijective
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransversalInverseGerm
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeSameBoxPartition
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativePlaqueRetraction
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeBaseProjectionGerm
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeProjectionGermTransport
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeProjectionRestrictedDerivative
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeProjectionAnnihilatesOther
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeProductDerivativeBijective
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeBijectiveInverseContmdiff
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductLeafRelationIff
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductAffineIntersectionUnique
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductPartitionIntersectionUnique

/-! This file proves the biholomorphic global product decomposition of complementary holomorphic leaves. (Zhang, Lemma 3.2.) -/



namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- Let M be a connected finite-dimensional complex manifold with two regular holomorphic foliations W^s and W^u whose tangent bundles are complementary. Let V be a finite-dimensional real vector space with a direct sum V=V^s⊕V^u, and let H:M→V be a homeomorphism such that H(W^s(x))=H(x)+V^s and H(W^u(x))=H(x)+V^u for every x∈M. (Zhang, Lemma 3.2.) -/
theorem holomorphic_global_leaf_product
    (p q : ℕ) (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    [ChartedSpace (ComplexModel (p + q)) M]
    [IsManifold (complexModel (p + q)) ∞ M]
    (Fs : RegularHolomorphicFoliation.{u, v} (p + q) p q M)
    (Fu : RegularHolomorphicFoliation.{u, v} (p + q) q p M)
    (V : Type w) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Vs Vu : Submodule ℝ V) (hV : IsCompl Vs Vu) (H : M ≃ₜ V)
    (hs : ∀ x : M, H '' {y : M | Fs.partition x y} =
      {z : V | z - H x ∈ Vs})
    (hu : ∀ x : M, H '' {y : M | Fu.partition x y} =
      {z : V | z - H x ∈ Vu})
    (htransverse : ∀ x : M, IsCompl (Fs.tangent x) (Fu.tangent x)) :
    ∃ R : Diffeomorph (complexModel (p + q))
        ((complexModel p).prod (complexModel q)) M
        (Fs.Leaf (H.symm 0) × Fu.Leaf (H.symm 0)) ∞,
      ContMDiff (complexModel (p + q)) (complexModel p) ∞ (fun x ↦ (R x).1) ∧
      ContMDiff (complexModel (p + q)) (complexModel q) ∞ (fun x ↦ (R x).2) ∧
      (∀ x : M, Fu.partition x (R x).1.val ∧ Fs.partition x (R x).2.val) ∧
      (∀ x y : M, Fu.partition x y → Fs.partition (H.symm 0) y →
        y = (R x).1.val) ∧
      (∀ x y : M, Fs.partition x y → Fu.partition (H.symm 0) y →
        y = (R x).2.val) ∧
      (∀ (s : Fs.Leaf (H.symm 0)) (u : Fu.Leaf (H.symm 0)),
        Fu.partition s.val (R.symm (s, u)) ∧
        Fs.partition u.val (R.symm (s, u))) ∧
      (∀ (s : Fs.Leaf (H.symm 0)) (u : Fu.Leaf (H.symm 0)) (y : M),
        Fu.partition s.val y → Fs.partition u.val y → y = R.symm (s, u)) ∧
      (∀ (s : Fs.Leaf (H.symm 0)) (u : Fu.Leaf (H.symm 0)),
        H (R.symm (s, u)) = H s.val + H u.val) := by
  classical
  have hintersection (a b : M) : ∃! y : M, Fs.partition a y ∧ Fu.partition b y :=
    partition_intersection_unique Fs.partition Fu.partition Vs Vu hV H hs hu a b
  let o := H.symm (0 : V)
  let meet (a b : M) := (hintersection a b).choose
  have hmeet (a b : M) : Fs.partition a (meet a b) ∧ Fu.partition b (meet a b) :=
    (hintersection a b).choose_spec.1
  have hmeet_unique (a b y : M) (hy : Fs.partition a y ∧ Fu.partition b y) :
      y = meet a b := (hintersection a b).choose_spec.2 y hy
  let rs (x : M) : Fs.Leaf o :=
    ⟨meet o x, Quotient.sound (Fs.partition.symm (hmeet o x).1)⟩
  let ru (x : M) : Fu.Leaf o :=
    ⟨meet x o, Quotient.sound (Fu.partition.symm (hmeet x o).2)⟩
  let backward (z : Fs.Leaf o × Fu.Leaf o) : M := meet z.2.val z.1.val
  have hsleaf (s : Fs.Leaf o) : Fs.partition o s.val :=
    Fs.partition.symm (Quotient.exact s.property)
  have huleaf (u : Fu.Leaf o) : Fu.partition o u.val :=
    Fu.partition.symm (Quotient.exact u.property)
  have hleft (x : M) : backward (rs x, ru x) = x := by
    apply (hmeet_unique x x _ ⟨?_, ?_⟩).trans
      (hmeet_unique x x x ⟨Fs.partition.refl x, Fu.partition.refl x⟩).symm
    · exact Fs.partition.trans (hmeet x o).1 (hmeet (ru x).val (rs x).val).1
    · exact Fu.partition.trans (hmeet o x).2 (hmeet (ru x).val (rs x).val).2
  have hright (z : Fs.Leaf o × Fu.Leaf o) :
      (rs (backward z), ru (backward z)) = z := by
    apply Prod.ext <;> apply Subtype.ext
    · exact (hmeet_unique o (backward z) z.1.val
        ⟨hsleaf z.1, Fu.partition.symm (hmeet z.2.val z.1.val).2⟩).symm
    · exact (hmeet_unique (backward z) o z.2.val
        ⟨Fs.partition.symm (hmeet z.2.val z.1.val).1, huleaf z.2⟩).symm
  let e : M ≃ (Fs.Leaf o × Fu.Leaf o) :=
    { toFun := fun x ↦ (rs x, ru x)
      invFun := backward
      left_inv := hleft
      right_inv := hright }
  have hsum (s : Fs.Leaf o) (u : Fu.Leaf o) :
      H (backward (s, u)) = H s.val + H u.val := by
    have hsm : H s.val ∈ Vs := by
      have hh := (leaf_relation_iff Fs.partition H Vs hs o s.val).mp (hsleaf s)
      simpa [o] using hh
    have hum : H u.val ∈ Vu := by
      have hh := (leaf_relation_iff Fu.partition H Vu hu o u.val).mp (huleaf u)
      simpa [o] using hh
    obtain ⟨v, hv, huniq⟩ := affine_intersection_unique Vs Vu hV (H u.val) (H s.val)
    exact (huniq _ ⟨(leaf_relation_iff Fs.partition H Vs hs _ _).mp
      (hmeet u.val s.val).1, (leaf_relation_iff Fu.partition H Vu hu _ _).mp
      (hmeet u.val s.val).2⟩).trans
      (huniq _ ⟨by simpa using hsm, by simpa [add_comm] using hum⟩).symm
  have hrs : ContMDiff (complexModel (p + q)) (complexModel p) ∞ rs := by
    intro x
    obtain ⟨φ, hφ, hφrel⟩ := native_projection_germ_transport Fs Fu o (rs x).val x
      (Fu.partition.symm (hmeet o x).2)
      (native_base_projection_germ Fs Fu htransverse o (rs x))
    apply hφ.congr_of_eventuallyEq
    filter_upwards [hφrel] with y hy
    apply Subtype.ext
    exact (hmeet_unique o y (φ y).val
      ⟨hsleaf (φ y), hy⟩).symm
  have hru : ContMDiff (complexModel (p + q)) (complexModel q) ∞ ru := by
    intro x
    obtain ⟨φ, hφ, hφrel⟩ := native_projection_germ_transport Fu Fs o (ru x).val x
      (Fs.partition.symm (hmeet x o).1)
      (native_base_projection_germ Fu Fs (fun y ↦ (htransverse y).symm) o (ru x))
    apply hφ.congr_of_eventuallyEq
    filter_upwards [hφrel] with y hy
    apply Subtype.ext
    exact (hmeet_unique y o (φ y).val
      ⟨hy, huleaf (φ y)⟩).symm
  have he : ContMDiff (complexModel (p + q))
      ((complexModel p).prod (complexModel q)) ∞ e := hrs.prodMk hru
  suffices hregular :
      ContMDiff (complexModel (p + q)) ((complexModel p).prod (complexModel q)) ∞ e ∧
      ContMDiff ((complexModel p).prod (complexModel q)) (complexModel (p + q)) ∞
        e.symm by
    let R : Diffeomorph (complexModel (p + q))
        ((complexModel p).prod (complexModel q)) M (Fs.Leaf o × Fu.Leaf o) ∞ :=
      { toEquiv := e
        contMDiff_toFun := hregular.1
        contMDiff_invFun := hregular.2 }
    refine ⟨R, contMDiff_fst.comp R.contMDiff, contMDiff_snd.comp R.contMDiff,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; exact ⟨(hmeet o x).2, (hmeet x o).1⟩
    · intro x y hxy hoy
      exact hmeet_unique o x y ⟨hoy, hxy⟩
    · intro x y hxy hoy
      exact hmeet_unique x o y ⟨hxy, hoy⟩
    · intro s u; exact ⟨(hmeet u.val s.val).2, (hmeet u.val s.val).1⟩
    · intro s u y hsy huy
      exact hmeet_unique u.val s.val y ⟨huy, hsy⟩
    · exact hsum
  refine ⟨he, ?_⟩
  have hbij (x : M) : Function.Bijective (mfderiv (complexModel (p + q))
      ((complexModel p).prod (complexModel q)) e x) :=
    native_product_derivative_bijective Fs Fu htransverse hintersection o rs ru hrs hru
      (fun y ↦ (hmeet o y).2) (fun y ↦ (hmeet y o).1) x
  exact native_bijective_inverse_contMDiff (complexModel (p + q))
    ((complexModel p).prod (complexModel q)) e he hbij


end HolomorphicAnosov
