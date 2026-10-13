import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeProjectionRestrictedDerivative
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeProjectionAnnihilatesOther

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- The two native projection differentials together are bijective: each has a bijective restriction to its own leaf and vanishes on the other leaf. -/
theorem native_product_derivative_bijective {d p q : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (Fs : RegularHolomorphicFoliation.{u, v} d p q M)
    (Fu : RegularHolomorphicFoliation.{u, w} d q p M)
    (htransverse : ∀ y : M, IsCompl (Fs.tangent y) (Fu.tangent y))
    (hunique : ∀ a b : M, ∃! y : M, Fs.partition a y ∧ Fu.partition b y)
    (o : M) (P : M → Fs.Leaf o) (Q : M → Fu.Leaf o)
    (hP : ContMDiff (complexModel d) (complexModel p) ∞ P)
    (hQ : ContMDiff (complexModel d) (complexModel q) ∞ Q)
    (hPrel : ∀ y : M, Fu.partition y (P y).val)
    (hQrel : ∀ y : M, Fs.partition y (Q y).val) (x : M) :
    Function.Bijective (mfderiv (complexModel d)
      ((complexModel p).prod (complexModel q)) (fun y ↦ (P y, Q y)) x) := by
  have hunique' : ∀ a b : M, ∃! y : M, Fu.partition a y ∧ Fs.partition b y := by
    intro a b
    obtain ⟨y, hy, huniq⟩ := hunique b a
    exact ⟨y, hy.symm, fun z hz ↦ huniq z hz.symm⟩
  let DP := mfderiv (complexModel d) (complexModel p) P x
  let DQ := mfderiv (complexModel d) (complexModel q) Q x
  let JS := mfderiv (complexModel p) (complexModel d)
    (fun s : Fs.Leaf x ↦ s.val) (⟨x, rfl⟩ : Fs.Leaf x)
  let JU := mfderiv (complexModel q) (complexModel d)
    (fun s : Fu.Leaf x ↦ s.val) (⟨x, rfl⟩ : Fu.Leaf x)
  have hPS : Function.Surjective (DP.comp JS) :=
    (native_projection_restricted_derivative Fs Fu htransverse hunique o P hP hPrel x).2
  have hQU : Function.Surjective (DQ.comp JU) :=
    (native_projection_restricted_derivative Fu Fs (fun y ↦ (htransverse y).symm)
      hunique' o Q hQ hQrel x).2
  have hPU : Fu.tangent x ≤ DP.ker :=
    native_projection_annihilates_other Fs Fu hunique o P hP hPrel x
  have hQS : Fs.tangent x ≤ DQ.ker :=
    native_projection_annihilates_other Fu Fs hunique' o Q hQ hQrel x
  have hsurj : Function.Surjective (DP.prod DQ) := by
    rintro ⟨s, u⟩
    obtain ⟨v, hv⟩ := hPS s
    obtain ⟨w, hw⟩ := hQU u
    refine ⟨JS v + JU w, ?_⟩
    have hzeroP : DP (JU w) = 0 := hPU ⟨w, rfl⟩
    have hzeroQ : DQ (JS v) = 0 := hQS ⟨v, rfl⟩
    apply Prod.ext
    · change DP (JS v + JU w) = s
      rw [map_add, hzeroP, add_zero]
      exact hv
    · change DQ (JS v + JU w) = u
      rw [map_add, hzeroQ, zero_add]
      exact hw
  have hdim : Module.finrank ℂ (TangentSpace (complexModel d) x) =
      Module.finrank ℂ (ComplexModel p × ComplexModel q) := by
    change Module.finrank ℂ (Fin d → ℂ) =
      Module.finrank ℂ ((Fin p → ℂ) × (Fin q → ℂ))
    rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi, Module.finrank_pi,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    exact Fs.dimension
  have hbij : Function.Bijective (DP.prod DQ) :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
  rw [mfderiv_prodMk ((hP x).mdifferentiableAt (by simp))
    ((hQ x).mdifferentiableAt (by simp))]
  exact hbij

