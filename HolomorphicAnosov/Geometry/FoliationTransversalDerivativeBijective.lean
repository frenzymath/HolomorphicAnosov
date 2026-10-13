import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseDerivativeKernel

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov

/-- The transverse box coordinate restricted to a holomorphic immersed transversal of complementary
dimension has bijective derivative. (Nisoli, Definition 1.3.1 and Remark 1.3.2, pp.21–22) -/
theorem foliation_transversal_derivative_bijective
    {d r c : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation d r c M)
    (τ : ComplexModel c → M) (z : ComplexModel c)
    (i : F.boxIndex) (hz : τ z ∈ (F.box i).source)
    (hτ : ContMDiffAt (complexModel c) (complexModel d) ∞ τ z)
    (hinj : Function.Injective (mfderiv (complexModel c) (complexModel d) τ z))
    (hdisjoint : Disjoint (mfderiv (complexModel c) (complexModel d) τ z).range
      (F.tangent (τ z))) :
    Function.Bijective (fderiv ℂ (fun w ↦ ((F.box i) (τ w)).2) z) := by
  let D := mfderiv (complexModel d) (complexModel c)
    (fun y : M ↦ ((F.box i) y).2) (τ z)
  let J := mfderiv (complexModel c) (complexModel d) τ z
  have hker : D.ker = F.tangent (τ z) :=
    native_transverse_derivative_kernel F i (τ z) hz
  have hDJ : Function.Injective (D.comp J) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro v hv
    have hDv : J v ∈ F.tangent (τ z) := by
      rw [← hker]
      exact hv
    have hvzero : J v = 0 :=
      (disjoint_iff_inf_le.mp hdisjoint) ⟨⟨v, rfl⟩, hDv⟩
    exact hinj (by simpa only [map_zero] using hvzero)
  have hbox := (F.box_holomorphic i).contMDiffAt
    ((F.box i).open_source.mem_nhds hz)
  have hQ := (contMDiffAt_snd.comp (τ z) hbox).mdifferentiableAt (by simp)
  have hder : fderiv ℂ (fun w ↦ ((F.box i) (τ w)).2) z = D.comp J := by
    rw [← mfderiv_eq_fderiv]
    change mfderiv (complexModel c) (complexModel c)
      ((fun y : M ↦ ((F.box i) y).2) ∘ τ) z = _
    exact mfderiv_comp z hQ (hτ.mdifferentiableAt (by simp))
  rw [hder]
  exact ⟨hDJ, LinearMap.surjective_of_injective hDJ⟩


end HolomorphicAnosov
