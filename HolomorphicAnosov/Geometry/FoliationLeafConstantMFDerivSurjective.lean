import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativePlaqueRetraction
import Mathlib.Geometry.Manifold.MFDeriv.Basic

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov

/-- The derivative of a holomorphic leaf-constant map is surjective everywhere if it is surjective
at one point of each intrinsic leaf. (Nisoli, §1.3, pp.21–23) -/
theorem foliation_leaf_constant_mfderiv_surjective
    {d r c : ℕ} {M E : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : RegularHolomorphicFoliation d r c M) (q : M → E)
    (hq : ContMDiff (complexModel d) 𝓘(ℂ, E) ∞ q)
    (hconstant : ∀ a b, F.partition a b → q a = q b)
    (hseed : ∀ b, ∃ a, F.partition a b ∧
      Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ, E) q a)) :
    ∀ b, Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ, E) q b) := by
  let P : M → Prop := fun a ↦ Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ, E) q a)
  have hstep : ∀ (i : F.boxIndex) (a b : M),
      a ∈ (F.box i).source → b ∈ (F.box i).source →
      ((F.box i) a).2 = ((F.box i) b).2 → P a → P b := by
    intro i a b hai hbi heq ha
    obtain ⟨α, hα, hαa, hαrel⟩ := native_plaque_retraction F i b a hbi hai heq.symm
    have hevent : q =ᶠ[𝓝 a] q ∘ α := by
      filter_upwards [hαrel] with y hy
      exact hconstant y (α y) hy
    have he := hevent.mfderiv_eq (I := complexModel d) (I' := 𝓘(ℂ, E))
    rw [mfderiv_comp a (hq.mdifferentiableAt (by simp)) (hα.mdifferentiableAt (by simp))] at he
    intro z
    obtain ⟨v, hv⟩ := ha z
    refine ⟨mfderiv (complexModel d) (complexModel d) α a v, ?_⟩
    have hev := congrArg (fun L ↦ L v) he
    change mfderiv (complexModel d) 𝓘(ℂ, E) q a v =
      mfderiv (complexModel d) 𝓘(ℂ, E) q (α a)
        (mfderiv (complexModel d) (complexModel d) α a v) at hev
    rw [hαa] at hev
    exact hev.symm.trans hv
  have htransport : ∀ a b, F.partition a b → (P a ↔ P b) := by
    intro a b hab
    have hgen := (F.partition_generated a b).mp hab
    clear hab
    induction hgen with
    | rel a b h =>
        obtain ⟨i, t, s, s', ha, hb⟩ := h
        have hst : (s.val, t.val) ∈ (F.box i).target := by
          rw [F.box_target]
          exact ⟨s.property, t.property⟩
        have hs't : (s'.val, t.val) ∈ (F.box i).target := by
          rw [F.box_target]
          exact ⟨s'.property, t.property⟩
        have hai : a ∈ (F.box i).source := ha ▸ (F.box i).map_target hst
        have hbi : b ∈ (F.box i).source := hb ▸ (F.box i).map_target hs't
        have heq : ((F.box i) a).2 = ((F.box i) b).2 := by
          rw [← ha, ← hb, (F.box i).right_inv hst, (F.box i).right_inv hs't]
        exact ⟨hstep i a b hai hbi heq, hstep i b a hbi hai heq.symm⟩
    | refl a => exact Iff.rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2
  intro b
  obtain ⟨a, hab, ha⟩ := hseed b
  exact (htransport a b hab).mp ha

end HolomorphicAnosov
