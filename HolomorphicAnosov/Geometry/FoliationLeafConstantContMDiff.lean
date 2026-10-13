import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativePlaqueRetraction

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov

/-- A map constant on the intrinsic leaves of a regular holomorphic foliation is holomorphic
everywhere if it is holomorphic at one point of each leaf. (Nisoli, §1.3, Eqs. (1.9)–(1.11),
pp.21–23) -/
theorem foliation_leaf_constant_contMDiff
    {d r c : ℕ} {M E : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : RegularHolomorphicFoliation d r c M) (q : M → E)
    (hq : ∀ a b, F.partition a b → q a = q b)
    (hseed : ∀ b, ∃ a, F.partition a b ∧
      ContMDiffAt (complexModel d) 𝓘(ℂ, E) ∞ q a) :
    ContMDiff (complexModel d) 𝓘(ℂ, E) ∞ q := by
  let P : M → Prop := fun a ↦ ContMDiffAt (complexModel d) 𝓘(ℂ, E) ∞ q a
  have hstep : ∀ (i : F.boxIndex) (a b : M),
      a ∈ (F.box i).source → b ∈ (F.box i).source →
      ((F.box i) a).2 = ((F.box i) b).2 → P a → P b := by
    intro i a b hai hbi heq ha
    obtain ⟨α, hα, hαb, hαrel⟩ := native_plaque_retraction F i a b hai hbi heq
    apply (ha.comp_of_eq hα hαb).congr_of_eventuallyEq
    filter_upwards [hαrel] with y hy
    exact hq y (α y) hy
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
