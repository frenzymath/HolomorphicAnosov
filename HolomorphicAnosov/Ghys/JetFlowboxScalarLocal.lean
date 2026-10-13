import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Complex.Basic

/-! Intrinsic scalar coordinates in a genuine leaf flowbox. Source: Ghys, Holomorphic Anosov systems (1995), p.592. -/



namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
universe u v w z

/-- A genuine holomorphic plaque parametrization makes the ambient scalar coordinate holomorphic on the intrinsic leaf, and reconstructs inclusion locally with a fixed transverse coordinate. -/
theorem jetFlowboxScalar_local
    {M : Type u} [TopologicalSpace M] {Q : Type v} {L : Q → Type w}
    [∀ q, TopologicalSpace (L q)] [∀ q, ChartedSpace ℂ (L q)]
    [∀ q, IsManifold 𝓘(ℂ) ∞ (L q)]
    {T : Type z} [TopologicalSpace T]
    (inclusion : ∀ q, L q → M)
    (hinj : Function.Injective (fun p : (q : Q) × L q ↦ inclusion p.1 p.2))
    (c : OpenPartialHomeomorph M (ℂ × T)) (V : Set T)
    (label : V → Q) (branch : ∀ t, Opens (L (label t)))
    (param : ∀ t : V, Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
      (⟨{z | (z, t.val) ∈ c.target}, c.open_target.preimage
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℂ ↦ t.val)))⟩ : Opens ℂ) (branch t) ∞)
    (htarget : ∀ p ∈ c.target, p.2 ∈ V)
    (hparam : ∀ t z, c.symm (z.val, t.val) = inclusion (label t) (param t z).val)
    (q : Q) (x : L q) (hx : inclusion q x ∈ c.source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (fun y ↦ (c (inclusion q y)).1) x ∧
    ∀ᶠ y in 𝓝 x, inclusion q y = c.symm ((c (inclusion q y)).1, (c (inclusion q x)).2) := by
  let t : V := ⟨(c (inclusion q x)).2, htarget _ (c.map_source hx)⟩
  let W : Opens ℂ := ⟨{z | (z, t.val) ∈ c.target},
    c.open_target.preimage (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℂ ↦ t.val)))⟩
  let w : W := ⟨(c (inclusion q x)).1, c.map_source hx⟩
  have hw : inclusion (label t) (param t w).val = inclusion q x := by
    rw [← hparam t w]
    exact c.left_inv hx
  have he : (⟨label t, (param t w).val⟩ : (q : Q) × L q) = ⟨q, x⟩ := hinj hw
  have hi : label t = q := congrArg Sigma.fst he
  have ht : t.val = (c (inclusion q x)).2 := rfl
  clear_value w t
  cases hi
  have hpoint : (param t w).val = x := eq_of_heq (Sigma.mk.inj he).2
  have hbranch : x ∈ branch t := hpoint ▸ (param t w).property
  have hformula (y : branch t) :
      c (inclusion (label t) y.val) = (((param t).symm y).val, t.val) := by
    have hp := hparam t ((param t).symm y)
    rw [(param t).apply_symm_apply] at hp
    rw [← hp]
    exact c.right_inv ((param t).symm y).property
  have hs : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
      (fun y : branch t ↦ (c (inclusion (label t) y.val)).1) :=
    (contMDiff_subtype_val.comp (param t).symm.contMDiff).congr
      (fun y ↦ congrArg Prod.fst (hformula y))
  refine ⟨(contMDiffAt_subtype_iff (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
    (U := branch t) (f := fun y ↦ (c (inclusion (label t) y)).1)).mp
      (hs.contMDiffAt (x := ⟨x, hbranch⟩)), ?_⟩
  filter_upwards [(branch t).isOpen.mem_nhds hbranch] with y hy
  rw [← ht, congrArg Prod.fst (hformula ⟨y, hy⟩), hparam,
    (param t).apply_symm_apply]

end HolomorphicAnosov.Ghys
