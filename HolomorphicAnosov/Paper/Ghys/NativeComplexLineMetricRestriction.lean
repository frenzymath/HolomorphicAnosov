import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Topology.VectorBundle.Basic

/-! This file restricts ambient Hermitian cores to complex submodules and proves continuity of the
resulting total-space norm from continuity of the ambient norm. (Moroianu, §4.2, pp. 24–25;
Hatcher, Lemma 1.1, p. 8) -/

noncomputable section
namespace HolomorphicAnosov
open Bundle

/-- Ambient positive Hermitian cores restrict to complex submodules with a continuous total-space
norm whenever the ambient diagonal square root is continuous. -/
theorem exists_restricted_hermitian_metric
    {M : Type*} {E : M → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    {S : ∀ x, Submodule ℂ (E x)}
    [TopologicalSpace (TotalSpace ℂ (fun x ↦ S x))]
    (g : ∀ x, InnerProductSpace.Core ℂ (E x))
    (hc : Continuous (fun z : TotalSpace ℂ (fun x ↦ S x) ↦
      Real.sqrt ((g z.proj).inner z.snd.val z.snd.val).re)) :
    ∃ core : ∀ x, InnerProductSpace.Core ℂ (S x),
      letI : ∀ x, NormedAddCommGroup (S x) := fun x ↦
        (core x).toNormedAddCommGroup
      Continuous (fun z : TotalSpace ℂ (fun x ↦ S x) ↦ ‖z.snd‖) := by
  let restrictCore : ∀ x, InnerProductSpace.Core ℂ (S x) := fun x ↦
    { toCore :=
        { toInner := ⟨fun v w ↦ (g x).inner v.1 w.1⟩
          conj_inner_symm := by
            intro v w
            exact (g x).conj_inner_symm v.1 w.1
          re_inner_nonneg := by
            intro v
            exact (g x).re_inner_nonneg v.1
          add_left := by
            intro v w z
            exact (g x).add_left v.1 w.1 z.1
          smul_left := by
            intro v w c
            exact (g x).smul_left v.1 w.1 c }
      definite := by
        intro v hv
        apply Subtype.ext
        apply (g x).definite v.1
        exact hv }
  exact ⟨restrictCore, hc⟩

end HolomorphicAnosov
