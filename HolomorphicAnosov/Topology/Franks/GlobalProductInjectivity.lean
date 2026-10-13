import HolomorphicAnosov.Topology.Franks.ExpandingLeafInjectivity
import Mathlib.LinearAlgebra.Span.Basic

namespace HolomorphicAnosov.FranksFibreInjectivity

/-- Franks (1969), §1.8, pp.122–123, global-product injectivity step.
For two points with the same image choose the intersection of the unstable
leaf of the first with the stable leaf of the second. Its image differs from
the common image by a vector in each of two disjoint linear subspaces, hence
by zero. Apply the preceding expansion contradiction on the unstable leaf
in forward time and the stable leaf in inverse time. All selected-leaf,
linear-image, intrinsic-distance and bounded-fibre inputs are explicit;
this theorem makes no assertion that the lower geometric providers are proved. -/
theorem injective_of_global_product {P V : Type*} [AddCommGroup V] [Module ℝ V]
    (F G : P → P) (A B : V → V) (H : P → V)
    (hsemF : Function.Semiconj H F A) (hsemG : Function.Semiconj H G B)
    (Lu Ls : P → P → Prop) (du ds : P → P → ℝ)
    (hinvu : ∀ x y, Lu x y → Lu (F x) (F y))
    (hinvs : ∀ x y, Ls x y → Ls (G x) (G y))
    (hposu : ∀ x y, Lu x y → x ≠ y → 0 < du x y)
    (hposs : ∀ x y, Ls x y → x ≠ y → 0 < ds x y)
    (C rate boundu bounds : ℝ) (hC : 0 ≤ C) (hrate : 0 ≤ rate) (hrate1 : rate < 1)
    (hexpu : ∀ x y, Lu x y → ∀ k : ℕ,
      du x y ≤ C * rate ^ k * du (F^[k] x) (F^[k] y))
    (hexps : ∀ x y, Ls x y → ∀ k : ℕ,
      ds x y ≤ C * rate ^ k * ds (G^[k] x) (G^[k] y))
    (hboundu : ∀ x y, Lu x y → H x = H y → du x y ≤ boundu)
    (hbounds : ∀ x y, Ls x y → H x = H y → ds x y ≤ bounds)
    (Vu Vs : Submodule ℝ V) (hdisj : Disjoint Vu Vs)
    (himageu : ∀ x z, Lu x z → H z - H x ∈ Vu)
    (himages : ∀ y z, Ls y z → H z - H y ∈ Vs)
    (hproduct : ∀ x y, ∃ z, Lu x z ∧ Ls y z) : Function.Injective H := by
  intro x y hxy
  obtain ⟨z, hxz, hyz⟩ := hproduct x y
  have hzero : H z - H x = 0 := Submodule.disjoint_def.mp hdisj _
    (himageu x z hxz) (by simpa only [hxy] using himages y z hyz)
  have hzx : H z = H x := sub_eq_zero.mp hzero
  have hx : x = z := eq_of_expanding_leaf_of_equal_image F A H hsemF Lu du
    hinvu hposu C rate boundu hC hrate hrate1 hexpu hboundu hxz hzx.symm
  have hy : y = z := eq_of_expanding_leaf_of_equal_image G B H hsemG Ls ds
    hinvs hposs C rate bounds hC hrate hrate1 hexps hbounds hyz (hxy.symm.trans hzx.symm)
  exact hx.trans hy.symm



end HolomorphicAnosov.FranksFibreInjectivity
