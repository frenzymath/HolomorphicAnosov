import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-! # Null loops under a factored fundamental-group map

Source: Hatcher, Algebraic Topology, change of basepoint pp.28–29 and
Proposition 1B.9 pp.90–91. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HolomorphicAnosov

/-- If the induced map of f factors through that of j, every loop made null by j
is made null by f, at any basepoint in the path connected domain.
Source: Hatcher pp.28–29, 90–91. Choose a path q from the marked point to
the loop basepoint. The j-image of qγq⁻¹ has trivial class, so factorization
makes its f-image trivial. Conjugating back by f(q) cancels the two root
paths and proves the class of f(γ) is trivial. Equality of path classes is
precisely endpoint-fixed homotopy. -/
theorem mapped_loop_null_of_factored_pi1 {A K Y : Type*} [TopologicalSpace A] [TopologicalSpace K] [TopologicalSpace Y]
    [PathConnectedSpace A] (a₀ : A) (f : C(A,Y)) (j : C(A,K))
    (φ : FundamentalGroup K (j a₀) →* FundamentalGroup Y (f a₀))
    (hf : FundamentalGroup.map f a₀ = φ.comp (FundamentalGroup.map j a₀))
    (a : A) (γ : Path a a) (hγ : (γ.map j.continuous).Homotopic (Path.refl (j a))) :
    (γ.map f.continuous).Homotopic (Path.refl (f a)) := by
  let q := PathConnectedSpace.somePath a₀ a
  let δ := (q.trans γ).trans q.symm
  have hj : FundamentalGroup.map j a₀ (Path.Homotopic.Quotient.mk δ) = 1 := by
    change Path.Homotopic.Quotient.mk (δ.map j.continuous) = Path.Homotopic.Quotient.refl _
    simp only [δ, Path.map_trans, ← Path.map_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
    rw [Path.Homotopic.Quotient.eq.mpr hγ]
    simp
  have hh : FundamentalGroup.map f a₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)) = 1 := by
    rw [hf, MonoidHom.comp_apply, hj]
    exact φ.map_one
  change Path.Homotopic.Quotient.mk (δ.map f.continuous) = Path.Homotopic.Quotient.refl _ at hh
  simp only [δ, Path.map_trans, ← Path.map_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at hh
  have hc := congrArg (fun z ↦ ((Path.Homotopic.Quotient.mk (q.map f.continuous)).symm.trans z).trans
      (Path.Homotopic.Quotient.mk (q.map f.continuous))) hh
  simp only [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_refl] at hc
  apply Path.Homotopic.Quotient.eq.mp
  simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.mk_refl] using hc

end HolomorphicAnosov
