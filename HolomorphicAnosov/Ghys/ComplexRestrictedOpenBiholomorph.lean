import HolomorphicAnosov.Ghys.ConnectedComponentRestrictedIterate

/-! This file constructs restrictions of complex smooth diffeomorphisms to invariant nonempty open
subtypes and typed complex iterates. (Lee, Prop. 1.8, pp.9–10) -/

open Set
open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

noncomputable def complexDiffeomorphIterate
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) : ℕ → Biholomorph d d M M
  | 0 => Diffeomorph.refl (complexModel d) M ∞
  | n + 1 => (complexDiffeomorphIterate f n).trans f

@[simp] theorem coe_complexDiffeomorphIterate
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (n : ℕ) :
    (complexDiffeomorphIterate f n : M → M) = (f : M → M)^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [complexDiffeomorphIterate, Diffeomorph.coe_trans, Function.iterate_succ']
      exact congrArg (fun g : M → M => f ∘ g) ih

/-- The restriction of a complex smooth diffeomorphism to a nonempty open subtype invariant under
both the map and its inverse. -/
noncomputable def restricted_open_biholomorph
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M)
    (K : TopologicalSpace.Opens M) (_hK : Nonempty K)
    (hmap : MapsTo (f : M → M) (K : Set M) (K : Set M))
    (hinv : MapsTo (f.symm : M → M) (K : Set M) (K : Set M)) :
    Biholomorph d d K K := by
  let g : K → K := fun x => ⟨f x.1, hmap x.2⟩
  let ginv : K → K := fun x => ⟨f.symm x.1, hinv x.2⟩
  have hleft : Function.LeftInverse ginv g := by
    intro x
    apply Subtype.ext
    simp [g, ginv]
  have hright : Function.RightInverse ginv g := by
    intro x
    apply Subtype.ext
    simp [g, ginv]
  let e : K ≃ K := { toFun := g, invFun := ginv, left_inv := hleft, right_inv := hright }
  have hcont : ContMDiff (complexModel d) (complexModel d) ∞ (e : K → K) := by
    intro x
    change ContMDiffAt (complexModel d) (complexModel d) ∞ g x
    apply (ContMDiffAt.subtypeVal_comp_iff K g x).mp
    change ContMDiffAt (complexModel d) (complexModel d) ∞ (fun y : K => (f (y : M) : M)) x
    rw [contMDiffAt_subtype_iff]
    exact f.contMDiff.contMDiffAt
  have hcontinv : ContMDiff (complexModel d) (complexModel d) ∞ (e.symm : K → K) := by
    intro x
    change ContMDiffAt (complexModel d) (complexModel d) ∞ ginv x
    apply (ContMDiffAt.subtypeVal_comp_iff K ginv x).mp
    change ContMDiffAt (complexModel d) (complexModel d) ∞ (fun y : K => (f.symm (y : M) : M)) x
    rw [contMDiffAt_subtype_iff]
    exact f.symm.contMDiff.contMDiffAt
  exact { toEquiv := e, contMDiff_toFun := hcont, contMDiff_invFun := hcontinv }

end HolomorphicAnosov.Ghys
