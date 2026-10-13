import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Homeomorph.Lemmas
import HolomorphicAnosov.Targets.Theorem11Support.Surface.coordinateProjection

/-!
Real coordinates identifying a lattice with the integer vectors induce a homeomorphism of its quotient with the unit torus. (Zhang, §2, p.4)
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW03

universe u
open Set Function

/-- A real coordinate equivalence identifying lattice vectors with integer-coordinate vectors
induces a homeomorphism from the complex torus to the unit torus. On representatives, each
coordinate is reduced modulo one. -/
theorem lattice_quotient_homeomorph {d n : ℕ} (L : FullComplexLattice d)
    (P : ComplexModel d ≃L[ℝ] (Fin n → ℝ))
    (hP : ∀ v : ComplexModel d, v ∈ L.lattice ↔
      ∀ i : Fin n, ∃ z : ℤ, P v i = (z : ℝ)) :
    ∃ q : ComplexTorus L ≃ₜ UnitAddTorus (Fin n),
      ∀ v : ComplexModel d, ∀ i : Fin n,
        q (QuotientAddGroup.mk v) i = (P v i : AddCircle (1 : ℝ)) := by
  classical
  let r := coordinateProjection n
  let g : ComplexModel d →+ UnitAddTorus (Fin n) := r.comp P.toLinearMap.toAddMonoidHom
  have hr : IsOpenQuotientMap (r : (Fin n → ℝ) → UnitAddTorus (Fin n)) := by
    exact IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      (QuotientAddGroup.isOpenQuotientMap_mk :
        IsOpenQuotientMap (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))))
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hr.surjective y
    refine ⟨P.symm x, ?_⟩
    change r (P (P.symm x)) = y
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx
  have hker : L.lattice.toAddSubgroup = g.ker := by
    ext v
    change v ∈ L.lattice ↔ g v = 0
    rw [hP]
    constructor
    · intro hv
      ext i
      obtain ⟨z, hz⟩ := hv i
      change (P v i : AddCircle (1 : ℝ)) = 0
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
      refine ⟨z, ?_⟩
      simpa only [zsmul_eq_mul, mul_one] using hz.symm
    · intro hv i
      have hi := congrFun hv i
      change (P v i : AddCircle (1 : ℝ)) = 0 at hi
      obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 hi
      exact ⟨z, by simpa only [zsmul_eq_mul, mul_one] using hz.symm⟩
  let e : ComplexTorus L ≃+ UnitAddTorus (Fin n) :=
    QuotientAddGroup.liftEquiv L.lattice.toAddSubgroup hg hker
  have he : (e : ComplexTorus L → UnitAddTorus (Fin n)) ∘ QuotientAddGroup.mk = g := by
    funext v
    exact QuotientAddGroup.liftEquiv_mk _ _ _ v
  have hgc : Continuous g := hr.continuous.comp P.continuous
  have hgo : IsOpenMap g := hr.isOpenMap.comp P.toHomeomorph.isOpenMap
  have hec : Continuous (e : ComplexTorus L → UnitAddTorus (Fin n)) := by
    apply QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    rwa [he]
  have heo : IsOpenMap (e : ComplexTorus L → UnitAddTorus (Fin n)) := by
    apply QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap_iff.mpr
    rwa [he]
  refine ⟨e.toEquiv.toHomeomorphOfContinuousOpen hec heo, ?_⟩
  intro v i
  change e (QuotientAddGroup.mk v) i = (P v i : AddCircle (1 : ℝ))
  rw [QuotientAddGroup.liftEquiv_mk]
  rfl

end HolomorphicAnosov.Theorem11SupportW03

