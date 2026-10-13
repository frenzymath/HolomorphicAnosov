import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! This file develops the constructions and results stated below. -/

open scoped ContDiff

namespace HolomorphicAnosov

/-- A biholomorphic automorphism of a complex torus lifts to an affine biholomorphism of the complex model whose linear part preserves the lattice. In dimension two, preserving the ordered coordinate leaf families makes the linear part preserve their direction lines (Hacking, Lemma 11.1; Ghys, p. 600). -/
theorem surface_torus_biholomorphic_lift
    (d : ℕ) (hd : 0 < d) (L : FullComplexLattice d)
    (hq : IsCoveringMap
      (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L))
    (hqHol : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞
      (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L))
    (g : Biholomorph d d (ComplexTorus L) (ComplexTorus L)) :
    ∃ (F : Biholomorph d d (ComplexModel d) (ComplexModel d))
      (A : ComplexModel d ≃ₗ[ℂ] ComplexModel d) (b : ComplexModel d),
      (∀ z, (QuotientAddGroup.mk (F z) : ComplexTorus L) =
        g (QuotientAddGroup.mk z)) ∧
      (∀ z, F z = A z + b) ∧
      L.lattice.toAddSubgroup.map A.toAddEquiv.toAddMonoidHom = L.lattice.toAddSubgroup ∧
      (∀ (l : L.lattice) (z : ComplexModel d), F (F.symm z + l) = z + A l) ∧
      (∀ h2 : d = 2,
        let i0 : Fin d := Fin.cast h2.symm (0 : Fin 2)
        let i1 : Fin d := Fin.cast h2.symm (1 : Fin 2)
        ((∀ z w, z i1 = w i1 → F z i1 = F w i1) ∧
          (∀ z w, z i0 = w i0 → F z i0 = F w i0)) →
        (Submodule.span ℂ {Pi.single i0 (1 : ℂ)}).map A.toLinearMap =
            Submodule.span ℂ {Pi.single i0 (1 : ℂ)} ∧
          (Submodule.span ℂ {Pi.single i1 (1 : ℂ)}).map A.toLinearMap =
            Submodule.span ℂ {Pi.single i1 (1 : ℂ)}) := by
  classical
  let q : ComplexModel d → ComplexTorus L := QuotientAddGroup.mk
  have hqcont : Continuous q := QuotientAddGroup.continuous_mk
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective (g (q 0))
  obtain ⟨F, ⟨hF0, hFq⟩, _⟩ :=
    hq.existsUnique_continuousMap_lifts ⟨g ∘ q, g.continuous.comp hqcont⟩ 0 b hb
  obtain ⟨H, ⟨hH0, hHq⟩, _⟩ :=
    hq.existsUnique_continuousMap_lifts ⟨g.symm ∘ q, g.symm.continuous.comp hqcont⟩
      b 0 (by simpa [q] using congrArg g.symm hb.symm)
  have hFq' (z) : q (F z) = g (q z) := congrFun hFq z
  have hHq' (z) : q (H z) = g.symm (q z) := congrFun hHq z
  have hHF : H ∘ F = id := by
    refine hq.eq_of_comp_eq (H.continuous.comp F.continuous) continuous_id ?_ 0 ?_
    · funext z
      change q (H (F z)) = q z
      rw [hHq', hFq']
      exact g.symm_apply_apply (q z)
    · simpa [Function.comp_def, hF0] using hH0
  have hFH : F ∘ H = id := by
    refine hq.eq_of_comp_eq (F.continuous.comp H.continuous) continuous_id ?_ b ?_
    · funext z
      change q (F (H z)) = q z
      rw [hFq', hHq']
      exact g.apply_symm_apply (q z)
    · simpa [Function.comp_def, hH0] using hF0
  have hsmooth : ∀ (k : Biholomorph d d (ComplexTorus L) (ComplexTorus L))
      (J : C(ComplexModel d, ComplexModel d)),
      (∀ z, q (J z) = k (q z)) → ContDiff ℂ ∞ J := by
    intro k J hJ
    apply contMDiff_iff_contDiff.mp
    intro z
    let hi := hqHol (J z)
    have heq : J =ᶠ[nhds z] hi.localInverse ∘ (k ∘ q) := by
      filter_upwards [J.continuous.continuousAt.eventually
        (hi.localInverse.open_target.mem_nhds hi.localInverse_mem_target)] with w hw
      change J w = hi.localInverse (k (q w))
      rw [← hJ w]
      exact (hi.localInverse_left_inv hw).symm
    have hinv := hi.localInverse_contMDiffAt
    change ContMDiffAt (complexModel d) (complexModel d) ∞ hi.localInverse (q (J z)) at hinv
    rw [hJ z] at hinv
    exact (hinv.comp z (k.contMDiff.contMDiffAt.comp z
      (hqHol.contMDiff z))).congr_of_eventuallyEq heq
  have hFs := hsmooth g F hFq'
  have hHs := hsmooth g.symm H hHq'
  let FF : Biholomorph d d (ComplexModel d) (ComplexModel d) :=
    { toFun := F
      invFun := H
      left_inv := fun z ↦ congrFun hHF z
      right_inv := fun z ↦ congrFun hFH z
      contMDiff_toFun := hFs.contMDiff
      contMDiff_invFun := hHs.contMDiff }
  have hperiod : ∀ z w, w ∈ L.lattice →
      fderiv ℂ F (z + w) = fderiv ℂ F z := by
    intro z w hw
    have hc : ∀ z, F (z + w) - F z = F w - F 0 := by
      intro z
      have hcc := hq.const_of_comp
        ((F.continuous.comp (continuous_id.add_const w)).sub F.continuous)
      suffices hh : ∀ a a', q (F (a + w) - F a) = q (F (a' + w) - F a') by
        simpa using hcc hh z 0
      intro a a'
      have hzero (t) : q (F (t + w) - F t) = 0 := by
        change (QuotientAddGroup.mk' L.lattice.toAddSubgroup) (F (t + w) - F t) = 0
        rw [map_sub]
        change q (F (t + w)) - q (F t) = 0
        rw [hFq', hFq']
        have htw : q (t + w) = q t := by
          change (QuotientAddGroup.mk' L.lattice.toAddSubgroup) (t + w) = q t
          rw [map_add]
          have hwq : q w = 0 := (QuotientAddGroup.eq_zero_iff w).mpr hw
          change q t + q w = q t
          rw [hwq, add_zero]
        rw [htw, sub_self]
      exact (hzero a).trans (hzero a').symm
    have heq : (fun z ↦ F (z + w)) = fun z ↦ F z + (F w - F 0) := by
      funext t
      linear_combination hc t
    have hh := congrArg (fun K ↦ fderiv ℂ K z) heq
    simpa only [fderiv_comp_add_right, fderiv_add_const] using hh
  let D := fderiv ℂ F
  have hDs : ContDiff ℂ ∞ D := hFs.fderiv_right (by simp)
  let := L.discrete
  let := L.full
  have hbounded : Bornology.IsBounded (Set.range D) :=
    (IsZLattice.isCompact_range_of_periodic L.lattice D hDs.continuous hperiod).isBounded
  have hDconst (z) : D z = D 0 :=
    hDs.differentiable (by simp) |>.apply_eq_apply_of_bounded hbounded z 0
  have haff : F = fun z ↦ D 0 z + F 0 := by
    apply eq_of_fderiv_eq (hFs.differentiable (by simp))
      ((D 0).differentiable.add_const (F 0)) (fun z ↦ by simpa [D] using hDconst z) 0
    simp
  let a : ComplexModel d →ₗ[ℂ] ComplexModel d := (D 0).toLinearMap
  have habij : Function.Bijective a := by
    constructor
    · intro z w heq
      apply FF.injective
      change F z = F w
      rw [haff]
      exact congrArg (fun y ↦ y + F 0) heq
    · intro w
      obtain ⟨z, hz⟩ := FF.surjective (w + F 0)
      refine ⟨z, ?_⟩
      change F z = w + F 0 at hz
      have hz' := (congrFun haff z).symm.trans hz
      exact add_right_cancel hz'
  let A := LinearEquiv.ofBijective a habij
  have haff' (z) : FF z = A z + F 0 := congrFun haff z
  have hmem (z) : A z ∈ L.lattice ↔ z ∈ L.lattice := by
    change A z ∈ L.lattice.toAddSubgroup ↔ z ∈ L.lattice.toAddSubgroup
    rw [← QuotientAddGroup.eq_zero_iff (A z), ← QuotientAddGroup.eq_zero_iff z]
    change q (A z) = 0 ↔ q z = 0
    have hrel : g (q z) = q (A z) + g (q 0) := by
      calc
        _ = q (FF z) := (hFq' z).symm
        _ = q (A z) + q (F 0) := by
          rw [haff']
          exact map_add (QuotientAddGroup.mk' L.lattice.toAddSubgroup) _ _
        _ = _ := by rw [hFq' 0]
    constructor
    · intro h
      have hz : g (q z) = g (q 0) := by simpa [h] using hrel
      simpa [q] using g.injective hz
    · intro h
      have hz : q (A z) + g (q 0) = g (q 0) := by
        rw [← hrel, h]
        rfl
      exact add_right_cancel (hz.trans (zero_add _).symm)
  have hmap : L.lattice.toAddSubgroup.map A.toAddEquiv.toAddMonoidHom =
      L.lattice.toAddSubgroup := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hmem z).mpr hz
    · intro hw
      refine ⟨A.symm w, ?_, A.apply_symm_apply w⟩
      exact (hmem (A.symm w)).mp (by simpa using hw)
  refine ⟨FF, A, F 0, hFq', haff', hmap, ?_, ?_⟩
  · intro l z
    rw [haff', map_add]
    have hinv := haff' (FF.symm z)
    rw [FF.apply_symm_apply] at hinv
    calc
      _ = (A (FF.symm z) + F 0) + A l := by abel
      _ = z + A l := by rw [← hinv]
  · intro h2
    subst d
    dsimp
    intro hlines
    have hline (i j : Fin 2) (hij : i ≠ j)
        (hp : ∀ z w, z j = w j → FF z j = FF w j) :
        (Submodule.span ℂ {Pi.single i (1 : ℂ)}).map A.toLinearMap =
          Submodule.span ℂ {Pi.single i (1 : ℂ)} := by
      let v : ComplexModel 2 := Pi.single i 1
      have hvj : v j = (0 : ComplexModel 2) j := by simp [v, Ne.symm hij]
      have hz := hp v 0 hvj
      rw [haff' v, haff' 0] at hz
      have hAzj : A v j = 0 := by simpa using hz
      have hv : A v = (A v i) • v := by
        ext k
        by_cases hk : k = i
        · subst k
          simp [v]
        · have hkj : k = j := by
            omega
          subst k
          simp [v, Ne.symm hij, hAzj]
      have hc : A v i ≠ 0 := by
        intro hc
        have hAv : A v = 0 := by rw [hv, hc, zero_smul]
        have hvzero : v = 0 := A.injective (by simpa using hAv)
        have := congrFun hvzero i
        simp [v] at this
      rw [Submodule.map_span, Set.image_singleton]
      change Submodule.span ℂ {A v} = Submodule.span ℂ {v}
      rw [hv]
      exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _
    exact ⟨hline 0 1 (by decide) hlines.1, hline 1 0 (by decide) hlines.2⟩


end HolomorphicAnosov
