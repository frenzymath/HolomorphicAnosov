import HolomorphicAnosov.Paper.Ghys.FlatProjectiveAtlas
import Mathlib.Topology.LocallyConstant.Basic

/-! Local projective transition germs determine locally constant effective Möbius transitions and a
flat projective atlas. (Ghys, Prop.4.1 and §5 p.597) -/

noncomputable section

namespace HolomorphicAnosov.Ghys

/-- Local projective transition equations determine unique locally constant effective Möbius
transitions satisfying the cocycle law and a flat atlas with the given charts. (Ghys, p.597) -/
theorem projectiveLocalGermsEffectiveCocycle
    {X L ι : Type*} [TopologicalSpace X] [TopologicalSpace L]
    (b : ι → OpenPartialHomeomorph X (L × ℂ)) (indexAt : X → ι)
    (hcover : ∀ x, x ∈ (b (indexAt x)).source)
    (hlocal : ∀ i j x, x ∈ (b i).source ∩ (b j).source →
      ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (b i).source ∩ (b j).source ∧
        ∃ g : MobiusGroup, ∀ y ∈ N,
          ((b j y).2 : OnePoint ℂ) = g.apply ((b i y).2 : OnePoint ℂ)) :
    ∃ t : ι → ι → X → MobiusGroup,
      (∀ i j x, x ∉ (b i).source ∩ (b j).source → t i j x = 1) ∧
      (∀ i j, IsLocallyConstant
        (fun x : ((b i).source ∩ (b j).source : Set X) ↦ t i j x)) ∧
      (∀ i j, ContinuousOn (t i j) ((b i).source ∩ (b j).source)) ∧
      (∀ i j x, x ∈ (b i).source ∩ (b j).source →
        ((b j x).2 : OnePoint ℂ) = (t i j x).apply ((b i x).2 : OnePoint ℂ)) ∧
      (∀ i x, x ∈ (b i).source → t i i x = 1) ∧
      (∀ i j k x, x ∈ (b i).source ∩ (b j).source ∩ (b k).source →
        t i k x = t j k x * t i j x) ∧
      (∀ i j x, x ∈ (b i).source ∩ (b j).source → ∀ g : MobiusGroup,
        (∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (b i).source ∩ (b j).source ∧
          ∀ y ∈ N,
            ((b j y).2 : OnePoint ℂ) = g.apply ((b i y).2 : OnePoint ℂ)) ↔
          g = t i j x) ∧
      (∃ A : FlatProjectiveAtlas X L ι,
        A.chart = b ∧ A.indexAt = indexAt ∧ A.transition = t) := by
  classical
  have unique_frame : ∀ (i j : ι) (x : X), x ∈ (b i).source ∩ (b j).source →
      ∀ g h : MobiusGroup,
      (∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (b i).source ∩ (b j).source ∧
        ∀ y ∈ N, ((b j y).2 : OnePoint ℂ) = g.apply ((b i y).2 : OnePoint ℂ)) →
      (∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (b i).source ∩ (b j).source ∧
        ∀ y ∈ N, ((b j y).2 : OnePoint ℂ) = h.apply ((b i y).2 : OnePoint ℂ)) → g = h := by
    intro i j x hx g h wg wh
    rcases wg with ⟨N, hNo, hNx, hNsub, hg⟩
    rcases wh with ⟨N', hN'o, hN'x, hN'sub, hh⟩
    have hSopen : IsOpen (N ∩ N') := hNo.inter hN'o
    have hSsub : N ∩ N' ⊆ (b i).source := fun y hy => hNsub hy.1 |>.1
    have himgopen : IsOpen ((b i) '' (N ∩ N')) :=
      (b i).isOpen_image_of_subset_source hSopen hSsub
    have himgmem : b i x ∈ (b i) '' (N ∩ N') := ⟨x, ⟨hNx, hN'x⟩, rfl⟩
    rcases (mem_nhds_prod_iff'.mp (himgopen.mem_nhds himgmem)) with
      ⟨P, V, hPo, huP, hVo, hvV, hPV⟩
    have hVnhds : V ∈ nhds ((b i x).2) := hVo.mem_nhds hvV
    have hVinf : Set.Infinite V := infinite_of_mem_nhds ((b i x).2) hVnhds
    have heq : ∀ z : ℂ, z ∈ V → g.apply (z : OnePoint ℂ) = h.apply (z : OnePoint ℂ) := by
      intro z hz
      have hm : ((b i x).1, z) ∈ (b i '' (N ∩ N')) := hPV ⟨huP, hz⟩
      rcases hm with ⟨y, hyS, hy⟩
      have hyj : y ∈ (b j).source := hNsub hyS.1 |>.2
      have hcoord : (b i y).2 = z := congrArg Prod.snd hy
      have e1 := hg y hyS.1
      have e2 := hh y hyS.2
      rw [hcoord] at e1 e2
      exact e1.symm.trans e2
    obtain ⟨A, hA⟩ := g.property
    obtain ⟨B, hB⟩ := h.property
    have heq' : ∀ z : ℂ, z ∈ V → A • (z : OnePoint ℂ) = B • (z : OnePoint ℂ) := by
      intro z hz
      have e := heq z hz
      change g.val (z : OnePoint ℂ) = h.val (z : OnePoint ℂ) at e
      rw [← hA, ← hB] at e
      exact e
    let Q : GL (Fin 2) ℂ := B⁻¹ * A
    have hfix : ∀ z : ℂ, z ∈ V → Q • (z : OnePoint ℂ) = z := by
      intro z hz
      dsimp [Q]
      rw [mul_smul]
      rw [heq' z hz]
      simp
    have hroot : Set.Infinite {z : ℂ | Polynomial.IsRoot (Matrix.GeneralLinearGroup.fixpointPolynomial Q) z} := by
      apply hVinf.mono
      intro z hz
      exact (Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff).2 (hfix z hz)
    have hpoly : Matrix.GeneralLinearGroup.fixpointPolynomial Q = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot _ hroot
    have hq10 : Q 1 0 = 0 := by
      simpa [Matrix.GeneralLinearGroup.fixpointPolynomial] using congrArg (Polynomial.coeff · 2) hpoly
    have hfixall : ∀ z : ℂ, Q • (z : OnePoint ℂ) = z := by
      intro z
      apply (Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff).1
      rw [hpoly]
      simp
    have hinf : Q • (OnePoint.infty : OnePoint ℂ) = OnePoint.infty := OnePoint.smul_infty_eq_self_iff.2 hq10
    have hQid : (MulAction.toPermHom (GL (Fin 2) ℂ) (OnePoint ℂ)) Q = 1 := by
      apply Equiv.Perm.ext
      intro z
      cases z with
      | infty => simpa using hinf
      | coe z => simpa using hfixall z
    let φ : GL (Fin 2) ℂ → Equiv.Perm (OnePoint ℂ) :=
      MulAction.toPermHom (GL (Fin 2) ℂ) (OnePoint ℂ)
    have hBAperm : (φ B)⁻¹ * φ A = 1 := by
      simpa only [Q, φ, map_mul, map_inv] using hQid
    have hAB : φ A = φ B := by
      have hmul := congrArg (fun p : Equiv.Perm (OnePoint ℂ) ↦ φ B * p) hBAperm
      simpa [← mul_assoc] using hmul

    apply Subtype.ext
    exact hA.symm.trans (hAB.trans hB)
  let frame : ∀ (i j : ι) (x : X), x ∈ (b i).source ∩ (b j).source → MobiusGroup :=
    fun i j x hx => Classical.choose (Classical.choose_spec (hlocal i j x hx) |>.2.2.2)
  have frame_spec : ∀ (i j : ι) (x : X) (hx : x ∈ (b i).source ∩ (b j).source),
      ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (b i).source ∩ (b j).source ∧
        ∀ y ∈ N, ((b j y).2 : OnePoint ℂ) =
          (frame i j x hx).apply ((b i y).2 : OnePoint ℂ) := by
    intro i j x hx
    dsimp [frame]
    rcases Classical.choose_spec (hlocal i j x hx) with ⟨hNo, hNx, hNsub, hg⟩
    exact ⟨Classical.choose (hlocal i j x hx), hNo, hNx, hNsub,
      Classical.choose_spec hg⟩
  let t : ι → ι → X → MobiusGroup := fun i j x ↦
    if hx : x ∈ (b i).source ∩ (b j).source then frame i j x hx else 1
  have tspec : ∀ (i j : ι) (x : X), x ∈ (b i).source ∩ (b j).source →
      ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (b i).source ∩ (b j).source ∧
        ∀ y ∈ N, ((b j y).2 : OnePoint ℂ) =
          (t i j x).apply ((b i y).2 : OnePoint ℂ) := by
    intro i j x hx
    simpa only [t, dite_eq_left hx] using frame_spec i j x hx
  have tloc : ∀ i j, IsLocallyConstant
      (fun x : ((b i).source ∩ (b j).source : Set X) ↦ t i j x) := by
    intro i j
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    rcases tspec i j x x.property with ⟨N, hNo, hNx, hNsub, hframe⟩
    refine ⟨Subtype.val ⁻¹' N, hNo.preimage continuous_subtype_val, hNx, ?_⟩
    intro y hy
    exact unique_frame i j y y.property (t i j y) (t i j x)
      (tspec i j y y.property) ⟨N, hNo, hy, hNsub, hframe⟩
  have tcont : ∀ i j, ContinuousOn (t i j) ((b i).source ∩ (b j).source) := by
    intro i j
    exact continuousOn_iff_continuous_domRestrict.mpr (tloc i j).continuous
  have tagree : ∀ i j x, x ∈ (b i).source ∩ (b j).source →
      ((b j x).2 : OnePoint ℂ) = (t i j x).apply ((b i x).2 : OnePoint ℂ) := by
    intro i j x hx
    rcases tspec i j x hx with ⟨N, _, hNx, _, hframe⟩
    exact hframe x hNx
  have tself : ∀ i x, x ∈ (b i).source → t i i x = 1 := by
    intro i x hx
    apply unique_frame i i x ⟨hx, hx⟩ (t i i x) 1 (tspec i i x ⟨hx, hx⟩)
    refine ⟨(b i).source, (b i).open_source, hx, fun y hy ↦ ⟨hy, hy⟩, ?_⟩
    intro y hy
    rfl
  have tcomp : ∀ i j k x, x ∈ (b i).source ∩ (b j).source ∩ (b k).source →
      t i k x = t j k x * t i j x := by
    intro i j k x hx
    rcases hx with ⟨⟨hxi, hxj⟩, hxk⟩
    rcases tspec i j x ⟨hxi, hxj⟩ with ⟨Nij, hNijo, hNijx, hNijsub, hNij⟩
    rcases tspec j k x ⟨hxj, hxk⟩ with ⟨Njk, hNjko, hNjkx, hNjksub, hNjk⟩
    apply unique_frame i k x ⟨hxi, hxk⟩ (t i k x) (t j k x * t i j x)
      (tspec i k x ⟨hxi, hxk⟩)
    refine ⟨Nij ∩ Njk, hNijo.inter hNjko, ⟨hNijx, hNjkx⟩,
      fun y hy ↦ ⟨(hNijsub hy.1).1, (hNjksub hy.2).2⟩, ?_⟩
    intro y hy
    change ((b k y).2 : OnePoint ℂ) =
      (t j k x).apply ((t i j x).apply ((b i y).2 : OnePoint ℂ))
    rw [← hNij y hy.1]
    exact hNjk y hy.2
  refine ⟨t, ?_, tloc, tcont, tagree, tself, tcomp, ?_, ?_⟩
  · intro i j x hx
    exact dite_eq_right hx
  · intro i j x hx g
    constructor
    · intro hg
      exact unique_frame i j x hx g (t i j x) hg (tspec i j x hx)
    · intro hg
      rw [hg]
      exact tspec i j x hx
  · exact ⟨{
      chart := b
      indexAt := indexAt
      mem_source := hcover
      transition := t
      transition_continuous := tcont
      transition_self := tself
      transition_comp := tcomp
      transition_agrees := tagree }, rfl, rfl, rfl⟩

end HolomorphicAnosov.Ghys
