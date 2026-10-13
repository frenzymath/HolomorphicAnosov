import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveSectionLocalFormulaG7
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import HolomorphicAnosov.SurfaceTorusSupport.ProjectiveActionHolomorphic

/-! The evaluation of an ordered frame section is locally biholomorphic on a holomorphic cover. -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

theorem ordered_projective_section_local_biholomorph
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    (Z : FiberBundleCore A.index S OrderedProjectiveFrameGroup)
    (hbase : Z.baseSet = fun i ↦ (A.chart i).source)
    (hindex : Z.indexAt = fun x ↦ Classical.choose (A.cover x))
    (hchange : Z.coordChange =
      fun i j x g ↦ g * (A.transition i j x)⁻¹)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] (p : U → S)
    (hp : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ p)
    (s : C(U, Z.TotalSpace)) (hsproj : ∀ u, (s u).proj = p u) :
    let ev : Z.TotalSpace → ComplexProjectiveLine × ComplexProjectiveLine :=
      fun z ↦ ((z.2.1 • (A.chart (Z.indexAt z.1) z.1).1),
        (z.2.2 • (A.chart (Z.indexAt z.1) z.1).2))
    IsLocalDiffeomorph (complexModel 2)
      ((complexModel 1).prod (complexModel 1)) ∞ (fun u ↦ ev (s u)) := by
  let ev : Z.TotalSpace → ComplexProjectiveLine × ComplexProjectiveLine :=
    fun z ↦ ((z.2.1 • (A.chart (Z.indexAt z.1) z.1).1),
      (z.2.2 • (A.chart (Z.indexAt z.1) z.1).2))
  dsimp only
  intro u
  obtain ⟨i, g, N, hNo, huN, hMaps, hformula⟩ :=
    ordered_projective_section_local_formula A Z hbase hindex hchange
      p hp.isLocalHomeomorph.continuous s hsproj u
  obtain ⟨P, huP, hP⟩ := hp u
  let c : PartialDiffeomorph (complexModel 2)
      ((complexModel 1).prod (complexModel 1)) S
      (ComplexProjectiveLine × ComplexProjectiveLine) ∞ :=
    { toPartialEquiv := (A.chart i).toPartialEquiv
      open_source := (A.chart i).open_source
      open_target := (A.chart i).open_target
      contMDiffOn_toFun := (A.holomorphic i).1
      contMDiffOn_invFun := (A.holomorphic i).2 }
  let G1 (m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) :
      Diffeomorph (complexModel 1) (complexModel 1)
        ComplexProjectiveLine ComplexProjectiveLine ∞ :=
    { toEquiv := MulAction.toPerm m
      contMDiff_toFun := projective_special_linear_action_contMDiff m
      contMDiff_invFun := projective_special_linear_action_contMDiff m⁻¹ }
  let G : Diffeomorph ((complexModel 1).prod (complexModel 1))
      ((complexModel 1).prod (complexModel 1))
      (ComplexProjectiveLine × ComplexProjectiveLine)
      (ComplexProjectiveLine × ComplexProjectiveLine) ∞ :=
    (G1 g.1).prodCongr (G1 g.2)
  let W : Set U := N ∩ p ⁻¹' (A.chart i).source
  have hWopen : IsOpen W := hNo.inter
    (hp.isLocalHomeomorph.continuous.isOpen_preimage _ (A.chart i).open_source)
  let r := P.toOpenPartialHomeomorph.restr W
  let P' : PartialDiffeomorph (complexModel 2) (complexModel 2) U S ∞ :=
    { toPartialEquiv := r.toPartialEquiv
      open_source := r.open_source
      open_target := r.open_target
      contMDiffOn_toFun := P.contMDiffOn_toFun.mono (by
        intro y hy
        rw [OpenPartialHomeomorph.restr_source] at hy
        exact hy.1)
      contMDiffOn_invFun := P.contMDiffOn_invFun.mono (by
        intro y hy
        rw [OpenPartialHomeomorph.restr_target] at hy
        exact hy.1) }
  let Q := P'.trans (c.trans G.toPartialDiffeomorph)
  refine ⟨Q, ?_, ?_⟩
  ·
    have huW : u ∈ W := ⟨huN, hMaps huN⟩
    have hur : u ∈ r.source := by
      rw [OpenPartialHomeomorph.restr_source, hWopen.interior_eq]
      exact ⟨huP, huW⟩
    refine ⟨hur, ?_⟩
    change P' u ∈ (c.trans G.toPartialDiffeomorph).toOpenPartialHomeomorph.source
    change P' u ∈ (c.toOpenPartialHomeomorph.trans G.toPartialDiffeomorph.toOpenPartialHomeomorph).source
    rw [OpenPartialHomeomorph.trans_source]
    change P' u ∈ c.source ∩ (c.toOpenPartialHomeomorph ⁻¹' G.toPartialDiffeomorph.toOpenPartialHomeomorph.source)
    refine ⟨?_, ?_⟩
    · change P' u ∈ (A.chart i).source
      have hPu : P u = p u := (hP huP).symm
      simpa [P', r, hPu] using hMaps huN
    · simp [G, G1, Diffeomorph.toPartialDiffeomorph]
  · intro y hy
    have hyN : y ∈ N := by
      have hy' : y ∈ P'.toPartialEquiv.source := hy.1
      change y ∈ r.source at hy'
      rw [OpenPartialHomeomorph.restr_source, hWopen.interior_eq] at hy'
      exact hy'.2.1
    change ev (s y) = _
    have hyP : y ∈ P.source := by
      have hy' : y ∈ r.source := hy.1
      rw [OpenPartialHomeomorph.restr_source, hWopen.interior_eq] at hy'
      exact hy'.1
    have hPy : P y = p y := (hP hyP).symm
    have hq : Q y =
        (g.1 • (A.chart i (p y)).1, g.2 • (A.chart i (p y)).2) := by
      change G (c (P' y)) = _
      change G ((A.chart i) (P y)) = _
      rw [hPy]
      rfl
    rw [hq]
    exact (hformula y hyN)

end HolomorphicAnosov.Ghys
