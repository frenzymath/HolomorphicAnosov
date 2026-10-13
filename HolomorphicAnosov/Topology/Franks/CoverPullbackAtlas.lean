import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.IsLocalHomeomorph

namespace HolomorphicAnosov.AbstractCoverPullback

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace E X] [TopologicalSpace Y]

/-- The literal sheet-composition atlas from Lee, Proposition 1.15, p. 9.
The preferred sheet is supplied by the native local-homeomorphism witness; its total
forward function is `p`, and composition with the downstairs preferred chart covers the point.
The atlas includes every local sheet agreeing with `p` on its source, not just the preferred ones.
-/
@[instance_reducible]
noncomputable def charts (p : Y → X) (hp : IsLocalHomeomorph p) :
    ChartedSpace (E) Y where
  atlas := {c | ∃ (e : OpenPartialHomeomorph Y X)
      (z : OpenPartialHomeomorph X (E)),
      Set.EqOn e p e.source ∧ z ∈ atlas (E) X ∧ c = e.trans z}
  chartAt y := (hp.localInverseAt y).symm.trans (chartAt (E) (p y))
  mem_chart_source y := by
    refine ⟨hp.self_mem_localInverseAt_target (x := y), ?_⟩
    simpa only [OpenPartialHomeomorph.symm_symm, hp.localInverseAt_symm,
      Set.mem_preimage] using mem_chart_source (E) (p y)
  chart_mem_atlas y := by
    refine ⟨(hp.localInverseAt y).symm, chartAt (E) (p y), ?_,
      chart_mem_atlas (E) (p y), rfl⟩
    intro x _
    exact congrFun (hp.localInverseAt_symm y) x


omit [ChartedSpace E X] in
/-- Guarded sheet cancellation in Lee's overlap calculation, Proposition 1.15, p. 9.
At a point in the lifted transition source the inverse of the first composed chart lies
in both lifted sources. The sheet identity and the downstairs right-inverse law then
identify its projection with the downstairs inverse coordinate. The second sheet identity
therefore identifies the lifted transition with the downstairs transition, on that domain only.
-/
theorem transition (p : Y → X)
    (e e' : OpenPartialHomeomorph Y X)
    (z z' : OpenPartialHomeomorph X (E))
    (he : Set.EqOn e p e.source) (he' : Set.EqOn e' p e'.source)
    {x : E} (hx : x ∈ ((e.trans z).symm.trans (e'.trans z')).source) :
    x ∈ (z.symm.trans z').source ∧
      ((e.trans z).symm.trans (e'.trans z')) x = (z.symm.trans z') x := by
  have hy := (e.trans z).map_target hx.1
  have hy' : (e.trans z).symm x ∈ (e'.trans z').source := by
    simpa only [OpenPartialHomeomorph.symm_symm, Set.mem_preimage] using hx.2
  have hpz : p ((e.trans z).symm x) = z.symm x := by
    rw [← he hy.1]
    exact e.right_inv hx.1.2
  refine ⟨⟨hx.1.1, ?_⟩, ?_⟩
  · change z.symm x ∈ z'.source
    rw [← hpz, ← he' hy'.1]
    exact hy'.2
  · change z' (e' ((e.trans z).symm x)) = z' (z.symm x)
    rw [he' hy'.1, hpz]


/-- All ordered pairs of the literal lifted atlas are smooth over the supplied scalar field.
Source: Lee, Proposition 1.15, p. 9, overlap paragraph, with its printed transition typo
corrected as in `transition`. Native downstairs manifold compatibility gives
smoothness of `z.symm.trans z'`; the guarded domain inclusion and equality restrict that
smoothness to the actual lifted overlap. This uses the supplied self model, so no boundary
or ambient-range condition is omitted.
-/
theorem isManifold [IsManifold (modelWithCornersSelf 𝕜 E) ∞ X]
    (p : Y → X) (hp : IsLocalHomeomorph p) :
    letI := charts (E := E) p hp
    IsManifold (modelWithCornersSelf 𝕜 E) ∞ Y := by
  let := charts (E := E) p hp
  apply isManifold_of_contDiffOn (modelWithCornersSelf 𝕜 E) ∞ Y
  intro c c' hc hc'
  obtain ⟨e, z, he, hz, rfl⟩ := hc
  obtain ⟨e', z', he', hz', rfl⟩ := hc'
  have hzz := IsManifold.compatible_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf 𝕜 E) (n := ∞) hz)
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf 𝕜 E) (n := ∞) hz')
  have hs := (contMDiffOn_of_mem_contDiffGroupoid hzz).contDiffOn
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id_eq, Set.range_id, Set.inter_univ]
  apply (hs.mono (fun x hx ↦ (transition p e e' z z' he he' hx).1)).congr
  intro x hx
  exact (transition p e e' z z' he he' hx).2


/-- Every actual local sheet and inverse is smooth for the literal pullback atlas.
Source: Lee, Proposition 1.15, p. 9, identity-coordinate argument. At a source point
choose a downstairs chart `z` containing its image and put `c = e.trans z`.
Both `c` and `z` are maximal-atlas members. On `c.source`, `e = z.symm ∘ c`;
near any target point, `e.symm = c.symm ∘ z`. The native chart smoothness and
composition lemmas therefore give both assertions locally on the actual open domains.
-/
theorem sheetSmooth [IsManifold (modelWithCornersSelf 𝕜 E) ∞ X]
    (p : Y → X) (hp : IsLocalHomeomorph p) :
    letI := charts (E := E) p hp
    ∀ e : OpenPartialHomeomorph Y X, Set.EqOn e p e.source →
      ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ e e.source ∧
        ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ e.symm e.target := by
  let := charts (E := E) p hp
  have := isManifold (𝕜 := 𝕜) (E := E) p hp
  intro e he
  constructor
  · intro y hy
    let z := chartAt (E) (e y)
    let c := e.trans z
    have hz : z ∈ IsManifold.maximalAtlas (modelWithCornersSelf 𝕜 E) ∞ X :=
      IsManifold.chart_mem_maximalAtlas (e y)
    have hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf 𝕜 E) ∞ Y :=
      IsManifold.subset_maximalAtlas ⟨e, z, he, chart_mem_atlas _ _, rfl⟩
    have hzy : e y ∈ z.source := mem_chart_source _ _
    have hcy : y ∈ c.source := ⟨hy, hzy⟩
    have hs := (contMDiffAt_symm_of_mem_maximalAtlas hz (z.map_source hzy)).comp y
      (contMDiffAt_of_mem_maximalAtlas hc hcy)
    apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [c.open_source.mem_nhds hcy] with t ht
    exact (z.left_inv ht.2).symm
  · intro x hx
    let z := chartAt (E) x
    let c := e.trans z
    have hz : z ∈ IsManifold.maximalAtlas (modelWithCornersSelf 𝕜 E) ∞ X :=
      IsManifold.chart_mem_maximalAtlas x
    have hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf 𝕜 E) ∞ Y :=
      IsManifold.subset_maximalAtlas ⟨e, z, he, chart_mem_atlas _ _, rfl⟩
    have hzx : x ∈ z.source := mem_chart_source _ _
    have hcx : z x ∈ c.target := ⟨z.map_source hzx,
      by simpa only [Set.mem_preimage, z.left_inv hzx] using hx⟩
    have hs := (contMDiffAt_symm_of_mem_maximalAtlas hc hcx).comp x
      (contMDiffAt_of_mem_maximalAtlas hz hzx)
    apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [z.open_source.mem_nhds hzx] with t ht
    change e.symm t = e.symm (z.symm (z t))
    rw [z.left_inv ht]


/-- Smooth local sheets imply a smooth projection and smoothness of every other sheet.
Source: Lee, Proposition 1.15, p. 9, uniqueness paragraph. The projection agrees near
each point with a supplied smooth sheet. For an arbitrary inverse sheet `e.symm` at `x`,
choose a supplied sheet `g` through `e.symm x`. Continuity keeps `e.symm` in `g.source`
after restriction. Both branches then project to the same point, so the left-inverse
law of `g` identifies `e.symm` with `g.symm` on that neighborhood. Smoothness is local.
-/
theorem smoothSheetsOfLocal [ChartedSpace (E) Y]
    (p : Y → X)
    (hlocal : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ e e.source ∧
        ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ e.symm e.target) :
    ContMDiff (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ p ∧
      ∀ e : OpenPartialHomeomorph Y X, Set.EqOn e p e.source →
        ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ e e.source ∧
          ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ e.symm e.target := by
  have hprojection : ContMDiff (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ p := by
    intro y
    obtain ⟨e, hy, he, hes, _⟩ := hlocal y
    apply (hes.contMDiffAt (e.open_source.mem_nhds hy)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hy] with t ht
    exact (he ht).symm
  refine ⟨hprojection, ?_⟩
  intro e he
  constructor
  · exact hprojection.contMDiffOn.congr he
  · intro x hx
    obtain ⟨g, hgy, hg, _, hgs⟩ := hlocal (e.symm x)
    have hpx : p (e.symm x) = x := by
      rw [← he (e.map_target hx), e.right_inv hx]
    have hgt : g (e.symm x) = x := (hg hgy).trans hpx
    have hs : ContMDiffAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ g.symm x := by
      rw [← hgt]
      exact hgs.contMDiffAt (g.open_target.mem_nhds (g.map_source hgy))
    apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
    have hn := (e.symm.continuousAt hx).preimage_mem_nhds (g.open_source.mem_nhds hgy)
    filter_upwards [e.open_target.mem_nhds hx, hn] with t ht htg
    have hpt : p (e.symm t) = t := by
      rw [← he (e.map_target ht), e.right_inv ht]
    calc
      e.symm t = g.symm (g (e.symm t)) := (g.left_inv htg).symm
      _ = g.symm t := congrArg g.symm ((hg htg).trans hpt)

/-- Smoothness of a continuous lift follows locally from the inverse sheet formula.
Source: Lee, Introduction to Smooth Manifolds, covering smooth structures, Proposition 2.12.
Choose a sheet around the image of the point. Continuity of the lift keeps its values in
that sheet; its lifting equation identifies it there with the smooth inverse sheet composed
with the downstairs map and projection. -/
theorem liftSmooth [IsManifold (modelWithCornersSelf 𝕜 E) ∞ X]
    (p : Y → X) (hp : IsLocalHomeomorph p)
    (f : X → X) (hf : ContMDiff (modelWithCornersSelf 𝕜 E)
      (modelWithCornersSelf 𝕜 E) ∞ f)
    (F : Y → Y) (hF : Continuous F) (hcomm : ∀ y, p (F y) = f (p y)) :
    letI := charts (E := E) p hp
    ContMDiff (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ F := by
  let := charts (E := E) p hp
  have hsheets := sheetSmooth (𝕜 := 𝕜) (E := E) p hp
  have hlocal : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ e e.source ∧
      ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) ∞ e.symm e.target := by
    intro y
    let e := (hp.localInverseAt y).symm
    have he : Set.EqOn e p e.source := fun t _ ↦ congrFun (hp.localInverseAt_symm y) t
    exact ⟨e, hp.self_mem_localInverseAt_target (x := y), he, hsheets e he⟩
  have hprojection := (smoothSheetsOfLocal p hlocal).1
  intro y
  obtain ⟨e, hey, he, _, hes⟩ := hlocal (F y)
  have hey' : e (F y) = f (p y) := (he hey).trans (hcomm y)
  have hs : ContMDiffAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E)
      ∞ e.symm (f (p y)) := by
    rw [← hey']
    exact hes.contMDiffAt (e.open_target.mem_nhds (e.map_source hey))
  apply (hs.comp y ((hf.comp hprojection) y)).congr_of_eventuallyEq
  filter_upwards [hF.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hey)] with t ht
  change F t = e.symm (f (p t))
  rw [← hcomm t, ← he ht]
  exact (e.left_inv ht).symm

end HolomorphicAnosov.AbstractCoverPullback
