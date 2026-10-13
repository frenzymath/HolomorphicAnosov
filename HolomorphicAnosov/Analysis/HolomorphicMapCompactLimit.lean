import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Compact-local uniform limits of holomorphic manifold maps

DAG node: `analysis.holomorphic_map_compact_limit_g2`.

Source: Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*,
arXiv:2609.37695v1, Section 3 p.11 and Lemma 3.2 p.12; Demailly,
*Complex Analytic and Differential Geometry*, June 21, 2012, I §3.B pp.22–23,
formula (3.8), and I §3.C p.23.

The identity complex models are boundaryless. `IsManifold` at complex regularity
`∞` expresses the holomorphic-atlas convention: finite-dimensional holomorphic
transition maps are complex C∞, and complex C∞ transitions are holomorphic.
Holomorphic maps themselves are expressed by `MDifferentiable` over ℂ, not real
smoothness. The target metric supplies the very topology used by its atlas.
-/

open scoped ContDiff Manifold Topology _root_.Topology

namespace HolomorphicAnosov

universe uE uF uM uN

/-- A compact-local uniformly convergent sequence of holomorphic maps has a
holomorphic continuous limit.

Source: Zhang Section 3 p.11 and Lemma 3.2 p.12; Demailly I §3.B pp.22–23
and I §3.C p.23. Natural-language proof, as recorded in the DAG:

1. Assume first that the source and target dimensions are positive, and fix x∈M. Choose the
preferred source holomorphic chart χ about x and the preferred target chart ψ about f(x). Choose
a Euclidean coordinate ball B(c,R), c=ψ(f(x)), whose closed ball lies inside the target chart
image. Put V=ψ⁻¹(B(c,R)) and C=ψ⁻¹(closedBall(c,R)); the inverse chart is continuous on the
closed coordinate ball, so C is compact in N. By continuity of f, the open set
χ(source(χ)∩f⁻¹(V)) contains χ(x). Choose an open polydisc D centered at χ(x) with its closed
polydisc contained in that open set. Its inverse-chart image K=χ⁻¹(closure D) is compact in M by
finite-dimensional compactness and continuity of χ⁻¹, and f(K)⊂V. Thus neither a common target
chart for all j nor any global compactness of M or N is assumed.

2. There is δ>0 such that any point of N at d_N-distance less than δ from any point of f(K) lies
in V. Indeed, for each a∈f(K), openness of V gives r_a>0 with ball(a,3r_a)⊂V. Finitely many
balls ball(a,r_a) cover compact f(K); choose δ to be the minimum of their finitely many positive
radii. If b∈f(K) belongs to ball(a,r_a) and d_N(y,b)<δ≤r_a, the triangle inequality gives
d_N(y,a)<2r_a, so y∈V. Uniform convergence on K with tolerance δ therefore gives J such that
f_j(K)⊂V⊂C for every j≥J. The compact set is nonempty because it contains f(x); an empty M is
dealt with below. This argument uses only the compatible metric, not its completeness or
properness.

3. The restriction of ψ to C is continuous into its finite-dimensional complex coordinate space,
so the compact uniform-continuity theorem makes it uniformly continuous for d_N and the
Euclidean coordinate metric. Given η>0, choose its uniform-continuity tolerance τ>0. For all
sufficiently large j≥J, the original convergence on K gives d_N(f_j(y),f(y))<τ for every y∈K;
both values lie in C, hence ||ψ(f_j(y))−ψ(f(y))||<η. Therefore g_j=ψ∘f_j∘χ⁻¹, for the tail j≥J,
converges uniformly on closure D to g=ψ∘f∘χ⁻¹. These coordinate maps are defined on an open
neighborhood of D, and each g_j is holomorphic there as a composition of holomorphic maps and
charts; g is continuous. Initial terms before J may be discarded without changing convergence.

4. For each point z∈D, each input coordinate i, and each output coordinate l, restrict the l-th
coordinate of g_j and g to the coordinate-line disc obtained by fixing all input coordinates
except i. It is an open disc because D is a polydisc. Their uniform convergence on closure D
implies uniform convergence on this disc and thus locally uniform convergence there: for any
positive tolerance the uniform bound already holds on the entire disc. Every tail approximant is
complex differentiable on the disc. Apply the scalar locally uniform limit theorem with index ℕ,
filter atTop (which is nontrivial), and codomain ℂ (which is complete). It gives complex
differentiability of the l-th coordinate of g on that slice. Reassemble the finitely many output
coordinates, obtaining complex differentiability of g on every coordinate-line preimage in D.

5. Demailly §3.B gives the continuous separate-holomorphy upgrade: apply
analysis.contDiffOn_of_continuousOn_separately_holomorphic to continuous g and all the preceding
coordinate-line restrictions on open D. Hence g is complex C∞ on D, and
geometry.complex_holomorphic_iff gives complex Fréchet differentiability at each point of D. For
the preferred source and target charts this is the local coordinate expression of f. The complex
manifolds have boundaryless identity models, whose model range is the whole coordinate space;
differentiability at χ(x) implies the required differentiability within that range. Ambient
continuity of f at x is already a hypothesis. The two conjuncts of
mathlib.mdifferentiableAt_coordinate_criterion therefore prove holomorphicity of f at x. Since x
was arbitrary, f is holomorphic on M. Equivalently, §3.C identifies the holomorphic coordinate
conclusion with holomorphicity in the original manifold atlas.

6. If M is empty the assertion is vacuous. A zero-dimensional source has singleton open
coordinate neighborhoods, so every map is locally constant and holomorphic. A zero-dimensional
target is discrete; continuity of f makes it locally constant, and its zero-dimensional
coordinate expression is holomorphic. If N is empty, existence of f forces M empty. Uniform
convergence on the empty compact set is vacuous under the stated ε formulation. Thus all
degenerate cases are covered without adding nonemptiness or positive dimension hypotheses.

The model spaces are arbitrary finite-dimensional complex normed spaces; their
finite dimensions may be zero. No nonemptiness, connectedness, completeness,
properness of the target metric, or global compactness of either manifold is
assumed. Hausdorffness of the target follows from its metric. Second countability
is retained for both manifolds. The literal ε formulation includes empty compact
sets without introducing a real supremum.

Implementation: the compact-neighborhood basis of each finite-dimensional manifold
chooses the compact source neighborhood K and compact receiving-chart enclosure L.
Compact-open convergence gives eventual containment in interior L directly; uniform
continuity on L transfers the original metric convergence into chart coordinates.
Finite-basis continuous linear equivalences identify the arbitrary model spaces
with the existing finite complex coordinate products. On the resulting open set,
the one-variable uniform-limit theorem applies to each exact coordinate-line
preimage. The imported separate-holomorphy theorem supplies the polydisc analytic
upgrade, including empty coordinate products. Its complex differentiability
conclusion is transported back to the original models and the manifold criterion.
The separate-holomorphy theorem remains an admitted dependency; this proof creates
no new admission and does not use the separate compatibility equivalence theorem.
-/
theorem holomorphic_map_compact_limit
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {M : Type uM} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    {N : Type uN} [MetricSpace N] [SecondCountableTopology N]
    [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]
    (fSeq : ℕ → M → N) (f : M → N)
    (hholomorphic : ∀ j, MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) (fSeq j))
    (hcontinuous : Continuous f)
    (hcompact : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ x ∈ K, dist (fSeq j x) (f x) < ε) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have : ProperSpace F := FiniteDimensional.proper ℂ F
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace F N
  have hcseq : ∀ j, Continuous (fSeq j) := fun j ↦ (hholomorphic j).continuous
  have hunif : ∀ K : Set M, IsCompact K →
      TendstoUniformlyOn fSeq f Filter.atTop K := by
    intro K hK
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨J, hJ⟩ := hcompact K hK ε hε
    filter_upwards [Filter.eventually_ge_atTop J] with j hj
    intro y hy
    simpa only [dist_comm] using hJ j hj y hy
  have hmaps : Filter.Tendsto (fun j ↦ (⟨fSeq j, hcseq j⟩ : C(M, N)))
      Filter.atTop (𝓝 (⟨f, hcontinuous⟩ : C(M, N))) :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr hunif
  intro x
  let e := chartAt E x
  let e' := chartAt F (f x)
  obtain ⟨L, ⟨hLnhds, hLc⟩, hLsub⟩ := (compact_basis_nhds (f x)).mem_iff.mp
    (e'.open_source.mem_nhds (mem_chart_source F (f x)))
  have hxL : f x ∈ interior L := mem_interior_iff_mem_nhds.mpr hLnhds
  obtain ⟨K, ⟨hKnhds, hKc⟩, hKsub⟩ := (compact_basis_nhds x).mem_iff.mp
    (Filter.inter_mem (e.open_source.mem_nhds (mem_chart_source E x))
      (hcontinuous.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hxL)))
  have hfKL : Set.MapsTo f K L := fun y hy ↦ interior_subset (hKsub hy).2
  have hevL : ∀ᶠ j in Filter.atTop, Set.MapsTo (fSeq j) K L := by
    have h := hmaps.eventually
      (ContinuousMap.eventually_mapsTo hKc isOpen_interior (fun y hy ↦ (hKsub hy).2))
    exact h.mono fun j hj y hy ↦ interior_subset (hj hy)
  have huchart : UniformContinuousOn e' L :=
    hLc.uniformContinuousOn_of_continuous (e'.continuousOn.mono hLsub)
  have hcu : TendstoUniformlyOn (fun j y ↦ e' (fSeq j y)) (fun y ↦ e' (f y))
      Filter.atTop K :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hevL hfKL huchart (hunif K hKc)
  let a := (Module.finBasis ℂ E).equivFunL
  let b := (Module.finBasis ℂ F).equivFunL
  let U : Set E := e.target ∩ e.symm ⁻¹' interior K
  have hUopen : IsOpen U := e.isOpen_inter_preimage_symm isOpen_interior
  let S : Set (ComplexModel (Module.finrank ℂ E)) := a.symm ⁻¹' U
  have hSopen : IsOpen S := hUopen.preimage a.symm.continuous
  have hxS : a (e x) ∈ S := by
    change a.symm (a (e x)) ∈ e.target ∩ e.symm ⁻¹' interior K
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨e.map_source (mem_chart_source E x), by
      change e.symm (e x) ∈ interior K
      rw [e.left_inv (mem_chart_source E x)]
      exact mem_interior_iff_mem_nhds.mpr hKnhds⟩
  let gSeq := fun j z ↦ b (e' (fSeq j (e.symm (a.symm z))))
  let g := fun z ↦ b (e' (f (e.symm (a.symm z))))
  have hsource : Set.MapsTo (fun z ↦ e.symm (a.symm z)) S K :=
    fun z hz ↦ interior_subset hz.2
  have hgconv : TendstoUniformlyOn gSeq g Filter.atTop S := by
    have h := b.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformlyOn hcu
    exact (h.comp (fun z ↦ e.symm (a.symm z))).mono hsource
  have hgdiff : ∀ᶠ j in Filter.atTop, DifferentiableOn ℂ (gSeq j) S := by
    filter_upwards [hevL] with j hj
    intro z hz
    have hsrc : a.symm z ∈ e.target := hz.1
    have htar : fSeq j (e.symm (a.symm z)) ∈ e'.source := hLsub (hj (hsource hz))
    have hd := (mdifferentiableAt_atlas (I := 𝓘(ℂ, F)) (chart_mem_atlas F (f x)) htar).comp
      (a.symm z) ((hholomorphic j (e.symm (a.symm z))).comp
        (a.symm z) (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, E))
          (chart_mem_atlas E x) hsrc))
    have hnorm := (mdifferentiableAt_iff_differentiableAt.mp hd)
    exact (b.differentiableAt.comp z
      (hnorm.comp z a.symm.differentiableAt)).differentiableWithinAt
  have hgsep : ∀ z : ComplexModel (Module.finrank ℂ E), ∀ i : Fin (Module.finrank ℂ E),
      DifferentiableOn ℂ (g ∘ Function.update z i) ((Function.update z i) ⁻¹' S) := by
    intro z i
    have hu : Differentiable ℂ (Function.update z i) :=
      fun t ↦ (hasFDerivAt_update z t).differentiableAt
    apply ((hgconv.comp (Function.update z i)).tendstoLocallyUniformlyOn).differentiableOn
    · exact hgdiff.mono fun j hj ↦ hj.comp hu.differentiableOn (Set.mapsTo_preimage _ _)
    · exact hSopen.preimage hu.continuous
  have hgcont : ContinuousOn g S := by
    have hcoord : ContinuousOn (fun y ↦ e' (f y)) K :=
      e'.continuousOn.comp hcontinuous.continuousOn (fun y hy ↦ hLsub (hfKL hy))
    exact b.continuous.continuousOn.comp
      (hcoord.comp (e.symm.continuousOn.comp a.symm.continuous.continuousOn
        (fun z hz ↦ hz.1)) hsource) (Set.mapsTo_univ _ _)
  have hgd : DifferentiableOn ℂ g S :=
    (contDiffOn_of_continuousOn_separately_holomorphic hSopen hgcont hgsep).differentiableOn
      (by simp)
  have hgat := hgd.differentiableAt (hSopen.mem_nhds hxS)
  have hcoordat : DifferentiableAt ℂ (e' ∘ f ∘ e.symm) (e x) := by
    have h := b.symm.differentiableAt.comp (e x) (hgat.comp (e x) a.differentiableAt)
    simpa only [g, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h
  apply (mdifferentiableAt_iff f x).mpr
  refine ⟨hcontinuous.continuousAt, ?_⟩
  simpa only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    mfld_simps] using hcoordat.differentiableWithinAt (s := Set.range (𝓘(ℂ, E)))


end HolomorphicAnosov
