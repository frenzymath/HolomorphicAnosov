import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularityCore
import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularityRefinement
import HolomorphicAnosov.Analysis.Regularity.CampanatoPolynomialRegularity
import HolomorphicAnosov.Analysis.Regularity.JourneLeafPolynomialApproximation
import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Ambient smoothness from two uniformly smooth continuous graph foliations

Source: Journé (1988), theorem p.187 and proof pp.187–192; Campanato (1964),
§6 Theorem [6.1] p.156; Michor (1980), §4.2 pp.32–33. This is the local-to-manifold
statement of `zhang.rank_one_ambient_g3_journe_regularity` for real foliations
in arbitrary complementary dimensions, including zero. No holomorphic structure,
transverse differentiability, or continuity of higher transverse jets is assumed.
-/

noncomputable section

namespace HolomorphicAnosov

open Set JourneLeafPolynomialApproximation
open scoped Manifold ContDiff

/-- Ambient Journé regularity under the original all-order leafwise hypotheses.

Source: Journé, *A Regularity Lemma for Functions of Several Variables* (1988),
theorem p.187, finite-order argument pp.187–192; Campanato (1964), §6 Theorem
[6.1] p.156; Michor (1980), §4.2 pp.32–33. The finite polynomial-approximation
prerequisite retains its agent-written arbitrary-block construction, omitted in
Journé's printed proof. This statement does not attribute that construction to
Journé or assert a complete transitive formal proof.

Meaning of the local predicate and the coordinates:
`UniformSmooth` is a theorem-local abbreviation, not a new exported notion.
It asserts spatial smoothness of the ORIGINAL graph maps and the ORIGINAL
scalar plaque restrictions. Its bound is uniform over each strict smaller
leaf/transverse subbox, with a separate constant for each derivative order.
It asserts no continuity of higher jets as the transverse parameter varies.
The two atlases have independent boxes and the original local slice-preserving
overlap condition. `AreTransverse` compares their actual plaque derivative
ranges, for every common point and chart choice.

The use of `GraphFoliation ... 1 0` is only a packaging of the C¹ geometry.
Its zero-exponent difference bound is not a Hölder regularity assumption:
on a relatively compact smaller product box, joint continuity of graph values
and first spatial derivatives gives a finite common bound L. Shrinking and
recentering both original coordinate balls yields a graph box covering the
marked point; choose K at least the value bound and 2L. Then the difference of
two first derivatives has norm at most 2L ≤ K, and ‖x-y‖^0 = 1, even at x=y.
Thus precisely the finite order-one, exponent-zero `graph_bounds` field holds.
Repeating these smaller boxes covers the original open chart neighborhood and
inherits slice-preserving overlaps. Conversely those graph-box fields already
supply joint C¹ geometry. The all-order hypothesis below supplies the higher
spatial smoothness and bounds, without adding higher transverse regularity.
The bounds on all strict smaller centered subboxes express local uniformity:
every compact subbox lies in a strict smaller centered subbox, and finite
covering of that compact product turns locally uniform bounds into one bound.
No radius common to every derivative order is required in applying the proof.

The Lean proof uses the direct uniform-bound route of J1: it refines each original
atlas by ALL strict smaller centered product balls on the same Ω. Their actual chart
restrictions preserve inverse coordinates, slice overlaps and original tangent ranges.
The spatial next-derivative estimate gives C^{n,1/2} bounds, so J2–J4 apply to the
same function. The stronger compact-joint-jet norm-continuity argument documented
below is not needed by this proof. There are no admissions in this module's proof;
the two exact finite-order child applications still inherit their own admissions.

Every ambient chart e belongs to the actual smooth maximal atlas. The explicit
membership a∈e.source and Ω⊆e.target ensure that e.symm is its literal local
inverse wherever plaque restrictions are evaluated. In particular the scalar
function is exactly h∘e.symm, not an extension or another representative.
Existence of these local restrictions at each point records the two given
foliations in coordinates; the conclusion is local and requires no compatibility
between different ambient neighborhoods beyond the original smooth atlas.

Complete natural-language proof from the current node:

J1. Work locally in an original ambient smooth chart and fix n≥1 and α∈(0,1). Fix the plaque source and receiving Euclidean coordinate frames before comparing parameters. For each of the two graph families q_t and the scalar family u_t=h∘q_t, retain a common open source ball B(0,R) and a smaller closed ball K=closedBall(0,r), with 0<r<R, inside the common graph domains and inside the domains on which the locally uniform spatial bounds hold. For this fixed n shrink the parameter neighborhood and R if needed so that all bounds through order n+2 hold there. These radii and bounds may depend on n and the local center. No statement about a radius common to every n is made. The graph values have joint continuous evaluation by their assumed leafwise C¹ continuity; u_t has joint continuous evaluation because it is the composition of the original continuous h with these same q_t. Its spatial derivative bounds are exactly the assumed bounds of h in these graph coordinates, not bounds deduced by differentiating h transversely.

First retain the original uniform-bound argument. For either family, apply the convex derivative estimate on K to its order-n derivative map, with the fixed comparison linear map zero and the given bound on the derivative of order n+1. The iterated derivative recursion identifies this next derivative by the canonical isometric currying convention. This gives a uniform Lipschitz bound L for the order-n spatial derivative. If D=2r, then ||D^n v_t(x)−D^n v_t(y)||≤L D^(1−α)||x−y||^α for x,y∈K, since ||x−y||≤D. Lower derivatives and function values have the original locally uniform bounds. Thus the graph maps and the original h in their plaque coordinates have common C^{n,α} bounds. The positive margin R−r supplies derivatives at the boundary of K directly from the original open-domain maps.

There is also a stronger norm-continuity conclusion under this parent's all-order assumptions. Set k=n+1. Use the JOINT spatial jet J^k v_t=(v_t,Dv_t,…,D^k v_t) on K. Its target is one fixed finite-dimensional real coefficient space V for the finite derivative arrays in these frames; take the product maximum of their fixed Euclidean norms. Equivalently one can use the finite product of symmetric multilinear-map spaces with their fixed operator norms. These conventions are equivalent with constants depending only on the fixed dimensions and k: expansion on the fixed orthonormal coordinate vectors is a finite sum, and multilinear evaluation is bounded by operator norm times the product of the vector norms. In particular these constants do not vary with t. Do not form an independent product of closures of the different derivative families.

The spatial bounds through k+1=n+2 and the convex derivative estimate give a common Lipschitz constant for every component of this joint jet on K, hence equicontinuity of the joint jet family. The zeroth and all derivative bounds also place its entire range in one fixed closed ball S of V. Finite real coordinate spaces are finite dimensional and proper, so S is compact; K is compact and convex. Regard these continuous jets as bounded continuous maps K→V with the uniform metric. The existing Arzelà–Ascoli compact-closure theorem, with precisely this K, S and equicontinuous family, gives a compact closure C of the actual set {J^k v_t}. This is a single joint closure retaining all derivative compatibility.

Michor, Manifolds of Differentiable Mappings (1980), §4.2, printed pp.32–33, supplies the needed closed-jet assertion with its written proof. Its local lemma takes U closed and convex in a quadrant Q⊂ℝ^p and uniform limits of all derivatives through k. Apply that local lemma with U=K and Q=ℝ^p; no atlas extension or new boundary regularity hypothesis is needed. For each element of C, the metric-closure characterization gives a sequence of the original joint jets converging uniformly in every component. If their limit is (g_0,…,g_k), the printed segment-integral argument passes to the limit in v_j(x+y)=v_j(x)+∫_0^1 Dv_j(x+sy)y ds, yielding g_0(x+y)=g_0(x)+∫_0^1 g_1(x+sy)y ds. Michor explicitly identifies g_1=Dg_0 also on the boundary, then repeats the same step inductively to obtain D^i g_0=g_i for every i≤k. The source local lemma is used here on the closed convex ball, rather than assuming a manifold-with-corners atlas for a round ball. Consequently every member of C is a holonomic finite jet. Its derivative components are uniquely determined by its value component: uniqueness on the interior extends to the boundary by continuity.

Let π_0:C→π_0(C) be the zeroth projection onto its ACTUAL image in the uniform-norm space of scalar or Euclidean-valued continuous maps on K. It is continuous (its distance is bounded by joint-jet distance), is onto this image by definition, and is injective by the preceding printed closed-jet result. The domain C is compact and the target image is Hausdorff. Apply Continuous.homeoOfEquivCompactToT2 to the actual equivalence given by this bijective projection; its inverse is continuous. There is no inversion of a projection onto all continuous maps and no assertion that every continuous function is a jet value.

For the original families the continuous uncurried evaluation gives continuity t↦v_t in the compact-open topology by the existing continuous-map curry theorem. On compact K the compact-uniform convergence characterization gives continuity in the uniform metric: it applies to every parameter filter, not just sequences. The bounded-continuous-map distance criterion identifies the same uniform metric for these maps. Since v_t∈π_0(C), this is also continuity into the actual image subtype. Composing with the continuous inverse π_0^{-1} gives continuity t↦J^k v_t in the joint uniform jet norm. In particular every spatial derivative through n+1 varies continuously in sup norm on K. This argument uses compactness of the spatial ball and the joint jet closure; it assumes neither compactness nor differentiability of the transverse parameter space.

Finally fix t_0 and apply the same convex derivative estimate to the order-n derivative of v_t−v_{t_0}. Its derivative has sup norm δ_t=||D^{n+1}v_t−D^{n+1}v_{t_0}||_∞ tending to zero by the preceding conclusion. For x≠y in K the α-Hölder quotient of this difference is at most δ_t||x−y||^(1−α)≤δ_t D^(1−α). Together with convergence of the lower derivative sup norms, this proves full C^{n,α}-norm continuity of both the original graph family and the original h plaque family on the smaller domains. This is an additional source-following analytical component specific to the all-order parent hypotheses, not a strengthening of the finite-order weak Journé child.

A compact smaller ambient chart and the continuous complementary tangent fields give the original uniform positive transversality constant. The uniform C^{n,α} bounds and continuous first plaque derivatives just established are exactly what J2's unchanged approximation theorem requires. No transverse parameter has been differentiated. The stronger norm continuity does not supply a native generic bifoliated disk, the uniform-chart construction asserted without printed proof in DDRO Proposition3.4.1 p.23, or a limiting identification of finite-data DDRO extensions with the original h. None of those unmatched DDRO application steps is used to replace J2 here.

J2. Apply analysis.journe_transverse_leaf_polynomial_approximation in these original chart coordinates with p,q the positive complementary leaf dimensions. For every ambient center a₀ its exact conclusion supplies an open neighborhood V and common constants C>0,r>0, with B(a,r) contained in the chart domain for every a∈V. For each such a it supplies one polynomial P_a of total degree≤n satisfying |h(y)−P_a(y)|≤C||y−a||^{n+α} for every y∈B(a,r); P_a is fixed for that center, not chosen separately at each error scale. This is the exact input of J3. The child is currently split with a complete Stage1 own-level decomposition and retains its AGENT origin for the higher-dimensional construction omitted on Journé p.187. An exact human-written proof under those hypotheses remains unmatched. This application uses the exact child statement without supplying that omitted construction or asserting a whole human-proof replacement or transitive formal closure.

J3. Apply analysis.campanato_uniform_polynomial_approximation_regularity to this same continuous h, the common C,r on V and the fixed polynomial P_a for each center. Its exact conclusion makes the original pointwise h locally C^{n,α}, with continuous classical derivatives through order n and locally α-Hölder order-n derivatives, hence C^n, in the original ambient chart. The current complete child proof follows the acquired printed Campanato L² route: the supplied pointwise errors certify the uniform polynomial-approximation seminorm on a smaller ball; its minimizing polynomials may depend on center and radius. The printed coefficient-limit and derivative argument gives a C^{n,α} representative, and continuity identifies that representative everywhere with the original h. Thus no representative is substituted for the function used in J4.

J4. The hypotheses hold for every finite n, and each application keeps the same original h and ambient open chart. Regularity is local at every point, so for each n it gives C^n on that chart, even though bounds and intermediate smaller neighborhoods depend on n and the center. For the chart expression use contMDiffOn_iff_contDiffOn with real identity models to turn each C^n statement into ContMDiffOn of the same chart function and set. Combine all natural finite orders using contMDiffOn_infty; convert back by the same identity-model equivalence. This gives C∞ for each original smooth chart expression and hence ambient C∞ on M by the definition of smooth manifold maps. The order-zero continuity is already assumed. This is the smooth conclusion of Journé p.187; it asserts neither transverse smoothness of the foliations nor real analyticity of h.

J5. If one leaf dimension is zero, the complementary foliation has full dimension and its plaques are ambient open sets; its assumed C∞ graph parametrizations are local smooth coordinates, so plaque smoothness of h is already ambient smoothness. Empty M is vacuous. For positive leaf dimensions J1–J4 apply. The argument is local and requires no compactness, absolute continuity or dynamics.
-/
theorem rank_one_ambient_g3_journe_regularity
    {p q : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Block (p + q)) M]
    [IsManifold (𝓘(ℝ, Block (p + q))) ∞ M]
    (h : M → ℝ) (hh : Continuous h) :
    let UniformSmooth := fun (d c : ℕ) {Ω : Set (Block (p + q))}
      (F : GraphFoliation d c (p + q) 1 0 Ω) (f : Block (p + q) → ℝ) ↦
      ∀ i : F.Index,
        (∀ w ∈ Metric.ball 0 (F.box i).transverseRadius,
          ContDiffOn ℝ ∞ ((F.box i).graph w) (Metric.ball 0 (F.box i).leafRadius) ∧
          ContDiffOn ℝ ∞ (f ∘ (F.box i).plaque w)
            (Metric.ball 0 (F.box i).leafRadius)) ∧
        ∀ r : ℝ, 0 < r → r < (F.box i).leafRadius →
          ∀ s : ℝ, 0 < s → s < (F.box i).transverseRadius →
            ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧
              ∀ w ∈ Metric.ball (0 : Block c) s, ∀ x ∈ Metric.ball (0 : Block d) r,
                ‖iteratedFDeriv ℝ j ((F.box i).graph w) x‖ ≤ K ∧
                ‖iteratedFDeriv ℝ j (f ∘ (F.box i).plaque w) x‖ ≤ K;
    (∀ a : M,
      ∃ e : OpenPartialHomeomorph M (Block (p + q)),
        e ∈ IsManifold.maximalAtlas (𝓘(ℝ, Block (p + q))) ∞ M ∧ a ∈ e.source ∧
        ∃ Ω : Set (Block (p + q)), IsOpen Ω ∧ Ω ⊆ e.target ∧ e a ∈ Ω ∧
          ∃ F₁ : GraphFoliation p q (p + q) 1 0 Ω,
            ∃ F₂ : GraphFoliation q p (p + q) 1 0 Ω,
              AreTransverse F₁ F₂ ∧
                UniformSmooth p q F₁ (h ∘ e.symm) ∧
                UniformSmooth q p F₂ (h ∘ e.symm)) →
      ContMDiff (𝓘(ℝ, Block (p + q))) (𝓘(ℝ, ℝ)) ∞ h := by
  dsimp only
  intro H
  by_cases hp0 : p = 0
  · subst p
    apply smooth_from_finite_chart_regularities h
    intro n a
    obtain ⟨e, he, ha, Ω, hΩ, hΩtarget, hea, F₁, F₂, ht, hs₁, hs₂⟩ := H a
    obtain ⟨i, hi⟩ := F₂.cover (e a) hea
    have hplaque := ((hs₂ i).1 0 (by
      simpa using (F₂.box i).transverseRadius_pos)).2
    exact ⟨e, he, ha, (F₂.box i).image, (F₂.box i).image_open, hi,
      (smooth_on_full_dimensional_box (F₂.box i) (h ∘ e.symm) hplaque).of_le
        (by exact_mod_cast le_top)⟩
  · by_cases hq0 : q = 0
    · subst q
      apply smooth_from_finite_chart_regularities h
      intro n a
      obtain ⟨e, he, ha, Ω, hΩ, hΩtarget, hea, F₁, F₂, ht, hs₁, hs₂⟩ := H a
      obtain ⟨i, hi⟩ := F₁.cover (e a) hea
      have hplaque := ((hs₁ i).1 0 (by
        simpa using (F₁.box i).transverseRadius_pos)).2
      exact ⟨e, he, ha, (F₁.box i).image, (F₁.box i).image_open, hi,
        (smooth_on_full_dimensional_box (F₁.box i) (h ∘ e.symm) hplaque).of_le
          (by exact_mod_cast le_top)⟩
    · apply smooth_from_local_finite_graph_data (by omega) (by omega) h hh
      intro n hn a
      obtain ⟨e, he, ha, Ω, hΩ, htarget, hea, F₁, F₂, ht, hs₁, hs₂⟩ := H a
      obtain ⟨G₁, hf₁, parent₁, htan₁⟩ := refine_smooth_foliation F₁ (h ∘ e.symm) n
        (fun i ↦ (hs₁ i).1) (fun i ↦ (hs₁ i).2)
      obtain ⟨G₂, hf₂, parent₂, htan₂⟩ := refine_smooth_foliation F₂ (h ∘ e.symm) n
        (fun i ↦ (hs₂ i).1) (fun i ↦ (hs₂ i).2)
      have ht' : AreTransverse G₁ G₂ := by
        intro i j x hx₁ hx₂
        obtain ⟨hx₁old, heq₁⟩ := htan₁ i x hx₁
        obtain ⟨hx₂old, heq₂⟩ := htan₂ j x hx₂
        rw [heq₁, heq₂]
        exact ht (parent₁ i) (parent₂ j) x hx₁old hx₂old
      exact ⟨e, he, ha, Ω, hΩ, htarget, hea, G₁, G₂, ht', hf₁, hf₂⟩

end HolomorphicAnosov

