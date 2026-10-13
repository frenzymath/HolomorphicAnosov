import HolomorphicAnosov.Analysis.Complex.NormalizedUnivalentDefinitions
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.Complex.OmittedValuesSphericalDerivative
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import HolomorphicAnosov.Analysis.Complex.NormalizedUnivalentSequenceExtraction
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Compactness of normalized univalent disk maps

Source: Mikhail Lyubich, *Conformal Geometry and Dynamics of Quadratic
Polynomials*, vol. I–II, author-hosted September 2023 book, §4.4 Theorem 4.12
and Lemma 4.13, printed pp.113–114.

The domain is Mathlib's `Complex.UnitDisc`, with its original subspace topology.
The topology on continuous maps is the compact-open topology. Mathlib's
`ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn` identifies it
with uniform convergence on compact subsets of the disk. No behavior at or
outside the unit circle, and no common extension of the family, is assumed.
-/

namespace HolomorphicAnosov

/-- The normalized univalent family is compact for uniform convergence on
compact subsets of the open unit disk. The native continuous-map topology
is exactly this topology, not uniform convergence on the entire disk.

Source: Lyubich §4.4 Theorem 4.12 and Lemma 4.13, printed pp.113–114;
§4.3 Exercises 4.3–4.7 and Theorem 4.8, pp.111–112;
§3.3 Propositions 3.8–3.9, pp.107–108; spherical metric inputs
§2.4.13, pp.75–76, and §7.1/§7.3, pp.133,135–136.

The disk is locally compact and σ-compact, and the target is metrizable;
thus its compact-convergence continuous-map space is metrizable. Consequently
this compactness statement is equivalent to the node's sequential formulation:
every sequence in the family admits a strictly increasing subsequence converging
to a family member uniformly on each compact subdisk. Continuity on the open
disk and the ambient-coordinate zero extension change neither the family nor
this topology. Only the derivative modulus, not its phase, is fixed.

Full natural-language proof of `analysis.normalized_univalent_compactness`:

1. The compact-convergence topology on C(D,ℂ) is metrizable. Explicitly let r_m=1−1/(m+2), K_m={|z|≤r_m}, and d(f,g)=Σ_{m≥0}2^(−m−1) min(1,sup_{K_m}|f−g|). Every supremum is finite by continuity and compactness. Each truncated supremum satisfies the triangle inequality, the summable weights give a finite metric, and d(f,g)=0 forces equality on ⋃K_m=D. A small d bounds each fixed compact supremum (use its positive weight and a tolerance below one); conversely finitely many small compact suprema control the first terms and the geometric tail is arbitrarily small. Every compact K⊂D lies in some K_m because max_K|z|<1. These estimates identify metric neighborhoods with uniform convergence on compacta. Subspaces, including U, inherit this metric, so sequential compactness implies compactness by the named generic theorem. This is the explicit solution of the source Exercise 4.3 specialized to the Euclidean target; no topology on U is assumed beyond the stated one.

Inputs: mathlib.isCompact_iff_isSeqCompact_g2.

2. Prove Lemma 4.13 with its omitted planar step. An injective holomorphic f is nonconstant and hence open by the analytic open-mapping theorem; consequently f:D→V=f(D) is a homeomorphism and V is simply connected. If V contained the unit circle and some b with |b|<1 were outside V, that circle would contract in V⊂ℂ\{b}. Homotopy invariance would give winding zero, contradicting its winding one about b. Thus the closed unit disk lies in V. Its compactness inside the open V gives r>1 with B(0,r)⊂V: cover the closed disk by finitely many interior balls and take a positive common collar. The holomorphic inverse h on B(0,r) fixes zero and maps into D. Apply scalar Schwarz to ζ↦h(rζ) to get r|h′(0)|≤1, while the derivative chain rule for h∘f=id and |f′(0)|=1 gives |h′(0)|=1. This contradiction supplies an omitted unit-circle value.

Inputs: mathlib.differentiableOn_analyticOnNhd_complex_g5, mathlib.analyticOnNhd_complex_open_mapping_g5, analysis.lyubich_winding_holomorphic_zero_count, analysis.qc_holomorphic_embedding_inverse, mathlib.complex_schwarz_norm_deriv_le_one_g5, mathlib.hasFDerivAt_comp.

3. Start with any sequence f_n∈U. Choose a_n on the unit circle omitted by f_n and put h_n=a_n^(−1)f_n. The maps h_n fix zero, are univalent, have derivative modulus one, and omit one. Compactness of the unit circle (a closed bounded subset of the plane) and the compact-subsequence theorem let us first pass to a subsequence with a_n→a, |a|=1. On D*=D\{0}, injectivity makes every h_n omit zero as well. Subsequences extracted below retain convergence of these rotations.

Inputs: mathlib.isCompact_tendsto_subseq.

4. Obtain the precise punctured-disk Montel extraction from the spherical derivative estimate. On every disk B(c,R) compactly inside D*, the estimate gives a uniform spherical derivative bound on B(c,R/2), independent of n. Integrating along straight segments yields a uniform spherical Lipschitz bound there. Finite such neighborhoods cover each compact annulus L_m={1/(m+2)≤|z|≤1−1/(m+2)}; a common sufficiently small proximity radius lies in one of those neighborhoods, yielding equicontinuity on L_m. The spherical target is the compact round two-sphere, and all restrictions are bounded continuous maps into it. Arzela–Ascoli gives compact closure of these restrictions, and compact-subsequence extraction gives a uniformly spherical convergent subsequence on L_m. Successively extract on the increasing L_m and take a strictly increasing diagonal subsequence. The resulting limits agree on overlaps, define a continuous F:D*→the sphere and give spherical uniform convergence on every compact subset, since every compact subset lies in some L_m. This writes the Ascoli/locality step of Theorem 4.8 rather than treating it as a bounded Euclidean Montel theorem.

Inputs: analysis.lyubich_omitted_values_spherical_derivative_bound, mathlib.arzela_ascoli_compact_closure_g2, mathlib.isCompact_tendsto_subseq.

5. First establish the zero-free limit fact used by Exercises 4.4–4.7 and by limit injectivity. If nonvanishing holomorphic q_n on a connected open planar set converge Euclidean locally uniformly to q, the scalar limit theorem gives holomorphic q. If q is not identically zero but q(c)=0, analytic identity excludes a zero germ, and analytic factorization gives an isolated zero of order m≥1. Choose a small closed disk around c on which c is the only zero and q is nonzero on its boundary. Boundary uniform convergence makes q_n and q homotopic there through their straight interpolations, which avoid zero. The winding zero-count theorem forces q_n to have m zeros in the disk, contradicting nonvanishing. Therefore q is either identically zero or nowhere zero. All disks are selected with their closures inside the open holomorphy set.

Inputs: mathlib.holomorphic_locally_uniform_limit_scalar, mathlib.differentiableOn_analyticOnNhd_complex_g5, mathlib.analyticAt_zero_factorization_g5, analysis.analytic_identity_open_domain, analysis.lyubich_winding_holomorphic_zero_count.

6. Apply this fact to exclude isolated infinite values of F without assuming a meromorphic-limit theorem. If F(c)=∞, spherical continuity provides a small closed disk about c in D* on which F stays near infinity and thus away from zero. Spherical convergence puts the h_n in that same infinity chart eventually. The reciprocal functions 1/h_n converge Euclidean locally uniformly there to the continuous reciprocal coordinate of F: inversion is continuous into this finite chart, and the named compact uniform-continuity theorem on a fixed compact chart enclosure makes the coordinate map uniformly continuous. Choose the limit image in a smaller chart neighborhood whose closure is contained in the larger chart; uniform spherical convergence puts the tail images in that larger compact enclosure. They are holomorphic and nowhere zero, since h_n omit zero and infinity. Their limit vanishes at c, so the previous zero-free limit fact makes it identically zero on that disk. Thus F^−1({∞}) is open; it is also closed by continuity. Since D* is connected, either F is identically infinity or F is finite everywhere. In the finite alternative, F(K) lies in a bounded finite chart for each compact K; spherical uniform convergence is then Euclidean uniform convergence by the same compact-chart uniform-continuity argument, and the scalar limit theorem makes F holomorphic on D*.

Inputs: mathlib.holomorphic_locally_uniform_limit_scalar, analysis.lyubich_winding_holomorphic_zero_count, mathlib.differentiableOn_analyticOnNhd_complex_g5, mathlib.analyticAt_zero_factorization_g5, analysis.analytic_identity_open_domain, mathlib.isCompact_uniformContinuousOn_of_continuous.

7. The identically-infinity alternative contradicts winding. For any 0<r<1, apply the argument principle to h_n on B̄(0,r). Its only zero is zero, of order one because |h_n′(0)|=1; hence w_0(h_n|∂B(0,r))=1. The value one is omitted, so w_1 of the same loop is zero. If this loop missed the whole segment [0,1], moving the base value along that segment would force the two winding numbers to agree. Thus for every n some boundary point has |h_n(z)|≤1. Uniform spherical divergence to infinity on this boundary would instead force |h_n|>2 everywhere for large n. Consequently F is finite and the subsequence converges Euclidean uniformly on every compact subset of D*.

Inputs: analysis.lyubich_winding_holomorphic_zero_count.

8. Fill the puncture with Euclidean convergence, not merely pointwise removable values. For a fixed r<1, convergence on γ_r=∂B(0,r) makes h_n a uniformly Cauchy sequence there. Apply the boundary maximum-modulus theorem to each holomorphic difference h_n−h_k on B(0,r), whose closed disk lies in D, to obtain the same Cauchy bound throughout B̄(0,r). Completeness of ℂ gives pointwise limits; passing k to infinity in the uniform Cauchy bound proves uniform convergence on that closed disk. These limits agree with F off zero and agree for different r. They define g:D→ℂ, and the scalar locally-uniform limit theorem gives holomorphy on D. Since each h_n(0)=0, g(0)=0; locally uniform derivative convergence gives |g′(0)|=1.

Inputs: mathlib.complex_boundary_maximum_modulus_g5, mathlib.holomorphic_locally_uniform_limit_scalar, mathlib.holomorphic_locally_uniform_derivative.

9. Prove injectivity of g by the source argument-principle step. Normalization makes g nonconstant. If g(z)=g(w) with z≠w, choose a small closed disk about w avoiding z and contained in D, with g−g(z) nonzero on its boundary and a positive-order zero at w; identity and local analytic factorization justify that choice. The functions h_n−h_n(z) converge uniformly on this disk to g−g(z). Boundary straight interpolation avoids zero for large n, so zero-count equality gives a zero of h_n−h_n(z) in the disk. This is a second preimage of h_n(z), contradicting injectivity because z is outside the disk. Thus g is injective. The zero-free limit fact applied to h_n−1 also shows g omits one, since g(0)=0 rules out the identically-one alternative.

Inputs: mathlib.differentiableOn_analyticOnNhd_complex_g5, mathlib.analyticAt_zero_factorization_g5, analysis.analytic_identity_open_domain, analysis.lyubich_winding_holomorphic_zero_count.

10. Undo the rotations. On each compact K, h_n→g uniformly and is therefore eventually bounded there; a_n→a and |a_n|=1 imply f_n=a_n h_n→ag uniformly by the triangle inequality. The map ag is holomorphic and injective, fixes zero, and has derivative modulus |a| |g′(0)|=1. Thus every sequence in U admits a subsequence converging in the explicit compact-convergence metric to a member of U. The generic sequential-compactness equivalence from step 1 makes U compact, and conversely compactness gives the asserted subsequence formulation. No derivative phase is fixed and no omitted-value hypothesis has been added to U.

Inputs: mathlib.isCompact_iff_isSeqCompact_g2.
-/
theorem normalized_univalent_compactness :
    IsCompact {f : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent f} := by
  let : LocallyCompactSpace Complex.UnitDisc := by
    exact (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).locallyCompactSpace
  let : SecondCountableTopology Complex.UnitDisc :=
    Complex.UnitDisc.isEmbedding_coe.secondCountableTopology
  have hcompact_seq : IsCompact {f : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent f} ↔
      IsSeqCompact {f : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent f} :=
    isCompact_iff_isSeqCompact
  have h_extension : ∀ (f : C(Complex.UnitDisc, ℂ)) (z : Complex.UnitDisc),
      unitDiscExtension f z = f z := by
    intro f z
    dsimp [unitDiscExtension]
    split
    next hz => exact congrArg f (Subtype.ext rfl)
    next hz => exact (hz z.property).elim
  have h_punctured_zero : ∀ (f : C(Complex.UnitDisc, ℂ)),
      f ∈ {g : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent g} →
      ∀ z : Complex.UnitDisc, z ≠ 0 → f z ≠ 0 := by
    intro f hf z hz hzero
    exact hz (hf.2.1 (hzero.trans hf.2.2.1.symm))
  have h_derivative_nonzero : ∀ (f : C(Complex.UnitDisc, ℂ)),
      f ∈ {g : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent g} →
      deriv (unitDiscExtension f) 0 ≠ 0 := by
    intro f hf hzero
    simpa [hzero] using hf.2.2.2
  apply hcompact_seq.mpr
  intro u hu
  have hu_normalized : ∀ n, IsNormalizedUnivalent (u n) := by
    intro n
    exact hu n
  have hu_zero : ∀ n, (u n) 0 = 0 := by
    intro n
    exact (hu_normalized n).2.2.1
  have hu_deriv_ne : ∀ n, deriv (unitDiscExtension (u n)) 0 ≠ 0 := by
    intro n
    exact h_derivative_nonzero (u n) (hu n)
  have hu_off_zero : ∀ n z, z ≠ 0 → (u n) z ≠ 0 := by
    intro n z hz
    exact h_punctured_zero (u n) (hu n) z hz
  suffices hextract : ∃ v : C(Complex.UnitDisc, ℂ), IsNormalizedUnivalent v ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ K : Set Complex.UnitDisc, IsCompact K →
          TendstoUniformlyOn (fun n z ↦ u (φ n) z) v Filter.atTop K by
    obtain ⟨v, hv, φ, hφ, hlim⟩ := hextract
    refine ⟨v, hv, φ, hφ, ?_⟩
    exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr hlim
  obtain ⟨v, hvdiff, hvinj, hvzero, hvnorm, φ, hφ, hlim⟩ :=
    normalized_univalent_sequence_extraction unitDiscExtension h_extension u (by
      intro n
      simpa [IsNormalizedUnivalent] using hu_normalized n)
  refine ⟨v, ?_, φ, hφ, hlim⟩
  exact ⟨hvdiff, hvinj, hvzero, hvnorm⟩

end HolomorphicAnosov

