import HolomorphicAnosov.Analysis.Measure.FiniteOrderDetection
import HolomorphicAnosov.Analysis.Measure.RegularZeroSetNull

/-!
# Null zero sets of real analytic functions

The domain is the original Euclidean space `EuclideanSpace ℝ (Fin N)`.
Its canonical `volume` is Lebesgue measure normalized to assign volume one
to every orthonormal unit parallelepiped. Analyticity is required only at
points of the open domain; no condition is imposed outside that domain.

Source: Boris S. Mityagin, *The Zero Set of a Real Analytic Function*,
arXiv:1512.07276v1 (22 December 2015), Proposition 0 and Claims 1–2,
pp. 1–3, equations (1)–(8).
-/

open Set MeasureTheory

namespace HolomorphicAnosov

/-- The zero set of a nontrivial real analytic function on a connected open
Euclidean domain has canonical Euclidean Lebesgue measure zero.

Source: Boris S. Mityagin, *The Zero Set of a Real Analytic Function*,
arXiv:1512.07276v1 (22 December 2015), Proposition 0 and Claims 1–2,
pp. 1–3, equations (1)–(8). Local source:
`literature/Mityagin-Zero-Set-Real-Analytic-2015-arxiv-v1.pdf`.
The source's implicit-function reference is Rudin (1964), second edition,
Theorem 9.18, pp. 195–201. The natural-language proof below is the full
DAG proof of `analysis.mityagin_real_analytic_zero_set_null_g6`, including
its exposed lower source and Mathlib applications.

Proof:

M1. For a real-analytic function B on U set F(B)={x∈U:B(x)=0} and G(B)={x∈U:B(x)=0 and ∇B(x)≠0}. For each positive integer k let G_k(B) consist of the x∈F(B) satisfying ‖x‖≤k, ‖∇B(x)‖≥1/k, and dist(x,ℝᴺ\U)≥1/k. When U=ℝᴺ omit the last condition, exactly as Mityagin p2 directs: no distance to the empty complement is used. Every point of G(B) belongs to some G_k(B), by positivity of its gradient norm and the distance of an interior point to the closed complement. Conversely every G_k(B) is contained in G(B). Analyticity gives continuity of B and its first derivatives on U. The distance condition keeps all closure points inside U, so the three inequalities and B=0 define a closed subset of the compact closed radius-k ball. Thus G_k(B) is compact; in the U=ℝᴺ case the same conclusion follows directly from global continuity. If B is identically zero, all G_k(B) are empty. This is Claim1 pp1–2, with its compactness and exhaustion conditions spelled out. The regularity premise here is supplied directly: for every x∈U apply mathlib.analyticAt_contDiffAt with scalar and target ℝ to B at x and order1 (or any finite order). ℝ is complete, so this gives C¹ locally at every point of U, including continuity of B and its first Fréchet derivative on U. The Euclidean coordinate partials are evaluations of that derivative at the fixed coordinate vectors, hence continuous. This argument uses no regularity of B outside U and does not require the finite-order detection assertion in M3.

M2. At y∈G_k(B), choose a coordinate j with ∂_jB(y)≠0. In the original E=ℝᴺ set H_j={v∈E:v_j=0}, and let e_j be the coordinate vector with j-th coordinate1 and every other coordinate0. H_j is a real linear subspace, and e_j∉H_j witnesses H_j≠⊤. Apply mathlib.addHaar_submodule_g6 to E, its usual Borel structure and its Euclidean Lebesgue measure: volume(H_j)=0. Define the continuous linear projection π_j(v)=v−v_j e_j onto H_j. The maps v↦(π_j(v),v_j) and (x,t)↦x+t e_j are inverse real linear coordinate identifications between E and H_j×ℝ; finite dimensionality makes them continuous. No isometry between the Euclidean norm and a product maximum norm is asserted or needed. At (π_j(y),y_j) the derivative of B(x+t e_j) in the scalar variable is multiplication by ∂_jB(y)≠0, hence is a continuous linear equivalence. Using the C¹ certificate for the real-analytic B obtained in M1 from mathlib.analyticAt_contDiffAt, mathlib.contDiffAt_implicitFunction at order1 gives a C¹ function ψ on a sufficiently small OPEN neighborhood V of π_j(y) in H_j, and an OPEN product neighborhood contained in U on which B(x+t e_j)=0 if and only if t=ψ(x). Shrink V and the product neighborhood to those on which both this equation and C¹ regularity hold.

Bind nullity using a map of the SAME E into itself. Extend ψ arbitrarily as a total function on H_j outside V, and define F(v)=π_j(v)+ψ(π_j(v))e_j. The set O=π_j⁻¹(V) is OPEN in E. On O the totalization agrees with the C¹ local ψ, so the derivative chain and sum rules give DifferentiableOn ℝ F O. Let S=H_j∩O. Since S⊆H_j, volume(S)=0; restricting DifferentiableOn from O to S and applying mathlib.addHaar_image_null_of_differentiableOn_g5 gives volume(F(S))=0. There is no assertion of regularity outside O. If z is a zero of B in the selected product neighborhood, then π_j(z)∈V, π_j(z)∈H_j and z_j=ψ(π_j(z)); hence π_j(z)∈S and F(π_j(z))=z. Thus the zero set in that neighborhood, and in particular its intersection with G_k(B), is null. For N=1 the subspace H_j is {0}; the same construction covers the locally isolated zero, without a separate positive-dimensional unsolved variable.

Use mathlib.isCompact_elim_finite_subcover_g2 on the compact G_k(B) and these original OPEN neighborhoods. Their finitely many null zero-set pieces cover G_k(B), and mathlib.measure_iUnion_null applied to the finite index type yields volume(G_k(B))=0. This supplies the lower nullity application behind Mityagin Claim1 p2: the paper invokes nice coordinates but does not print this projection/graph-map calculation. The proper-subspace and differentiable-null-image statements are separate exact Mathlib inputs; compact finite extraction alone does not establish nullity. The analytic-to-C¹ premise is obtained from mathlib.analyticAt_contDiffAt as in M1; no new C¹ hypothesis is inserted into Proposition0. When B is a classical mixed partial D^tA, the ordered fixed-tuple identification and its analytic regularity are supplied by M3/M4 on this same original U. The occurrence of F(A) in Claim1 p2 is read as F(B), as required by the claim and its surrounding definitions.

M3. Bind the analytic derivative fields, their TRUE derivatives, and the classical ordered-coordinate dictionary on the ORIGINAL open domain U. Write E=EuclideanSpace ℝ (Fin N), with its original Euclidean norm, and T_m(x)=iteratedFDeriv ℝ m A x. The canonical real target is complete by mathlib.real_completeSpace_g6. For every m≥0 mathlib.analyticOnNhd_iteratedFDeriv_g6 therefore makes T_m analytic at every x∈U, with values in the actual continuous m-multilinear maps E^m→ℝ. Its target completeness must also be bound before applying analytic-to-smoothness: use mathlib.continuousMultilinearMap_instCompleteSpace_g6 with slots Fin m, each slot the original normed E and target ℝ. Scalar multiplication and addition are continuous in these normed spaces, ℝ is complete, and the finite product is metrizable and hence sequential, including the singleton empty product for m=0. The source operator-norm structure retains this SAME canonical uniformity. Thus the actual T_m target is complete; neither completeness of an arbitrary input nor a changed multilinear norm is inserted.

For x∈U apply mathlib.analyticAt_contDiffAt to this analytic T_m with order ω. Then mathlib.contDiffAt_differentiableAt, with the nonzero order ω, gives DifferentiableAt ℝ T_m x, and mathlib.differentiableAt_hasFDerivAt gives the TRUE certificate HasFDerivAt T_m (fderiv ℝ T_m x) x. Only after this certificate use mathlib.iteratedFDeriv_recursion_g7: the derivative is the left curry of T_(m+1)(x), namely v↦(h↦T_(m+1)(x)(v::h)). The raw selected-fderiv recursion is not treated as differentiability by itself.

For a fixed tuple h:Fin m→E, evaluation ev_h(S)=S(h) is real linear and bounded by mathlib.continuousMultilinearMap_le_opNorm_g7:
|ev_h(S)|≤||S||∏_l||h_l||.
Hence it is an actual continuous linear map in the operator-norm target. The m=0 tuple is empty and its product is1. mathlib.continuousLinearMap_comp_analyticOnNhd_g6 makes B_h=ev_h∘T_m analytic on U. Apply mathlib.continuousLinearMap_hasFDerivAt to ev_h and mathlib.hasFDerivAt_comp to the TRUE derivative certificate above. This gives the actual derivative
DB_h(x)v=T_(m+1)(x)(v::h)
for every x∈U. No tensor symmetry is used to prove B_h analytic or differentiable.

Bind classical first partials using the actual written Lee2003 Appendix Lemma A.54, printed585/PDF601, on the SAME original Euclidean open U. Differentiability gives B_h(x+v)−B_h(x)−DB_h(x)v=o(||v||). Put v=t e_j for the original coordinate vector e_j, divide by t and take t>0 and t<0 separately as the source does; the error divided by |t| tends0. Since U is open, this coordinate line stays in U for all sufficiently small |t|. The two limits give ∂_jB_h(x)=DB_h(x)e_j=T_(m+1)(x)(e_j::h). This is a classical partial of the ORIGINAL function on U, not an added derivative notion or regularity outside U.

Starting with the empty tuple, T_0(x) evaluated at it is A(x) by the zeroth recursion. Repeatedly apply the preceding first-partial formula to the analytic fixed-tuple functions B_h. Induction on the length now identifies every ordered classical coordinate differentiation of A with T_m(x) evaluated on its corresponding ordered coordinate tuple; prepending j agrees with differentiating the scalar field once more. To compare orders, apply mathlib.analyticAt_contDiffAt to A itself with real complete target and order ω at x∈U. The exact mathlib.contDiffAt_iteratedFDeriv_comp_perm_g6 then identifies evaluations of T_m(x) on tuples differing by a permutation. Its premise is ω, not a weaker indexed⊤ certificate. For a multi-index s∈ℕ^N, enumerate s_j copies of the original coordinate j in a fixed canonical order. Every tuple with those multiplicities differs by a finite permutation, so it represents the SAME classical D^sA(x). In particular
∂_j(D^tA)(x)=D^(t+e_j)A(x)
on U. The finite enumeration/permutation is an explicit original-coordinate application of this symmetry theorem. Duplicate coordinates and the empty multi-index are included; no arbitrary formal-series symmetry is asserted.

Now bind finite-order detection, the local step in Mityagin Claim2. Suppose w∈U and ALL classical D^sA(w)=0, including s=0. The preceding dictionary implies T_m(w)(e_(r(0)),…,e_(r(m−1)))=0 for EVERY ordered coordinate choice r:Fin m→Fin N. Construct the ORIGINAL Euclidean coordinate basis as follows. Let Φ=EuclideanSpace.equiv (Fin N) ℝ from mathlib.euclideanSpace_equiv_g8. Apply mathlib.module_basis_map_g8 to Pi.basisFun ℝ (Fin N) and Φ.symm.toLinearEquiv. mathlib.pi_basisFun_apply and mathlib.pi_basisFun_repr identify its vectors with Φ.symm(Pi.single j 1), precisely the original e_j, and retain their original coordinate representation. This is an algebraic basis transported by the actual coordinate equivalence; it asserts no isometry between Euclidean and Pi supremum norms.

Apply mathlib.module_basis_ext_multilinear_g6 with scalar ℝ, slots Fin m, this basis in each slot, f=T_m(w).toMultilinearMap and g=0. The ordered-coordinate equality above meets EVERY source basis-tuple premise, so the actual multilinear map T_m(w) is0. The m=0 premise is its unique empty tuple A(w)=0, not an omitted positive-order case. In particular T_m(w)(fun _↦y)=0 for every original y∈E and every m.

Unfold AnalyticAt of A at w to choose one actual HasFPowerSeriesOnBall A p w r with r>0. Shrink its ball to lie in U, using openness at w and the source certificate on the smaller ball; no analyticity outside U is required. Apply mathlib.hasFPowerSeriesOnBall_hasSum_iteratedFDeriv_g6 over ℝ to this SAME ball, complete real target and characteristic zero. For every y in its original EMetric.ball(0,r) it gives
HasSum (m↦(m!:ℝ)^−1 • T_m(w)(fun _↦y)) (A(w+y)).
All terms are0 by the preceding derivative conclusion. Unfold HasSum as convergence of the finite partial sums over Finset ℕ directed by inclusion: every partial sum is identically0. This directed filter is nontrivial (the empty finite set exists and unions give common upper bounds), and the constant sums converge to0. Apply mathlib.tendsto_nhds_unique_of_forall in the Hausdorff real target to this constant-zero limit and the SAME HasSum certificate. Thus A(w+y)=0 throughout one actual neighborhood of w. The formal multilinear series p is NOT asserted0; the theorem supplies the diagonal factorial Taylor sum directly, so possibly nonsymmetric coefficients are never replaced by a single derivative.

The existing analysis.analytic_identity_open_domain now propagates equality with the analytic zero function from this neighborhood to the original connected, hence preconnected U. That contradicts the given point of U where A is nonzero. Consequently at every w∈F(A) some classical partial is nonzero. This establishes the finite-order conclusion used by Claim2 without changing the proposition’s nontriviality premise, the classical derivative convention or the original domain.

M4. At w∈F(A), M3 supplies a nonzero classical partial. Choose a multi-index s of smallest total degree r with D^sA(w)≠0. Since D^0A(w)=A(w)=0, r≥1. Select j with s_j>0 and put t=s−e_j, coordinatewise natural subtraction. Then |t|=r−1 and t+e_j=s. Minimality gives D^tA(w)=0. The actual ordered-tuple/ω-permutation dictionary proved in M3 gives
∂_j(D^tA)(w)=D^(t+e_j)A(w)=D^sA(w)≠0.
Thus the original gradient of B=D^tA at w has a nonzero coordinate. By M3 this B is the scalar fixed-tuple field ev_h∘T_(|t|) for the canonical tuple of multiplicities t, and is analytic at every point of U by mathlib.analyticOnNhd_iteratedFDeriv_g6 and mathlib.continuousLinearMap_comp_analyticOnNhd_g6. mathlib.analyticAt_contDiffAt with real complete target gives its C¹ regularity at all points of U. Hence M1–M2 apply to this SAME classical partial B with their actual regularity premise and prove its regular-zero sets null. We have w∈G(D^tA), so
F(A)⊆⋃_{t∈ℕ^N}G(D^tA),
exactly Mityagin equations6–8 pp2–3. The original multi-index type is countable because N is finite. This is a cover, not a disjoint decomposition; no uniform order of vanishing is asserted. The first-partial identification, derivative-field regularity and permutation certificates are source applications to the original U, not additional hypotheses.

M5. For each original multi-index t, the analytic classical partial D^tA supplied in M3–M4 satisfies M1–M2, so G(D^tA)=⋃_{k≥1}G_k(D^tA) is a countable union of null sets. Apply mathlib.measure_iUnion_null first to the positive-integer k union and then to the countable multi-index t union in M4. Outer measure monotonicity and F(A) being a subset of that union yield volume(F(A))=0. These null union and subset conclusions require no separate measurability of the individual subsets. This is the final paragraph of Proposition0 on p3. The source argument is complete at this node’s one-level source/API application: its named lower providers and exact native coordinate/derivative/Taylor bindings are identified above. This is not a Lean/kernel or transitive-caller certificate, a peer-reviewed proof-version claim, or a whole human proof of the weak arbitrary-block Journé variant.

The nonzero witness forces the domain to be nonempty. The case N=1 is
included, as is the entire or an unbounded Euclidean domain. A nonzero
constant has empty zero set. The identically zero function is excluded by
the witness. Connectedness is essential: on a disconnected open domain a
function can vanish on one component and be nonzero on another. No
regularity outside U, global analytic extension, or change to a Pi supremum
norm or arbitrarily normalized volume is assumed.
-/
theorem volume_real_analytic_zero_set {N : ℕ} (_hN : 1 ≤ N)
    (U : Set (EuclideanSpace ℝ (Fin N)))
    (A : EuclideanSpace ℝ (Fin N) → ℝ)
    (_hUopen : IsOpen U) (hUconn : IsConnected U)
    (hA : ∀ x ∈ U, AnalyticAt ℝ A x)
    (hA_nonzero : ∃ x ∈ U, A x ≠ 0) :
    volume {x | x ∈ U ∧ A x = 0} = 0 := by
  classical
  let S := fun n : ℕ ↦ {x | x ∈ U ∧ iteratedFDeriv ℝ n A x = 0 ∧
    fderiv ℝ (iteratedFDeriv ℝ n A) x ≠ 0}
  have hS (n : ℕ) : volume (S n) = 0 :=
    volume_regular_zero_set_eq_zero _ U (fun x hx ↦
      ((show AnalyticOnNhd ℝ A U from hA).iteratedFDeriv n x hx).contDiffAt)
  apply measure_mono_null (t := ⋃ n, S n) _ (measure_iUnion_null hS)
  intro x hx
  have hex := analytic_exists_iteratedFDeriv_ne_zero U A hUconn hA hA_nonzero hx.1
  let n := Nat.find hex
  have hn : iteratedFDeriv ℝ n A x ≠ 0 := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra hnpos
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnpos
    apply hn
    rw [hn0]
    ext v
    simpa using hx.2
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  apply mem_iUnion.mpr
  refine ⟨k, hx.1, ?_, ?_⟩
  · exact not_not.mp (Nat.find_min hex (by omega))
  · intro hzero
    apply hn
    rw [hk]
    ext v
    rw [iteratedFDeriv_succ_apply_left, hzero]
    rfl

end HolomorphicAnosov
