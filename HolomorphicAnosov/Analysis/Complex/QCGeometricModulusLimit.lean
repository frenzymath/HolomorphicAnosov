import HolomorphicAnosov.Analysis.Complex.QCInnerMarkedModulusDiagonal

/-!
# Geometric modulus distortion persists under locally uniform homeomorphic limits

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane*, second edition (1973),
Chapter I Theorem 5.2, p.29; Lemmas 4.3–4.4, pp.26–27; Rengel's inequality, pp.22–23.
The image domains may vary, and only a fixed eventual distortion bound is required.
-/

namespace HolomorphicAnosov

open Set Filter _root_.Topology Analysis.MarkedRectangle

theorem qc_modulus_limit_order
    {L m m' : ℝ} {μ ν : ℕ → ℝ}
    (hμ : Tendsto μ atTop (𝓝 m)) (hν : Tendsto ν atTop (𝓝 m'))
    (hBounds : ∀ j, ν j ≤ L * μ j) : m' ≤ L * m := by
  exact le_of_tendsto_of_tendsto hν (tendsto_const_nhds.mul hμ)
    (Eventually.of_forall hBounds)

/-- Locally uniform homeomorphic limits preserve the eventual geometric modulus bound.

Source: Lehto–Virtanen I.Theorem 5.2, p.29, with the inside-continuity and approximation
Lemmas 4.3–4.4, pp.26–27, Rengel's inequality, pp.22–23, and orientation I.§§1.5–1.6,
pp.9–10. The derivative hypothesis supplies positive orientation for the approximants.
The explicit winding condition supplies positive orientation for the limit.

The marked-modulus witnesses name the actual source and image moduli. The existing
marked rectangle theorem supplies such witnesses for positively marked Jordan regions;
no smoothness of the boundary or derivative of the limit is assumed.

Natural-language proof:

1. Use the geometric convention of Lehto–Virtanen I.§§2.3,3.1–3.2: a quadrilateral P is a bounded
   Jordan region with four distinct positively cyclic corner marks; the a-sides are the bottom/top
   pair and the b-sides the right/left pair. The registered marked rectangle theorem supplies a
   holomorphic bijection F:R_(a,b)→P and its same-map closed-rectangle extension with those side
   labels. Its modulus M(P)=a/b is positive and independent of the chosen model. Normalize by a
   positive similarity to R_M={0<x<M(P),0<y<1}. A positively marked homeomorphism carries those
   labels to its image quadrilateral. Cyclically moving the first corner changes the modulus to
   its reciprocal: rotating and rescaling a canonical rectangle gives the exchanged marked model,
   and model uniqueness gives M(P with exchanged side pairs)=1/M(P). Conformal changes preserve
   marked modulus by composing their actual same-map boundary extensions. In this proof a sense-
   preserving homeomorphism f on an open domain is geometrically K-quasiconformal when M(f(P))≤K
   M(P) for every such P with closure compactly contained in that domain. Applying the inequality
   to the cyclically relabeled P also gives M(f(P))≥M(P)/K. This definition is used only inside
   the proof; it does not replace the current analytic statement.
   Source: LV1973 I.§2.3–2.4 pp.14–15; I.§3.1–3.2 pp.16–17

2. Write out the Rengel estimate used by both closure and rigidity. For a bounded quadrilateral P let
   s_a(P) and s_b(P) be the infimal Euclidean lengths of locally regular interior arcs joining the
   a-sides and b-sides, respectively, with endpoints on those closed sides; a curve with infinite
   length causes no problem. Let H:R_M→P be the inverse canonical map with its same-map closure
   extension. The image-Jacobian formula and the complex derivative identity |det DH|=|Hprime|²
   give area(P)=∫_(R_M)|Hprime|². Tonelli makes the vertical energy finite for almost every
   u∈(0,M). On such a slice Holder gives square-integrable⇒IntegrableOn speed on (0,1). Extend the
   real speed by finite endpoint values 0 and use the registered open-interval/interval-
   integrability equivalence for Lebesgue measure to obtain IntervalIntegrable on [0,1], with no
   boundary derivative assumption. On this slice the vertical image arc has Euclidean length at
   most L(u)=∫_0^1|Hprime(u+iv)|dv, hence L(u)≥s_a(P); its endpoints are on the a-sides by the
   closure map. Explicitly, apply the registered norm-sub integral estimate to each segment of any
   finite partition on a compact interior subinterval and sum: every such polygonal chord sum is
   at most the speed integral there. Taking the supremum over partitions and then over compact
   interior subintervals gives full open-arc length at most L(u). This inequality suffices and
   requires no boundary derivative or additional converse arclength formula. Thus
   ∫_0^1|Hprime(u+iv)|²dv≥L(u)²≥s_a(P)². Integration gives M(P) s_a(P)²≤area(P). Apply the
   identical argument after exchanging marked side pairs to obtain s_b(P)²≤M(P) area(P). Whenever
   the displayed denominators are positive, this is s_b(P)²/area(P)≤M(P)≤area(P)/s_a(P)². Only the
   canonical analytic arcs are needed; the general extremal-length function classes in I.§4.2 are
   not assumed as extra input.
   Source: LV1973 I.§4.1–4.3 pp.20–23, especially Rengel’s inequality p.22 and its inverse-canonical-map calculation p.23

3. Follow I.Lemma4.3 to prove only the inside continuity needed here. Suppose P_j⊂P and every point
   of each marked side of P_j eventually has distance <ε from the corresponding side of P, for
   every ε>0. No nesting or reverse Hausdorff bound is required. Apply the canonical map of P,
   including its continuous closed-domain extension. Uniform continuity on the compact closure,
   applied as a globally continuous map on the closure SUBTYPE, sends the four labeled sides of
   the images S_j into strips of width ε along the corresponding sides of R_M. All S_j lie in R_M
   and have area at most M. For 0<ε<min(1/2,M/2), every a-side joining arc has length at least
   1−2ε, and every b-side joining arc at least M−2ε. The preceding Rengel inequalities imply
   (M−2ε)²/M≤M(S_j)≤M/(1−2ε)². Conformal invariance gives M(S_j)=M(P_j); letting ε↓0 proves
   M(P_j)→M(P). All regions in the application are bounded, so Euclidean and spherical side-
   distance convergence agree. This is the full written squeeze (4.15); the generalized theorem in
   I.§4.9 and its external Rado theorem are unnecessary.
   Source: LV1973 I.Lemma4.3 p.26, (4.14)–(4.15)

4. Follow I.Lemma4.4 using an actual closed-disk map, not extra data silently attached to the marked
   rectangle model. The Jordan-region theorem makes a quadrilateral P a bounded simply connected
   nonempty open region. Its bounded Riemann map supplies φ:D→P, and the same-map Caratheodory
   theorem extends precisely that φ to a homeomorphism Φ:closed D→closure P. Pull back the four
   corner marks to distinct positively cyclic ζ₁,…,ζ₄∈S¹. For j≥2 set r_j=1−1/j and
   P_j=φ({|z|<r_j}), with marked corners φ(r_j ζ_i) and the corresponding circular subarcs. Each
   closed smaller disk lies compactly inside D; injectivity, holomorphicity and nonzero derivative
   show its boundary image is analytic in the source’s sense. Its image closure lies compactly
   inside P. Uniform continuity of Φ on closed D gives sup_|ζ|=1 |φ(r_j ζ)−Φ(ζ)|→0. Thus every
   point of each labeled side of P_j is close to the corresponding side of P, so P_j→P from
   inside. This gives the exact source approximation, including the harmless exclusion of the
   degenerate r₁=0 term.
   Source: LV1973 I.Lemma4.4 p.27; boundary correspondence I.§2.2 p.14

5. Apply the written closure proof I.Theorem5.2 with the fixed L≥1 in the hypothesis. Choose N so
   that every n≥N satisfies the stated geometric L-modulus inequality; no K_n specialization is
   needed. Fix any quadrilateral P with closure compactly contained in U and choose its analytic
   inside approximations P_j from the previous step. For each fixed j, g(closure P_j) is compactly
   inside g(P). Its positive distance from the complement of g(P), together with uniform
   convergence on closure P, ensures g_n(closure P_j)⊂g(P) for all sufficiently large n. Choose a
   strictly increasing n_j≥max(N,j) with this containment and sup_(closure P)|g_nj−g|≤1/j. For any
   point z on a labeled side of P_j, choose q on the corresponding side of P with |z−q| tending
   uniformly to zero. Then |g_nj(z)−g(q)|≤1/j+|g(z)−g(q)|→0 by uniform continuity of g on closure
   P. Therefore g_nj(P_j) converges to g(P) FROM INSIDE, with the labels carried by the given
   orientation-preserving homeomorphisms. The inside continuity calculation gives M(P_j)→M(P) and
   M(g_nj(P_j))→M(g(P)). Pass to the limit in M(g_nj(P_j))≤L M(P_j) to get M(g(P))≤L M(P). Since P
   was arbitrary, g is geometrically L-quasiconformal. This is the source’s diagonal subsequence
   proof; it uses neither a common V_n nor convergence of derivatives or inverse derivatives. The
   positive invertible real derivative ensures each approximant preserves orientation, by the
   local linear homotopy: differentiability bounds the remainder on a small circle by less than
   the minimum linear stretch, so the straight homotopy is nonzero; the determinant sign gives
   winding +1. The orientation theorem I.§1.5 propagates this sign through the connected domain.
   The assumed winding condition supplies the limit’s positive orientation. All image
   quadrilaterals therefore have the transported positive markings.
   Source: LV1973 I.Theorem5.2 p.29; Lemmas4.3–4.4 pp.26–27
-/
theorem qc_geometric_modulus_limit
    (U : Set ℂ) (hU : IsOpen U) (hU_connected : IsConnected U)
    (gSeq : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (hSeq_source : ∀ n, (gSeq n).source = U) (hg_source : g.source = U)
    (hSeq_derivative : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (gSeq n) (A : ℂ →L[ℝ] ℂ) z ∧ 0 < (A : ℂ →L[ℝ] ℂ).det)
    (hLocallyUniform : TendstoLocallyUniformlyOn (fun n z ↦ gSeq n z) g atTop U)
    (hg_positive : ∀ a : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall a r ⊆ U →
      ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
          Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) = (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
        θ 1 = θ 0 + 2 * Real.pi)
    (L : ℝ) (_hL : 1 ≤ L)
    (hBound : ∀ᶠ n in atTop, ∀ (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ),
      IsCompact (closure Q) → closure Q ⊆ U →
      HasMarkedConformalModulus Q p m →
      HasMarkedConformalModulus (gSeq n '' Q) (fun i ↦ gSeq n (p i)) m' → m' ≤ L * m)
    (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ)
    (hQcompact : IsCompact (closure Q)) (hQinside : closure Q ⊆ U)
    (hQmod : HasMarkedConformalModulus Q p m)
    (hImageMod : HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m') : m' ≤ L * m := by
  -- The eventual distortion hypothesis is independent of the geometric construction.
  obtain ⟨N, hN⟩ := eventually_atTop.mp hBound
  -- LV I.Lemmas 4.3–4.4 and Theorem 5.2 supply inner marked quadrilaterals and
  -- a diagonal sequence after N whose source and image moduli converge.
  -- This is the remaining geometric obligation: positive side markings, both
  -- Rengel estimates, and orientation transport still have to be formalized.
  have hInnerModels := qc_inner_marked_modulus_diagonal U hU hU_connected gSeq g
    hSeq_source hg_source hSeq_derivative hLocallyUniform hg_positive Q p m m'
    hQcompact hQinside hQmod hImageMod N
  obtain ⟨φ, Qinner, pinner, μ, ν, _hφ, hinner, hμ, hν⟩ := hInnerModels
  have hBounds : ∀ j, ν j ≤ L * μ j := by
    intro j
    obtain ⟨hjN, hjcompact, hjinside, hjmod, hjimage⟩ := hinner j
    exact hN (φ j) hjN (Qinner j) (pinner j) (μ j) (ν j)
      hjcompact hjinside hjmod hjimage
  exact qc_modulus_limit_order hμ hν hBounds

end HolomorphicAnosov

