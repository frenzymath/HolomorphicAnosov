import HolomorphicAnosov.Linear.HyperbolicRealSplitting
import HolomorphicAnosov.Topology.FranksCompactCWCoverLifts
import HolomorphicAnosov.Topology.FranksSeriesCorrection
import HolomorphicAnosov.Topology.FranksWindingLemmas
import HolomorphicAnosov.Topology.FranksIntegralToralContinuousMap
import HolomorphicAnosov.Topology.FranksWindingAction
import HolomorphicAnosov.Topology.FranksMatrixAction
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Franks's pointed fundamental-group semiconjugacy theorem

Source: Franks, *Anosov Diffeomorphisms* (1970), pointed conventions p. 69 and
Proposition (2.1), pp. 70–71; definition of a Π₁ diffeomorphism, p. 62.
The complete original is `literature/Global analysis, part I.pdf` (PDF pp. 79–80).
This is the Stage 2 interface of `topo.franks_pi1_semiconjugacy`.
-/

namespace HolomorphicAnosov

open _root_.Topology

universe u v

/-- The exact pointed Π₁ semiconjugacy into a hyperbolic integral toral automorphism.

Source: Franks (1970), Proposition (2.1), pp. 70–71, with the pointed conventions of p. 69.
The torus is the genuine product of quotient circles ℝ/ℤ. The complex-cast matrix acts by
row-times-column, and the spectral premise excludes exactly modulus-one eigenvalues.
The induced maps use `FundamentalGroup.mapOfEq` with the actual basepoint equalities.

The unique map is unique among all pointed maps in the FREE homotopy class of `h0`, not only
among maps with a previously supplied based homotopy. The conclusion also supplies a homotopy
relative to `{b}`. There is no surjectivity or injectivity conclusion.

The lift conclusion applies to every pointed universal cover: a surjective covering from a
simply connected space, and every pointed continuous lift `H0` through the coordinate quotient.
It supplies a pointed lift `H` of the same `k` whose difference from `H0` is bounded and invariant
under every actual deck transformation. The supremum norm on the finite real coordinate space
is a canonical norm; boundedness agrees with Euclidean boundedness. No particular construction
of the universal cover, fundamental domain, deck-group presentation or lift is assumed.

Complete natural-language proof from the current DAG node:

1. Use the compact-CW covering theorem to obtain P:K̃→K, b̃, Γ=π1(K,b), its left deck action, the
pointed homeomorphism lift G, and the pointed φ-equivariant H0, where φ=(h0)_* in winding
coordinates. The torus winding theorem identifies (Abar)_* with A, so the assumed square reads
φ(g_*γ)=Aφ(γ). These data use only the topology of K; no smooth structure or Anosov hypothesis is
used.

2. Put e(x)=A⁻¹H0(Gx)−H0(x). Deck covariance and the square give
e(γx)=A⁻¹(H0(Gx)+φ(g_*γ))−H0(x)−φ(γ)=e(x). Also e(b̃)=0. The compact-CW cover theorem therefore
gives a bound ‖e(x)‖≤B with B≥0. Let Q be the space of bounded continuous Γ-invariant vector maps
vanishing at b̃; define L(v)=A⁻¹v∘G and L⁻¹(v)=Av∘G⁻¹. These operators preserve Q because G
conjugates the Γ action through the automorphism g_*. Composition with the surjective G leaves the
sup norm unchanged.

3. Use the spectral splitting to project e=e_s+e_u and Q=Q_s⊕Q_u. For values in E^u, ‖L^j v‖∞≤C_u
r_u^j‖v‖∞; for values in E^s, ‖L^(−j)v‖∞≤C_s r_s^j‖v‖∞. This corrects the stable/unstable labels
printed on Franks p.70: with the displayed L=A⁻¹(·)∘G, it is Q_u on which positive powers decay,
and Q_s on which negative powers decay. The printed labels are reversed, as direct substitution and
the visually inspected PDF confirm.

4. Define v_u=−Σ_(j≥0)L^j e_u and v_s=Σ_(j≥1)L^(−j)e_s. The spectral estimates bound each term
uniformly by a constant times r^j. Partial-sum increments thus satisfy the geometric Cauchy
estimate; finite-dimensional completeness and the Cauchy limit leaf give pointwise limits. The real
geometric-sum formula bounds every tail by C r^N/(1−r), uniformly in x, hence yields uniform
convergence and bounded limits. The uniform-limit-continuity leaf gives continuity on all of K̃.
Invariance and vanishing at b̃ pass to the pointwise limits. Consequently v=v_s+v_u lies in Q. This
proves the Banach-space convergence invoked without expansion at Franks p.70, without assuming
completeness of Q as a new premise.

5. For unstable partial sums U_N=−Σ_(0≤j<N)L^j e_u, (L−I)U_N=e_u−L^N e_u. For stable partial sums
S_N=Σ_(1≤j≤N)L^(−j)e_s, (L−I)S_N=e_s−L^(−N)e_s. The remainders converge uniformly to0 by the
respective decay estimates. Applying the fixed linear operator A⁻¹ and the fixed homeomorphism G to
the uniformly convergent sums commutes with the limit, since ‖A⁻¹(w_N−w)∘G‖∞≤‖A⁻¹‖‖w_N−w‖∞.
Therefore (L−I)v=e. This gives both signs and index ranges explicitly.

6. Set H=H0−v. The equation gives A⁻¹H(Gx)−H(x)=0, so HG=AH. Deck invariance of v gives
H(γx)=H(x)+φ(γ), and H(b̃)=0. The map p∘H is constant on P-fibres, hence descends continuously to k
by quotient descent, with k(b)=0 and kg=Abar k. For t∈[0,1], H_t=H0−t v has the same φ-equivariance
and is jointly continuous. In a covering chart of P choose a continuous section s; the descended
homotopy there is (t,z)↦p(H_t(s(z))), so it is jointly continuous. These local formulas agree on
overlaps by equivariance and fix b for every t. They give the required homotopy relative to b. The
bound on v is exactly the claimed bounded deck-invariant difference H0−H.

7. If k′ is another pointed continuous map homotopic to h0 with k′g=Abar k′, lift a homotopy h0~k′
after precomposition with P, starting at H0, using covering homotopy lifting. Deck equivariance
persists by uniqueness of lifted homotopies; if the basepoint traces a loop, the endpoint lift
differs at b̃ by an integer vector, so subtract that constant vector to obtain the pointed lift H′.
Since translations commute and the torus fundamental group is abelian, this adjustment preserves
the φ-equivariance. The pointed maps H′G and AH′ cover the same map and agree at b̃, hence are
equal by unique map lifting. H′−H is deck invariant and bounded by compact descent. For every j∈Z,
(H′−H)(G^j x)=A^j(H′−H)(x). Its entire A-orbit is bounded, so the spectral bounded-orbit conclusion
forces H′−H=0 for every x, and then k′=k.

8. When n=0 the target torus and vector space are singletons, all series are zero and uniqueness is
immediate. If K is a point and n>0, the sole pointed map is constant0, so the general theorem
cannot assert surjectivity. This edge case explains why onto is a separate conclusion in the
standard-torus specialization.
-/
theorem franks_pi1_semiconjugacy
    (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1)
    {K : Type u} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [ConnectedSpace K] [CWComplex (Set.univ : Set K)]
    (b : K) (g : K ≃ₜ K) (hg : g b = b)
    (h0 : C(K, UnitAddTorus (Fin n))) (hh0 : h0 b = 0)
    (hπ : (FundamentalGroup.mapOfEq h0 hh0).comp
        (FundamentalGroup.mapOfEq (⟨g, g.continuous⟩ : C(K, K)) hg) =
      (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap A)
        (by classical ext i; simp [franksIntegralToralContinuousMap, ContinuousMap.pi])).comp
        (FundamentalGroup.mapOfEq h0 hh0)) :
    ∃ k : C(K, UnitAddTorus (Fin n)),
      k b = 0 ∧
      k.Homotopic h0 ∧
      (∀ x : K, k (g x) = integralToralMap A (k x)) ∧
      (∀ k' : C(K, UnitAddTorus (Fin n)),
        k' b = 0 → k'.Homotopic h0 →
        (∀ x : K, k' (g x) = integralToralMap A (k' x)) → k' = k) ∧
      k.HomotopicRel h0 {b} ∧
      ∀ (E : Type v) [TopologicalSpace E] [SimplyConnectedSpace E]
        (P : C(E, K)), IsCoveringMap P → Function.Surjective P →
        ∀ (e0 : E), P e0 = b →
        ∀ (H0 : C(E, Fin n → ℝ)), H0 e0 = 0 →
          (∀ x : E, (fun i : Fin n ↦ (H0 x i : UnitAddCircle)) = h0 (P x)) →
          ∃ H : C(E, Fin n → ℝ),
            H e0 = 0 ∧
            (∀ x : E, (fun i : Fin n ↦ (H x i : UnitAddCircle)) = k (P x)) ∧
            (∃ B : ℝ, 0 ≤ B ∧ ∀ x : E, ‖H0 x - H x‖ ≤ B) ∧
            ∀ (d : deck (P : E → K)) (x : E),
              H0 (d • x) - H (d • x) = H0 x - H x := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨h0, hh0, ContinuousMap.Homotopic.refl h0, ?_, ?_,
      ContinuousMap.HomotopicRel.refl h0, ?_⟩
    · intro x
      exact Subsingleton.elim _ _
    · intro k' _ _ _
      exact Subsingleton.elim _ _
    · intro E _ _ P _ _ e0 _ H0 hzero hlift
      refine ⟨H0, hzero, hlift, ⟨0, le_rfl, ?_⟩, ?_⟩
      · intro x
        simp
      · intro d x
        simp
  · have hsplitting := hyperbolic_real_splitting n (FranksMatrix.realAction A)
      (FranksMatrix.complexification_hyperbolic A hA)
    obtain ⟨covT, zeroT, hzT, w, hw, E, tE, hcover⟩ :=
      Topology.FranksCompactCWCoverLifts.compact_cw_cover_lifts K b g hg n h0 hh0
    let _ : TopologicalSpace E := tE
    obtain ⟨P, btilde, hb, cov, hsimp, hlocal, hsurj, δ, φ, G, H0,
      hδpoint, hfibres, hfree, hφ, hGb, hPG, hGδ, hH0b, hH0lift, hH0δ, hdescent⟩ := hcover
    have hatorus : franksIntegralToralContinuousMap A 0 = 0 := by
      classical
      ext i
      simp [franksIntegralToralContinuousMap, ContinuousMap.pi]
    have hφsquare : ∀ γ : (FundamentalGroup K b)ᵐᵒᵖ,
        (φ (MulOpposite.op (FundamentalGroup.mapOfEq ⟨g, g.continuous⟩ hg γ.unop))).toAdd =
          Matrix.mulVec (A : Matrix (Fin n) (Fin n) ℤ) (φ γ).toAdd := by
      intro γ
      rw [hφ, hφ]
      simp only [MulOpposite.unop_op]
      have hπγ := DFunLike.congr_fun hπ γ.unop
      change FundamentalGroup.mapOfEq h0 hh0
        (FundamentalGroup.mapOfEq ⟨g, g.continuous⟩ hg γ.unop) =
          FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap A) hatorus
            (FundamentalGroup.mapOfEq h0 hh0 γ.unop) at hπγ
      rw [hπγ]
      exact winding_matrix_action covT zeroT hzT w hw A hatorus _
    let AR := (FranksMatrix.realAction A).toContinuousLinearEquiv
    let e : C(E, Fin n → ℝ) :=
      ⟨fun x ↦ AR.symm (H0 (G x)) - H0 x,
        (AR.symm.continuous.comp (H0.continuous.comp G.continuous)).sub H0.continuous⟩
    have hezero : e btilde = 0 := by
      change AR.symm (H0 (G btilde)) - H0 btilde = 0
      rw [hGb, hH0b]
      simp
    have heinvariant : ∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) x,
        e (δ γ • x) = e x := by
      intro γ x
      change AR.symm (H0 (G (δ γ • x))) - H0 (δ γ • x) =
        AR.symm (H0 (G x)) - H0 x
      rw [hGδ, hH0δ, hH0δ, hφsquare]
      have hcast := FranksMatrix.realAction_intCast A (φ γ).toAdd
      change AR (fun i ↦ ((φ γ).toAdd i : ℝ)) = _ at hcast
      rw [← hcast, map_add, AR.symm_apply_apply]
      abel
    obtain ⟨ebar, heb, hebunique⟩ := (hdescent e heinvariant).1
    obtain ⟨B, hB, hebound⟩ := (hdescent e heinvariant).2
    obtain ⟨Es, Eu, Ps, Pu, Cs, Cu, rs, ru, hcompl, hAs, hAu, hAis, hAiu,
      hrPs, hrPu, hPs2, hPu2, hsum, hPsA, hPuA, hCs, hCu,
      hrs, hrs1, hru, hru1, hSbound, hUbound, hboundedOrbit⟩ := hsplitting
    have hpow : ∀ j x, (AR ^ j) x = (FranksMatrix.realAction A ^ j) x := by
      intro j
      induction j with
      | zero => intro x; rfl
      | succ j ih => intro x; rw [pow_succ', pow_succ']; exact congrArg AR (ih x)
    have hipow : ∀ j x, (AR.symm ^ j) x = ((FranksMatrix.realAction A).symm ^ j) x := by
      intro j
      induction j with
      | zero => intro x; rfl
      | succ j ih => intro x; rw [pow_succ', pow_succ']; exact congrArg AR.symm (ih x)
    let fs : ℕ → E → Fin n → ℝ := fun j x ↦ (AR ^ j) (Ps (e ((G.symm ^ j) x)))
    let fu : ℕ → E → Fin n → ℝ := fun j x ↦ (AR.symm ^ j) (Pu (e ((G ^ j) x)))
    have hfscont : ∀ j, Continuous (fs j) := fun j ↦
      (AR ^ j).continuous.comp (Ps.continuous.comp
        (e.continuous.comp (G.symm ^ j).continuous))
    have hfucont : ∀ j, Continuous (fu j) := fun j ↦
      (AR.symm ^ j).continuous.comp (Pu.continuous.comp
        (e.continuous.comp (G ^ j).continuous))
    have hfsbound : ∀ j x, ‖fs j x‖ ≤ (Cs * ‖Ps‖ * B) * rs ^ j := by
      intro j x
      have hmem : Ps (e ((G.symm ^ j) x)) ∈ Es := by
        rw [← hrPs]; exact ⟨_, rfl⟩
      change ‖(AR ^ j) _‖ ≤ _
      rw [hpow]
      apply (hSbound j _ hmem).trans
      have hnorm := (Ps.le_opNorm (e ((G.symm ^ j) x))).trans
        (mul_le_mul_of_nonneg_left (hebound _) (norm_nonneg Ps))
      calc
        Cs * rs ^ j * ‖Ps (e ((G.symm ^ j) x))‖ ≤ Cs * rs ^ j * (‖Ps‖ * B) :=
          mul_le_mul_of_nonneg_left hnorm (mul_nonneg (le_trans zero_le_one hCs) (pow_nonneg hrs.le _))
        _ = _ := by ring
    have hfubound : ∀ j x, ‖fu j x‖ ≤ (Cu * ‖Pu‖ * B) * ru ^ j := by
      intro j x
      have hmem : Pu (e ((G ^ j) x)) ∈ Eu := by
        rw [← hrPu]; exact ⟨_, rfl⟩
      change ‖(AR.symm ^ j) _‖ ≤ _
      rw [hipow]
      apply (hUbound j _ hmem).trans
      have hnorm := (Pu.le_opNorm (e ((G ^ j) x))).trans
        (mul_le_mul_of_nonneg_left (hebound _) (norm_nonneg Pu))
      calc
        Cu * ru ^ j * ‖Pu (e ((G ^ j) x))‖ ≤ Cu * ru ^ j * (‖Pu‖ * B) :=
          mul_le_mul_of_nonneg_left hnorm (mul_nonneg (le_trans zero_le_one hCu) (pow_nonneg hru.le _))
        _ = _ := by ring
    have hfsstep : ∀ j x, AR.symm (fs (j + 1) (G x)) = fs j x := by
      intro j x
      dsimp [fs]
      rw [pow_succ (G.symm), pow_succ' AR]
      change AR.symm (AR ((AR ^ j) (Ps (e ((G.symm ^ j) (G.symm (G x))))))) = _
      rw [G.symm_apply_apply, AR.symm_apply_apply]
    have hfustep : ∀ j x, AR.symm (fu j (G x)) = fu (j + 1) x := by
      intro j x
      dsimp [fu]
      rw [pow_succ G, pow_succ' AR.symm]
      rfl
    have hGpowb : ∀ j, (G ^ j) btilde = btilde := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ']; change G ((G ^ j) btilde) = btilde; rw [ih, hGb]
    have hGipowb : ∀ j, (G.symm ^ j) btilde = btilde := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
          rw [pow_succ']
          change G.symm ((G.symm ^ j) btilde) = btilde
          rw [ih]
          exact G.injective (by rw [G.apply_symm_apply, hGb])
    obtain ⟨v, hvzero, hveq, hvbound, hvformula⟩ := FranksSeries.correction_from_geometric_terms
      AR.symm.toContinuousLinearMap G fs fu (Cs * ‖Ps‖ * B) (Cu * ‖Pu‖ * B) rs ru
      (by positivity) (by positivity) hrs.le hrs1 hru.le hru1 hfscont hfucont
      hfsbound hfubound hfsstep hfustep btilde
      (fun j ↦ by simp [fs, hGipowb, hezero])
      (fun j ↦ by simp [fu, hGpowb, hezero])
    have hvresolvent : ∀ x, AR.symm (v (G x)) - v x = e x := by
      intro x
      calc
        AR.symm (v (G x)) - v x = fs 0 x + fu 0 x := hveq x
        _ = e x := by
          change Ps (e x) + Pu (e x) = e x
          exact DFunLike.congr_fun hsum (e x)
    have he_fibre : ∀ x y, P x = P y → e x = e y := by
      intro x y hxy
      obtain ⟨γ, hγ⟩ := (hfibres x y).mp hxy
      rw [← hγ, heinvariant]
    have hG_fibre : ∀ x y, P x = P y → P (G x) = P (G y) := by
      intro x y hxy
      rw [hPG, hPG, hxy]
    have hGi_fibre : ∀ x y, P x = P y → P (G.symm x) = P (G.symm y) := by
      intro x y hxy
      apply g.injective
      rw [← hPG, ← hPG, G.apply_symm_apply, G.apply_symm_apply, hxy]
    have hGp_fibre : ∀ j x y, P x = P y → P ((G ^ j) x) = P ((G ^ j) y) := by
      intro j
      induction j with
      | zero => intro x y h; exact h
      | succ j ih =>
          intro x y h
          rw [pow_succ']
          exact hG_fibre _ _ (ih x y h)
    have hGip_fibre : ∀ j x y, P x = P y → P ((G.symm ^ j) x) = P ((G.symm ^ j) y) := by
      intro j
      induction j with
      | zero => intro x y h; exact h
      | succ j ih =>
          intro x y h
          rw [pow_succ']
          exact hGi_fibre _ _ (ih x y h)
    have hv_fibre : ∀ x y, P x = P y → v x = v y := by
      intro x y hxy
      rw [hvformula, hvformula]
      have hfs : ∀ j, fs j x = fs j y := fun j ↦ congrArg (fun w ↦ (AR ^ j) (Ps w))
        (he_fibre _ _ (hGip_fibre j x y hxy))
      have hfu : ∀ j, fu j x = fu j y := fun j ↦ congrArg (fun w ↦ (AR.symm ^ j) (Pu w))
        (he_fibre _ _ (hGp_fibre j x y hxy))
      simp_rw [hfs, hfu]
    have hvinvariant : ∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) x, v (δ γ • x) = v x := by
      intro γ x
      apply hv_fibre
      exact ((hfibres x (δ γ • x)).mpr ⟨γ, rfl⟩).symm
    obtain ⟨vbar, hvbar, hvbar_unique⟩ := (hdescent v hvinvariant).1
    let H : C(E, Fin n → ℝ) := H0 - v
    have hHzero : H btilde = 0 := by change H0 btilde - v btilde = 0; rw [hH0b, hvzero]; simp
    have hHequiv : ∀ x, H (G x) = AR (H x) := by
      intro x
      apply AR.symm.injective
      rw [AR.symm_apply_apply]
      change AR.symm (H0 (G x) - v (G x)) = H0 x - v x
      rw [map_sub]
      have hh := hvresolvent x
      change AR.symm (v (G x)) - v x = AR.symm (H0 (G x)) - H0 x at hh
      linear_combination -hh
    have hvbarzero : vbar b = 0 := by rw [← hb, hvbar, hvzero]
    let q : C(Fin n → ℝ, UnitAddTorus (Fin n)) :=
      ⟨fun x i ↦ (x i : UnitAddCircle), covT.continuous⟩
    let k : C(K, UnitAddTorus (Fin n)) := h0 - q.comp vbar
    have hkP : ∀ x, k (P x) = q (H x) := by
      intro x
      change h0 (P x) - q (vbar (P x)) = q (H0 x - v x)
      rw [hvbar, ← hH0lift]
      ext i
      exact (map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _).symm
    have hkzero : k b = 0 := by
      change h0 b - q (vbar b) = 0
      rw [hh0, hvbarzero]
      simp [q]
      rfl
    have hqA : ∀ x, q (AR x) = integralToralMap A (q x) := by
      intro x
      ext i
      change ((FranksMatrix.realAction A x i : ℝ) : UnitAddCircle) = _
      rw [FranksMatrix.realAction_apply]
      simp [integralToralMap, q, ← zsmul_eq_mul]
    have hkequiv : ∀ x, k (g x) = integralToralMap A (k x) := by
      intro y
      obtain ⟨x, rfl⟩ := hsurj y
      rw [← hPG, hkP, hkP, hHequiv, hqA]
    let hom : h0.HomotopyRel k {b} :=
      { toContinuousMap :=
          ⟨fun tx ↦ h0 tx.2 - q ((tx.1 : ℝ) • vbar tx.2),
            (h0.continuous.comp continuous_snd).sub
              (q.continuous.comp ((continuous_subtype_val.comp continuous_fst).smul
                (vbar.continuous.comp continuous_snd)))⟩
        map_zero_left := by intro x; simp [q]; rfl
        map_one_left := by intro x; simp [k]
        prop' := by
          intro t x hx
          have hxb : x = b := Set.mem_singleton_iff.mp hx
          subst x
          simp [hvbarzero, q]
          rfl }
    refine ⟨k, hkzero, ?_, hkequiv, ?_, ?_, ?_⟩
    · exact ⟨hom.symm.toHomotopy⟩
    · intro k' hk'zero hk'hom hk'equiv
      obtain ⟨hom'⟩ := hk'hom.trans ⟨hom.toHomotopy⟩
      let differenceHom : C(unitInterval × K, UnitAddTorus (Fin n)) :=
        ⟨fun tx ↦ hom'.symm tx - k tx.2,
          hom'.symm.continuous.sub (k.continuous.comp continuous_snd)⟩
      have hdifferenceZero : ∀ x, differenceHom (0, x) = q ((0 : C(K, Fin n → ℝ)) x) := by
        intro x
        change hom'.symm (0, x) - k x = q 0
        have hz := hom'.symm.map_zero_left x
        change hom'.symm (0, x) = k x at hz
        rw [hz]
        simp [q]
        rfl
      let lifted := covT.liftHomotopy differenceHom (0 : C(K, Fin n → ℝ)) hdifferenceZero
      let u0 : C(K, Fin n → ℝ) :=
        ⟨fun x ↦ lifted (1, x), lifted.continuous.comp (continuous_const.prodMk continuous_id)⟩
      have hu0lift : ∀ x, q (u0 x) = k' x - k x := by
        intro x
        have hh := congrFun (covT.liftHomotopy_lifts differenceHom
          (0 : C(K, Fin n → ℝ)) hdifferenceZero) (1, x)
        change q (u0 x) = hom'.symm (1, x) - k x at hh
        have ho := hom'.symm.map_one_left x
        change hom'.symm (1, x) = k' x at ho
        rwa [ho] at hh
      let u : C(K, Fin n → ℝ) := u0 - ContinuousMap.const K (u0 b)
      have huzero : u b = 0 := by change u0 b - u0 b = 0; exact sub_self _
      have hulift : ∀ x, q (u x) = k' x - k x := by
        intro x
        change q (u0 x - u0 b) = _
        have hbq : q (u0 b) = 0 := by rw [hu0lift, hk'zero, hkzero, sub_self]
        have hsub : q (u0 x - u0 b) = q (u0 x) - q (u0 b) := by
          ext i
          exact map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
        rw [hsub, hbq, sub_zero, hu0lift]
      have huequiv : ∀ x, u (g x) = AR (u x) := by
        have hh : (fun x ↦ u (g x)) = (fun x ↦ AR (u x)) := covT.eq_of_comp_eq
          (u.continuous.comp g.continuous) (AR.continuous.comp u.continuous)
          (by
            funext x
            change q (u (g x)) = q (AR (u x))
            rw [hulift, hk'equiv, hkequiv, hqA, hulift]
            ext i
            simp [integralToralMap, smul_sub, Finset.sum_sub_distrib]) b
          (by rw [hg, huzero]; simp)
        exact congrFun hh
      obtain ⟨Bu, hBu, hubound⟩ := (hdescent (u.comp P)
        (fun γ x ↦ congrArg u (((hfibres x (δ γ • x)).mpr ⟨γ, rfl⟩).symm))).2
      have hub : ∀ x, ‖u x‖ ≤ Bu := by
        intro x
        obtain ⟨y, rfl⟩ := hsurj x
        exact hubound y
      have hup : ∀ j x, u ((g ^ j) x) = (AR ^ j) (u x) := by
        intro j
        induction j with
        | zero => intro x; rfl
        | succ j ih =>
            intro x
            rw [pow_succ', pow_succ']
            change u (g ((g ^ j) x)) = AR ((AR ^ j) (u x))
            rw [huequiv, ih]
      have hui : ∀ x, u (g.symm x) = AR.symm (u x) := by
        intro x
        apply AR.injective
        rw [AR.apply_symm_apply, ← huequiv, g.apply_symm_apply]
      have huip : ∀ j x, u ((g.symm ^ j) x) = (AR.symm ^ j) (u x) := by
        intro j
        induction j with
        | zero => intro x; rfl
        | succ j ih =>
            intro x
            rw [pow_succ', pow_succ']
            change u (g.symm ((g.symm ^ j) x)) = AR.symm ((AR.symm ^ j) (u x))
            rw [hui, ih]
      have huxzero : ∀ x, u x = 0 := by
        intro x
        have hbound : ∀ k : ℤ, ‖(FranksMatrix.realAction A ^ k) (u x)‖ ≤ Bu := by
          intro z
          cases z with
          | ofNat j =>
              change ‖(FranksMatrix.realAction A ^ (j : ℤ)) (u x)‖ ≤ Bu
              rw [zpow_natCast, ← hpow, ← hup]
              exact hub _
          | negSucc j =>
              rw [zpow_negSucc, ← inv_pow]
              change ‖((FranksMatrix.realAction A).symm ^ (j + 1)) (u x)‖ ≤ Bu
              rw [← hipow, ← huip]
              exact hub _
        simpa using hboundedOrbit (u x) ⟨Bu, hbound⟩ 0
      apply ContinuousMap.ext
      intro x
      have hh := hulift x
      rw [huxzero] at hh
      have hqzero : q 0 = 0 := by ext i; rfl
      rw [hqzero] at hh
      exact sub_eq_zero.mp hh.symm
    · exact ⟨hom.symm⟩
    · intro E' tE' hsimp' P' hcov' hsurj' e0 he0 H0' hH0'zero hH0'lift
      let H' : C(E', Fin n → ℝ) := H0' - vbar.comp P'
      refine ⟨H', ?_, ?_, ?_, ?_⟩
      · change H0' e0 - vbar (P' e0) = 0
        rw [hH0'zero, he0, hvbarzero]; simp
      · intro x
        change q (H0' x - vbar (P' x)) = h0 (P' x) - q (vbar (P' x))
        rw [← hH0'lift]
        ext i
        exact map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
      · refine ⟨Cs * ‖Ps‖ * B * (1 - rs)⁻¹ + Cu * ‖Pu‖ * B * (1 - ru)⁻¹,
          by positivity, fun x ↦ ?_⟩
        obtain ⟨y, hy⟩ := hsurj (P' x)
        change ‖H0' x - (H0' x - vbar (P' x))‖ ≤ _
        rw [sub_sub_cancel, ← hy, hvbar]
        exact hvbound y
      · intro d x
        change H0' (d • x) - (H0' (d • x) - vbar (P' (d • x))) =
          H0' x - (H0' x - vbar (P' x))
        simp only [sub_sub_cancel]
        congr 1
        exact deck.proj_smul d x

end HolomorphicAnosov
