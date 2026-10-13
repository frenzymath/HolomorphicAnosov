import HolomorphicAnosov.Topology.WhyburnUnboundedComponentExterior
import HolomorphicAnosov.Topology.FrontierConnectedComponentIn
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Piecewise

/-!
# A simple arc does not separate the real plane

Source statement: Whyburn, *Topological Analysis* (1958), Chapter III (1.1),
printed pp.29–30. The proof here is an independent agent-written argument
using the exponential covering and Tietze extension.
-/

namespace HolomorphicAnosov

/-- The complement of every topologically embedded closed real unit interval
in the real plane is connected.

Source statement: Whyburn, *Topological Analysis*, III (1.1), pp.29–30.
The following independent proof is agent-written.

Let `K` be the compact range of the embedding, and identify the Euclidean
plane isometrically with `ℂ`. For any `x` outside `K`, lift the nonzero path
`e(t) - x` through the exponential covering. This gives a continuous logarithm
on the parameter interval. Since the embedding is closed, Tietze extension
extends this logarithm to a continuous complex function `L` on the plane.
Thus `exp L(z) = z - x` for every `z` in `K`.

Suppose the complementary component `R` through `x` is bounded. Its frontier
lies in `K`. Paste `exp L` on `R` with `z - x` on the complement of `R`.
The two formulas agree on the frontier, so the resulting function `f` is
continuous. It never vanishes: the first formula is an exponential, and
the only zero of the second would be `x`, which belongs to `R`.
The plane is contractible, so the exponential covering gives a global
continuous logarithm `g` of `f`.

Choose a circle centered at `x` with radius exceeding a bound for `R`.
Parametrize it by `p(t) = x + r exp(2πit)`. On the circle `f(p(t))` equals
`r exp(2πit)`. Uniqueness of covering lifts compares `g(p(t))` with
`g(p(0)) + 2πit`, giving equality for every `t` in `[0,1]`. But `p(0)=p(1)`,
whereas the two proposed logarithm endpoint values differ by `2πi ≠ 0`.
This contradiction shows every complementary component is unbounded.

An unbounded component of a compact plane set contains the exterior of a
large closed ball. Thus any two complementary components have a common point
outside sufficiently large balls. Equivalently, the connected union of the
two components contains the two prescribed points of the complement. The
complement is therefore preconnected. It is nonempty because `K` is compact
and the plane is not compact, proving the stated connectedness.

The argument uses only the given topological embedding; no polygonality,
smoothness, boundary accessibility or Jordan-curve premise is assumed.
-/
theorem simpleArc_compl_isConnected
    (e : ↥unitInterval → EuclideanSpace ℝ (Fin 2)) (he : Topology.IsEmbedding e) :
    IsConnected (Set.range e)ᶜ := by
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  let h : E ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let K := Set.range e
  have hcompact : IsCompact K := isCompact_range he.continuous
  have hclosed : IsClosed K := hcompact.isClosed
  have hnonempty : Kᶜ.Nonempty := Set.nonempty_compl.mpr hcompact.ne_univ
  have hlog (x : E) (hx : x ∉ K) :
      ∃ L : C(E, ℂ), ∀ z ∈ K, Complex.exp (L z) = h z - h x := by
    have hne (t : unitInterval) : h (e t) - h x ≠ 0 := by
      intro ht
      exact hx ⟨t, h.injective (sub_eq_zero.mp ht)⟩
    let f : C(unitInterval, {z : ℂ // z ≠ 0}) :=
      ⟨fun t ↦ ⟨h (e t) - h x, hne t⟩,
        ((h.continuous.comp he.continuous).sub continuous_const).subtype_mk _⟩
    obtain ⟨l, hl, _⟩ := Complex.isCoveringMap_exp.exists_path_lifts
      f (Complex.log (h (e 0) - h x)) (by
        apply Subtype.ext
        exact (Complex.exp_log (hne 0)).symm)
    obtain ⟨L, hL⟩ := l.exists_extension' (show Topology.IsClosedEmbedding e from ⟨he, hclosed⟩)
    refine ⟨L, ?_⟩
    rintro z ⟨t, rfl⟩
    rw [show L (e t) = l t from congrFun hL t]
    exact congrArg Subtype.val (congrFun hl t)
  have hunbounded (x : E) (hx : x ∉ K) :
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) := by
    intro hbdd
    let R := connectedComponentIn Kᶜ x
    have hxR : x ∈ R := mem_connectedComponentIn hx
    have hfront : frontier R ⊆ K := by
      simpa only [compl_compl] using
        frontier_connectedComponentIn_subset_compl hclosed.isOpen_compl x
    obtain ⟨L, hL⟩ := hlog x hx
    let f : E → ℂ := R.piecewise (fun z ↦ Complex.exp (L z)) (fun z ↦ h z - h x)
    have hf : Continuous f := Continuous.piecewise (fun z hz ↦ hL z (hfront hz))
      (Complex.continuous_exp.comp L.continuous) (h.continuous.sub continuous_const)
    have hf0 : ∀ z, f z ≠ 0 := by
      intro z
      by_cases hz : z ∈ R
      · simp [f, hz]
      · simp only [f, Set.piecewise_eq_of_notMem R _ _ hz]
        intro heq
        exact hz (h.injective (sub_eq_zero.mp heq) ▸ hxR)
    let f' : C(E, {z : ℂ // z ≠ 0}) := ⟨fun z ↦ ⟨f z, hf0 z⟩, hf.subtype_mk _⟩
    obtain ⟨g, hg, _⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
      f' x (L x) (by apply Subtype.ext; change Complex.exp (L x) = f x; simp [f, hxR])
    have hgf (z : E) : Complex.exp (g z) = f z :=
      congrArg Subtype.val (congrFun hg.2 z)
    obtain ⟨C, hC⟩ := hbdd.subset_closedBall x
    let r := max C 0 + 1
    have hr : 0 < r := by dsimp [r]; linarith [le_max_right C 0]
    have hCr : C < r := by dsimp [r]; linarith [le_max_left C 0]
    let τ : ℂ := 2 * Real.pi * Complex.I
    let p : unitInterval → E := fun t ↦ h.symm (h x + (r : ℂ) * Complex.exp (τ * (t : ℝ)))
    have hp : Continuous p := by fun_prop
    have hdist (t : unitInterval) : dist (p t) x = r := by
      rw [← h.dist_map]
      simp [p, dist_eq_norm, Complex.norm_exp, τ, abs_of_pos hr]
    have hpout (t : unitInterval) : p t ∉ R := by
      intro ht
      have ht' := hC ht
      change dist (p t) x ≤ C at ht'
      rw [hdist] at ht'
      exact (not_le_of_gt hCr) ht'
    have hgp (t : unitInterval) :
        Complex.exp (g (p t)) = (r : ℂ) * Complex.exp (τ * (t : ℝ)) := by
      rw [hgf]
      dsimp only [f]
      rw [Set.piecewise_eq_of_notMem R _ _ (hpout t)]
      simp [p]
    have hp01 : p 0 = p 1 := by simp [p, τ]
    let k : unitInterval → ℂ := fun t ↦ g (p 0) + τ * (t : ℝ)
    have hk : Continuous k := by fun_prop
    have hgk : (fun t ↦ g (p t)) = k := by
      refine Complex.isCoveringMap_exp.eq_of_comp_eq (g.continuous.comp hp) hk ?_ 0 ?_
      · funext t
        apply Subtype.ext
        change Complex.exp (g (p t)) = Complex.exp (k t)
        rw [hgp]
        dsimp [k]
        rw [Complex.exp_add, hgp 0]
        simp
      · simp [k]
    have hτ : τ = 0 := by
      have heq := congrFun hgk 1
      simp only [k, Set.Icc.coe_one, Complex.ofReal_one, mul_one] at heq
      rw [← hp01] at heq
      exact (add_eq_left.mp heq.symm)
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hτ
  refine ⟨hnonempty, isPreconnected_of_forall_pair ?_⟩
  intro x hx y hy
  let R := connectedComponentIn Kᶜ x
  let S := connectedComponentIn Kᶜ y
  have hxR : x ∈ R := mem_connectedComponentIn hx
  have hyS : y ∈ S := mem_connectedComponentIn hy
  obtain ⟨B, hB, _, hBR⟩ := unbounded_component_contains_exterior K R hcompact
    ⟨x, hxR⟩ (hunbounded x hx) ⟨x, hxR, rfl⟩ 0
  obtain ⟨C, hC, _, hCS⟩ := unbounded_component_contains_exterior K S hcompact
    ⟨y, hyS⟩ (hunbounded y hy) ⟨y, hyS, rfl⟩ 0
  obtain ⟨z, hz⟩ : (Metric.closedBall (0 : E) (max B C))ᶜ.Nonempty :=
    Set.nonempty_compl.mpr (isCompact_closedBall (0 : E) (max B C)).ne_univ
  have hzR : z ∈ R := hBR (fun hzB ↦ hz (Metric.closedBall_subset_closedBall (le_max_left _ _) hzB))
  have hzS : z ∈ S := hCS (fun hzC ↦ hz (Metric.closedBall_subset_closedBall (le_max_right _ _) hzC))
  refine ⟨R ∪ S, Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _),
    Or.inl hxR, Or.inr hyS, ?_⟩
  exact isPreconnected_connectedComponentIn.union z hzR hzS isPreconnected_connectedComponentIn


end HolomorphicAnosov
