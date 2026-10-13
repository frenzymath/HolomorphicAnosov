import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Closure of a complex subspace detected by bounded functionals

Source: Walter Rudin, *Real and Complex Analysis*, third edition (1987), Theorem 5.19,
printed page 107 (PDF page 120). Complex Hahn–Banach is Theorem 5.16, printed page 104,
proved in subsection 5.18, printed pages 106–107.

Mathlib's `Submodule` represents the complex linear subspace, `closure` is the norm-topological
closure, and `X →L[ℂ] ℂ` represents bounded complex-linear functionals. No additional building
notion is introduced.
-/

namespace HolomorphicAnosov

/--
A point lies in the closure of a complex linear subspace exactly when every bounded complex-linear
functional annihilating that subspace vanishes at the point. The normed space may be incomplete,
and the subspace need not be closed.

Source: Rudin, *Real and Complex Analysis*, third edition (1987), Theorem 5.19, printed page 107
(PDF page 120); Theorem 5.16, printed page 104, with its complex proof in subsection 5.18,
printed pages 106–107. Local source: `literature/Rudin-Real-and-Complex-Analysis-3rd-1987.pdf`.

Natural-language proof:

1. A bounded complex-linear Φ has |Φ(v)|≤C‖v‖ for some C≥0; by linearity |Φ(v)−Φ(w)|≤C‖v−w‖. This
directly gives continuity: for any ε>0 choose η=ε/(C+1), so ‖v−w‖<η implies |Φ(v)−Φ(w)|<ε.
Conversely every continuous linear functional is bounded: continuity at0 gives η>0 with |Φ(v)|<1 for
‖v‖<η; for v≠0 apply this to (η/(2‖v‖))v to get |Φ(v)|≤(2/η)‖v‖, and v=0 is immediate. Thus
StrongDual ℂ X encodes precisely the stated bounded functionals. The singleton{0} is closed in ℂ
(each nonzero z has a ball of radius|z|/2 missing0); its inverse image kerΦ is closed by the named
preimage leaf. If Φ vanishes on M, then M⊆kerΦ. The named closure-minimal leaf gives closure M⊆kerΦ,
so every x0∈closure M satisfies Φ(x0)=0. This is Rudin’s forward continuity argument; it does not
replace M by a closed-subspace hypothesis.

2. For the converse argue contrapositively, as Rudin does. Suppose x0∉closure M. By the metric
definition of closure, some open ball B(x0,r), r>0, misses M. Put δ=r/2>0. Then ‖m−x0‖≥r>δ for every
m∈M. In particular x0∉M. This uses distance from the original M, not an orthogonal complement,
nearest-point projection, completeness, or a minimum attained by m.

3. Let P=M+ℂx0={m+c x0:m∈M,c∈ℂ}, a complex-linear subspace: add two displayed decompositions and
multiply one by an arbitrary scalar. If m+c x0=n+d x0 and c≠d, then x0=(c−d)⁻¹(n−m)∈M, contrary to
x0∉M. Hence c=d and then m=n. Define φ0(m+c x0)=c using this unique decomposition. Addition and
complex homogeneity of these unique coefficients show φ0 is complex-linear. Its restriction to M is0
(take c=0), and φ0(x0)=1 (take m=0,c=1). This fills the representation check implicit in Rudin5.19,
without assuming P or M closed.

4. For v=m+c x0∈P, first handle c=0: |φ0(v)|=0≤δ⁻¹‖v‖. If c≠0, then −c⁻¹m∈M, so the preceding
distance estimate gives ‖x0+c⁻¹m‖>δ. Norm homogeneity overℂ yields ‖m+c x0‖=|c|‖x0+c⁻¹m‖≥δ|c|. Since
δ>0, |φ0(v)|=|c|≤δ⁻¹‖v‖. Thus φ0 is bounded on P with its norm induced from X; the same difference
estimate as in the first step makes it continuous, so φ0:P→L[ℂ]ℂ and ‖φ0‖≤δ⁻¹. This is exactly
Rudin’s displayed scalar-distance inequality, with the zero-scalar case made explicit. No global
Banach-space structure is used.

5. Apply mathlib.exists_extension_norm_eq with 𝕜=ℂ, E=X, p=P and f=φ0. It gives Φ:X→L[ℂ]ℂ agreeing
with φ0 on every point of P and with ‖Φ‖=‖φ0‖≤δ⁻¹. In particular Φ vanishes at every point of M and
Φ(x0)=1≠0. This contradicts the asserted vanishing of all bounded annihilating functionals whenever
x0 is outside closure M. Together with the forward direction this proves the exact equivalence. The
extension is valid on arbitrary P: the pinned theorem has no IsClosed P or CompleteSpace X premise.
Rudin’s underlying complex extension theorem is5.16, proved in subsection5.18 by real Hahn–Banach
and F(x)=U(x)−iU(ix); the chosen Mathlib theorem supplies precisely that lower conclusion rather
than an algebraic-only separator.

6. If x0=0 then x0∈M and every linear Φ satisfies Φ(0)=0, so the forward argument applies; the
converse never divides by‖x0‖. If M=X, or M is dense, every point is in closure M and the forward
argument forces each annihilating bounded functional to vanish on all X. If M={0}, the
contrapositive construction applies to each nonzero x0. The zero normed space is covered by the
forward direction alone. Infinite-dimensional, incomplete X and nonclosed M remain within the exact
hypotheses throughout; δ is chosen only under x0∉closure M and c⁻¹ only under c≠0.
-/
theorem rudin_bounded_functional_annihilator_closure
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (M : Submodule ℂ X) (x0 : X) :
    x0 ∈ closure (M : Set X) ↔
      ∀ Φ : X →L[ℂ] ℂ, (∀ m ∈ M, Φ m = 0) → Φ x0 = 0 := by
  constructor
  · intro hx Φ hΦ
    exact closure_minimal hΦ (isClosed_eq Φ.continuous continuous_const) hx
  · intro h
    by_contra hx
    let N := M.topologicalClosure
    have : IsClosed (N : Set X) := M.isClosed_topologicalClosure
    have hq : (Submodule.Quotient.mk x0 : X ⧸ N) ≠ 0 := by
      intro hq
      apply hx
      exact (Submodule.Quotient.mk_eq_zero N).mp hq
    obtain ⟨f, _, hf⟩ := exists_dual_vector ℂ
      (Submodule.Quotient.mk x0 : X ⧸ N) (norm_ne_zero_iff.mpr hq)
    have hfzero := h (f.comp N.mkQL) (by
      intro m hm
      change f (Submodule.Quotient.mk m : X ⧸ N) = 0
      rw [(Submodule.Quotient.mk_eq_zero N).mpr (M.le_topologicalClosure hm), map_zero])
    change f (Submodule.Quotient.mk x0 : X ⧸ N) = 0 at hfzero
    rw [hf] at hfzero
    exact (norm_ne_zero_iff.mpr hq) (by simpa using congrArg Complex.re hfzero)

end HolomorphicAnosov
