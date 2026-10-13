import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Ring

/-!
# Free complex affine actions are translation actions

Source: Étienne Ghys, *Holomorphic Anosov systems*, Invent. Math. 119 (1995),
proof of Theorem B, printed p. 598. The affine arithmetic and transfer of
commutativity and torsion-freeness follow the source proof recorded in DAG node
`topo.free_affine_action_translations`, using Mathlib v4.35.0-rc1, revision
c32e1ec0d1eb5237ba344eee50162f45d5b0fc76: `mul_div_cancel₀`,
`Complex.instIsAddTorsionFree`, `MonoidHom.commGroupOfInjective`, and
`Function.Injective.isMulTorsionFree`.
-/

namespace HolomorphicAnosov

universe u

/-- A free left action on the complex plane by affine maps has unit slopes and
embeds its original group into the **additive** complex group by its translation
coefficients. In particular the original group is abelian and torsion-free.

The hypotheses express the affine action directly, with no extra faithful-action
assumption or replacement of its slopes by units. The conclusion about `b` is
the additive homomorphism law, not a homomorphism to complex multiplication.

Natural-language proof (Ghys, printed p. 598, with the recorded field and group
arithmetic expanded):

1. Evaluate the identity action at zero to get `b(1) = 0`, and at one to get
   `a(1) = 1`, independently of freeness.
2. If `a(g) ≠ 1`, set `d = 1 - a(g) ≠ 0` and `z = b(g)/d`.
   Field cancellation gives `d*z = b(g)`, hence
   `a(g)*z + b(g) = z - d*z + b(g) = z`. Indexed freeness gives `g = 1`,
   contradicting the identity slope. Thus every slope is one.
3. Evaluate the composition law at zero. With unit slopes it becomes
   `b(g*h) = b(g) + b(h)`. Together with `b(1) = 0` this constructs the
   homomorphism `φ(g) = Multiplicative.ofAdd (b(g))` into the tagged additive
   complex group. Substituting `h = g⁻¹` gives `b(g⁻¹) = -b(g)`.
4. If `b(g) = b(h)`, then `b(g⁻¹*h) = 0`. The affine map indexed by
   `g⁻¹*h` fixes zero, so freeness forces `g⁻¹*h = 1`, and therefore `g = h`.
   Thus `b`, and also its type-tagged homomorphism `φ`, are injective.
5. The tagged additive complex group is commutative. Comparing `φ(g*h)` and
   `φ(h*g)` and using injectivity yields commutativity of the original group,
   exactly as in `MonoidHom.commGroupOfInjective`. The additive complex group
   has injective multiplication by every positive natural number; the
   multiplicative type tag identifies those maps with positive powers.
   `Function.Injective.isMulTorsionFree` transfers positive-power injectivity
   through `φ` to the original group. In particular any element of finite
   order is the identity. The trivial group is included; no discreteness,
   lattice, rank, topology, or geometric premise is asserted.

This is statement formalization only; the named theorem's proof is postponed.
-/
theorem freeAffineActionTranslations
    {G : Type u} [Group G] (a b : G → ℂ)
    (_ha : ∀ g : G, a g ≠ 0)
    (hidentity : ∀ z : ℂ, a 1 * z + b 1 = z)
    (hcomposition : ∀ (g h : G) (z : ℂ),
      a (g * h) * z + b (g * h) = a g * (a h * z + b h) + b g)
    (hfree : ∀ (g : G) (z : ℂ), a g * z + b g = z → g = 1) :
    (∀ g : G, a g = 1) ∧
      b 1 = 0 ∧
      (∀ g h : G, b (g * h) = b g + b h) ∧
      Function.Injective b ∧
      (∀ g h : G, g * h = h * g) ∧
      IsMulTorsionFree G := by
  have hb1 : b 1 = 0 := by simpa using hidentity 0
  have ha1 : a 1 = 1 := by simpa [hb1] using hidentity 1
  have slopes : ∀ g : G, a g = 1 := by
    intro g
    by_contra hg
    have hd : 1 - a g ≠ 0 := sub_ne_zero.mpr (Ne.symm hg)
    have hcancel := mul_div_cancel₀ (b g) hd
    have hfixed : a g * (b g / (1 - a g)) + b g = b g / (1 - a g) := by
      calc
        a g * (b g / (1 - a g)) + b g =
            b g / (1 - a g) - (1 - a g) * (b g / (1 - a g)) + b g := by ring
        _ = b g / (1 - a g) := by rw [hcancel]; ring
    have he : g = 1 := hfree g _ hfixed
    exact hg (he ▸ ha1)
  have hbmul : ∀ g h : G, b (g * h) = b g + b h := by
    intro g h
    simpa [slopes, add_comm] using hcomposition g h 0
  have hbinv : ∀ g : G, b g⁻¹ = -b g := by
    intro g
    have h := hbmul g g⁻¹
    simp only [mul_inv_cancel, hb1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hbinj : Function.Injective b := by
    intro g h he
    have hbzero : b (g⁻¹ * h) = 0 := by rw [hbmul, hbinv, he]; simp
    have hgh : g⁻¹ * h = 1 := hfree (g⁻¹ * h) 0 (by simp [hbzero])
    exact inv_mul_eq_one.mp hgh
  let phi : G →* Multiplicative ℂ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (b g)
      map_one' := by change b 1 = 0; exact hb1
      map_mul' := by intro g h; change b (g * h) = b g + b h; exact hbmul g h }
  have hphi : Function.Injective phi := by
    intro g h he
    exact hbinj (congrArg Multiplicative.toAdd he)
  have hcomm : ∀ g h : G, g * h = h * g := by
    let := phi.commGroupOfInjective hphi
    exact fun g h ↦ mul_comm g h
  exact ⟨slopes, hb1, hbmul, hbinj, hcomm, Function.Injective.isMulTorsionFree phi hphi⟩


end HolomorphicAnosov
