
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.LongExact
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Stabilization of actual first cohomology along a short exact chain

Intended upstream module:
`Aglib.AlgebraicGeometry.Cohomology.Exact.Stabilization`.

For actual short exact sequences `M n ⟶ M (n + 1) ⟶ Q n` on a scheme over
a field, vanishing of the actual `H¹(Q n)` makes the original `H¹` coefficient
maps surjective. Finite dimension of `H¹(M 0)` then implies eventual equality
of adjacent dimensions and hence injectivity of those same maps. Native
connecting exactness gives eventual surjectivity of `H⁰(M (n + 1)) ⟶ H⁰(Q n)`.
Naturality of `moduleH0Equiv` transfers this to the literal map on global
sections, `(g n).val.app (op ⊤)`.

Only initial finite dimension and quotient `H¹` vanishing are assumed. No
properness, coherence, or vanishing of the `H¹(M n)` is required. The current
consumer is the cohomological lifting step in the proper integral curve
projectivity construction; its geometric hypotheses supply these cohomology
premises separately.

The native exactness and degree-zero comparison APIs are from Aglib revision
`197ca0728db3cdf1552a6bcefeeda901e3377862`.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Exact.Stabilization` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`66439f76f125c523a825ebdb48a2650bd9de52255f3bfb3f2149392e192680ad`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {K : Type u} [Field K] (X : FScheme K)

/-- Vanishing of quotient `H¹` makes the original preceding `H¹` map surjective. -/
theorem moduleH1Map_surjective_of_shortExact
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Subsingleton (moduleCohomology K X S.X₃ 1)] :
    Function.Surjective (moduleCohomologyMap X S.f 1) := by
  apply (LinearMap.surjective_iff_eq_zero_of_exact
    (moduleCohomologyMap_exact X S hS 1)).2
  exact Subsingleton.elim _ _

/-- Injectivity of the original `H¹` map kills the connecting map and gives
surjectivity of the original `H⁰` quotient map. -/
theorem moduleH0Map_surjective_of_shortExact_of_injective_h1
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    (hf : Function.Injective (moduleCohomologyMap X S.f 1)) :
    Function.Surjective (moduleCohomologyMap X S.g 0) := by
  apply (LinearMap.surjective_iff_eq_zero_of_exact
    (moduleCohomologyConnecting_exact_left X S hS 0)).2
  exact (LinearMap.injective_iff_eq_zero_of_exact
    (moduleCohomologyConnecting_exact_right X S hS 0)).1 hf

/-- The native `H⁰` comparison transfers surjectivity to the literal coefficient
map on global sections. -/
theorem moduleGlobalSectionsMap_surjective_of_moduleH0Map
    {M N : X.left.Modules} (φ : M ⟶ N)
    (hφ : Function.Surjective (moduleCohomologyMap X φ 0)) :
    Function.Surjective (φ.val.app (op ⊤)) := by
  intro y
  obtain ⟨x, hx⟩ := hφ ((moduleH0Equiv X N).symm y)
  refine ⟨moduleH0Equiv X M x, ?_⟩
  have hn := Sheaf.H.equiv₀_naturality isTerminalTop (coefficientSheafMap X φ) x
  change φ.val.app (op ⊤) (moduleH0Equiv X M x) =
    moduleH0Equiv X N (moduleCohomologyMap X φ 0 x) at hn
  rw [hn, hx, LinearEquiv.apply_symm_apply]

/-- In an actual short exact chain, finite-dimensional initial `H¹` and
vanishing quotient `H¹` give eventual surjectivity on both actual `H⁰` and
the original global-section maps. -/
theorem eventually_surjective_moduleH0Map_of_h1_chain
    (M Q : ℕ → X.left.Modules)
    (f : ∀ n, M n ⟶ M (n + 1)) (g : ∀ n, M (n + 1) ⟶ Q n)
    (w : ∀ n, f n ≫ g n = 0)
    (hS : ∀ n, (ShortComplex.mk (f n) (g n) (w n)).ShortExact)
    [FiniteDimensional K (moduleCohomology K X (M 0) 1)]
    (hQ : ∀ n, Subsingleton (moduleCohomology K X (Q n) 1)) :
    ∃ N, ∀ n ≥ N,
      Function.Surjective (moduleCohomologyMap X (g n) 0) ∧
      Function.Surjective ((g n).val.app (op ⊤)) := by
  classical
  have hsurj (n : ℕ) : Function.Surjective (moduleCohomologyMap X (f n) 1) := by
    let := hQ n
    exact moduleH1Map_surjective_of_shortExact X
      (ShortComplex.mk (f n) (g n) (w n)) (hS n)
  have hfinite (n : ℕ) : FiniteDimensional K (moduleCohomology K X (M n) 1) := by
    induction n with
    | zero => infer_instance
    | succ n ih =>
      let := ih
      exact Module.Finite.of_surjective (moduleCohomologyMap X (f n) 1) (hsurj n)
  let := hfinite
  let d : ℕ → ℕ := fun n => Module.finrank K (moduleCohomology K X (M n) 1)
  have hstep (n : ℕ) : d (n + 1) ≤ d n :=
    LinearMap.finrank_le_finrank_of_surjective (hsurj n)
  have hanti : Antitone d := antitone_nat_of_succ_le hstep
  have hex : ∃ a, ∃ n, d n = a := ⟨d 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  have hmin (n : ℕ) : d N ≤ d n := by
    rw [hN]
    exact Nat.find_min' hex ⟨n, rfl⟩
  have hstable (n : ℕ) (hn : N ≤ n) : d n = d N :=
    le_antisymm (hanti hn) (hmin n)
  refine ⟨N, fun n hn => ?_⟩
  have hdim : d n = d (n + 1) :=
    (hstable n hn).trans (hstable (n + 1) (hn.trans (Nat.le_succ n))).symm
  have hinj : Function.Injective (moduleCohomologyMap X (f n) 1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 (hsurj n)
  have hg := moduleH0Map_surjective_of_shortExact_of_injective_h1 X
    (ShortComplex.mk (f n) (g n) (w n)) (hS n) hinj
  exact ⟨hg, moduleGlobalSectionsMap_surjective_of_moduleH0Map X (g n) hg⟩

/-- One original quotient map is surjective on both actual `H⁰` and global
sections; only finite-dimensional initial `H¹` is needed. -/
theorem exists_surjective_moduleH0Map_of_h1_chain
    (M Q : ℕ → X.left.Modules)
    (f : ∀ n, M n ⟶ M (n + 1)) (g : ∀ n, M (n + 1) ⟶ Q n)
    (w : ∀ n, f n ≫ g n = 0)
    (hS : ∀ n, (ShortComplex.mk (f n) (g n) (w n)).ShortExact)
    [FiniteDimensional K (moduleCohomology K X (M 0) 1)]
    (hQ : ∀ n, Subsingleton (moduleCohomology K X (Q n) 1)) :
    ∃ n, Function.Surjective (moduleCohomologyMap X (g n) 0) ∧
      Function.Surjective ((g n).val.app (op ⊤)) := by
  obtain ⟨N, hN⟩ := eventually_surjective_moduleH0Map_of_h1_chain X M Q f g w hS hQ
  exact ⟨N, hN N le_rfl⟩

end AlgebraicGeometry.Scheme.Cohomology
