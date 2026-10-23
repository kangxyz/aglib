# Native exterior powers and changing coefficient rings

`Semilinear` extends Mathlib's original `exteriorPower` objects.
`exteriorPower.mapSemilinear n f` sends every original wedge to the wedge
of the images under `f`, for an arbitrary semilinear map over any
homomorphism of commutative rings. The two ring universes and two module
universes are independent. No finiteness, flatness or invertibility
hypothesis is imposed, and degree zero is included.

The construction uses the existing universal
`exteriorPower.alternatingMapLinearEquiv` with the actual target action
restricted through `Module.compHom`. `semilinearMap_ext` detects equality
on original wedges. Identity and composition are proved for this same map;
composition retains Mathlib's native `RingHomCompTriple` identifying the
displayed composite ring map. For the literal composite, that class is
supplied by `⟨rfl⟩`, with no additional mathematical premise. When the
coefficient ring is unchanged, `mapSemilinear_eq_map` identifies the map
with the existing native `exteriorPower.map`.

The immediate consumer is the actual exterior power of a presheaf of
modules: its restriction maps change coefficient rings. Module
sheafification, exterior local bases and determinant transition formulas
are subsequent interfaces. No new exterior-power quotient or substitute
module object is introduced here.

`TopDegree` proves that a displayed `Basis (Fin n) R M` identifies the
original top exterior power with `R`. The forward map is the native basis
determinant extended through the original exterior universal property;
the inverse is exactly `r ↦ r • exteriorPower.ιMulti R n b`.
`exteriorPower.ιMulti_eq_det_smul` retains this generator formula for every
wedge. `Module.Basis.exteriorPowerTopEquiv_changeBasis` gives the original
basis-change determinant, and `exteriorPowerTopEquiv_mapSemilinear` gives
the determinant of the source-basis images times the original ring-map
image of the scalar coordinate. Rank zero and trivial coefficient rings
are included; no localization, flatness or nontriviality is assumed.
The immediate consumer is the actual local top-exterior frame and its
determinant transition in the module-sheaf family.

`BaseChange` changes coefficient rings along an algebra `A → B`.
`mapOfIsScalarTower B k g` sends `p₁ ∧ ⋯ ∧ p_k` to `g p₁ ∧ ⋯ ∧ g p_k`
for an `A`-linear `g` into a `B`-module; it is the `A`-linear form of
`mapSemilinear` along `algebraMap A B` (`semilinearOfIsScalarTower`).
`toBaseChange A B k P` is the case `g = 1 ⊗ ·`. Its `B`-linear extension
`B ⊗[A] ⋀[A]^k P → ⋀[B]^k (B ⊗[A] P)` is surjective for every module and
bijective for projective modules (`isBaseChange_toBaseChange`; free
modules by bases, projective modules as retracts). Exterior powers of
projective modules are projective, and a finite projective module of
constant rank `r` has `k`-th exterior power of constant rank `r.choose k`
(`rankAtStalk_exteriorPower`). `tmul_ιMulti_induction` is the induction
principle on `a ⊗ (m₁ ∧ ⋯ ∧ m_k)`. `Wedge` gives left wedge multiplication
`wedgeLeft n m : ⋀^n M → ⋀^(n+1) M`, natural and compatible with base
change. If `V ⧸ N` is finite projective of constant rank `n + 1`, then `N`
consists of the `v` with
`v ∧ ⋀^n V ⊆ ker (⋀^(n+1) V → ⋀^(n+1) (V ⧸ N))`
(`mem_iff_forall_wedgeLeft_mem_ker`). Consumer: the Plücker map in
`RingTheory/Grassmannian`.
