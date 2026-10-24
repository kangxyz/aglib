# The actual completed local factors of a finite algebra

Import `Aglib.RingTheory.AdicCompletion.FiniteSemilocal`.
The namespace is `AdicCompletion.FiniteSemilocal`.

Let R be a Noetherian local ring and S a finite commutative R-algebra.
The interfaces retain a Noetherian instance for S, supplied by
`IsNoetherianRing.of_finite R S`. Define the literal closed-fibre ideal
`I = (maximalIdeal R).map (algebraMap R S)`.

`Branch R S` is `MaximalSpectrum (S ⧸ I)`. For a branch q, `branchIdeal R S q`
is the inverse image of q's ideal under the original quotient map. It is
maximal and contracts to `maximalIdeal R`. `Local R S q` is its actual prime
localization, and `Completed R S q` is that local ring's maximal-adic completion.
`finite_branch` proves finiteness of the branch set from the Artinian closed
fibre. `branchOfPrime` includes any supplied original prime over the closed
point, and `branchIdeal_branchOfPrime` recovers exactly that prime.

`baseAlgebra R S q` is the original completion map supplied by
[FiniteLocalization](FiniteLocalization.md), including its same-precision maps
on all ideal-power quotients. `baseIsScalarTower` and `base_algebraMap` retain
the original R-action. `baseFinite` and `baseIsLocalHom` prove that this actual
completed-base map is finite and local. The uncompleted localization is not
assumed finite over R.

Writing Rhat for `AdicCompletion (maximalIdeal R) R`, `tensorEquiv` constructs
the Rhat-algebra equivalence

```text
Rhat ⊗[R] S ≃ₐ[Rhat] ∀ q : Branch R S, Completed R S q.
```

It uses the proved general `exists_residueBranchesAlgEquiv`, then the original
maximal-localization completion equivalences. The residue quotient is proved
Artinian from the original finite algebra. The completed-base component map
is identified at every quotient level with `FiniteLocalization.completionMap`.
Thus no product decomposition, cofinality exponent, or factorization of I is
assumed.

`tensorEquiv_one_tmul` sends `1 ⊗ s` in each component through the literal maps
S→Local(q)→Completed(q). `tensorEquivRight` gives the same equivalence with
domain `S ⊗[R] Rhat` and its original right Rhat-action, using canonical tensor
commutation. `tensorEquivRight_tmul_one` gives the corresponding integral-element
equation for `s ⊗ 1`.

The degree consumer is [FiniteSemilocalDegree](FiniteSemilocalDegree.md).
The decomposition itself requires no domain, normality, separability, dimension,
or Dedekind hypothesis on S.
