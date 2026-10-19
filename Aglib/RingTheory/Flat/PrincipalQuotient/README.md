# Regular equations and flat principal quotients

The main public supplier is `Algebra.regular_and_flat_of_fibre_regular`, imported from `Aglib.RingTheory.Flat.PrincipalQuotient.Fibrewise`. For commutative rings `R`, `S`, an `R`-algebra structure on `S`, `[Algebra.FinitePresentation R S]` and `[Module.Flat R S]`, it proves

```lean
(∀ (p : Ideal R) [p.IsPrime],
  IsSMulRegular (p.Fiber S) ((1 : p.ResidueField) ⊗ₜ[R] a)) →
  IsSMulRegular S a ∧ Module.Flat R (S ⧸ Ideal.span {a})
```

There is no Noetherian, reducedness, local-base, domain or characteristic hypothesis on this supplier. Its residue element is the canonical `1 ⊗ a`, and the quotient is the actual principal-ideal quotient. The proof constructs its finite coefficient stage and Noetherian local model through the [finite-presentation prerequisites](../FinitePresentation/README.md); it does not assume their existence as a theorem-family input.

| Focused import | Contents |
| --- | --- |
| `Aglib.RingTheory.Flat.PrincipalQuotient.Basic` | `Algebra.mulLeft_quotient_exact` identifies the principal quotient with the actual cokernel of multiplication. `Algebra.regular_and_flat_principal_quotient_iff` gives the cyclic-quotient tensor criterion for an arbitrary flat algebra. |
| `Aglib.RingTheory.Flat.PrincipalQuotient.BaseChange` | `Algebra.lTensor_mulLeft`, faithfully flat detection of regularity, algebraic-closure and residue-fibre comparisons, and arbitrary scalar-extension/equivalence transport of a regular element with flat quotient. These comparisons retain the actual pure tensor and canonical quotient equivalence. Arbitrary scalar extension does not require a flat base-change algebra when the original quotient is flat. |
| `Aglib.RingTheory.Flat.PrincipalQuotient.Local` | `Algebra.regular_and_flat_of_residue_regular_noetherian` assumes local `R`, local Noetherian `S`, a local structure map and `R`-flat `S`. It proves regularity and quotient flatness from residue injectivity, without adding a separate Noetherian hypothesis on `R`. |
| `Aglib.RingTheory.Flat.PrincipalQuotient.Localization` | Canonical quotient/localization scalar comparisons, transport of regularity and flat principal quotients, and local-to-global criteria using every actual maximal localization of `S`. |
| `Aglib.RingTheory.Flat.PrincipalQuotient.Fibrewise` | Transports the local residue result through localization of the base and supplies the unrestricted theorem above. |
| `Aglib.RingTheory.Flat.PrincipalQuotient.AtPrime` | `Algebra.isSMulRegular_atPrime_of_fiber_regular`, a second public supplier: for flat finitely presented `S` over an arbitrary `R`, regularity of `1 ⊗ a` on the one fiber `(q.under R).Fiber S` gives regularity of `a` at `q`. |

The lower module criteria are in [LocalCriterion](../LocalCriterion/README.md). Scheme chart transports and line-bundle/zero-scheme endpoints remain downstream consumers of these ring/module results.

Extraction basis: pure ring/module blocks of `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, frozen revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256 `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`. No mathematical hypothesis has been strengthened in the transfer.
