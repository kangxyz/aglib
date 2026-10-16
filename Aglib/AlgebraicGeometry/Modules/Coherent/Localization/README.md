# Coherent restriction as Serre localization

For an open immersion `j : U ⟶ X` between locally Noetherian schemes, the native coherent
restriction functor has kernel the coherent sheaves supported in the closed complement.
This family uses `Scheme.Modules.Coherent`, Mathlib's actual `isoModSerre.Localization`
category and its quotient functor.

For a Noetherian scheme `X`, an open subscheme `U` and closed complement `Z`,
restriction induces `Coh(X) / Coh_Z(X) ≃ Coh(U)`. Here `Coh_Z(X)` consists of
coherent sheaves supported in `Z`. A coherent extension of `F` means a coherent
sheaf `E` on `X` together with an isomorphism `j* E ≅ F`; the extension is not
unique and can have nonzero stalks on `Z`. Extension by zero `j_!` is a different
construction and generally does not preserve quasicoherence. The
[Stacks discussion](https://stacks.math.columbia.edu/tag/029N), Remark 111.36.8,
states the corresponding geometric extension fact. This reference does not
replace the native source construction or its independent review.

- [Denominators](Denominators.lean) identifies the support denominators inverted by
  restriction and detects equality after restriction.
- [Quotient](Quotient.lean) constructs the actual descended restriction functor. It is
  faithful, additive and preserves finite limits and finite colimits. Its factorization,
  quotient-arrow and image-support equations retain the original maps.
- [Fractions](Fractions.lean) first states the fraction construction under an explicit
  subobject-extension hypothesis, then supplies that hypothesis under local Noetherianity.
- [Fullness](Fullness.lean) records the specified quasicoherent direct-image criterion and
  the resulting locally Noetherian fullness of the quotient comparison.
- [Equivalence](Equivalence.lean) first derives equivalence and localization from essential
  surjectivity of restriction. The proved specialization assumes `IsNoetherian X` and
  obtains essential surjectivity from coherent extension.
- [Principal](Principal.lean) proves the affine and global principal-open localization
  statements for a Noetherian coefficient ring, using the actual finite-module comparison
  squares and localization-torsion quotient.

[Extension](../Extension/README.md) supplies the geometric existence results.
[Small support presentations](../Support/README.md) retain the chosen small-model support
categories and exact inclusion comparison.
