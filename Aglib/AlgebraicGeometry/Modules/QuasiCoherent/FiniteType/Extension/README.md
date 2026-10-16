# Finite-type approximation on affine schemes

[Affine](Affine.lean), imported as
`Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Affine`, gives
`Scheme.Modules.QuasiCoherent.exists_fg_submodule_principal_restriction_isIso`,
`exists_fg_submodule_open_restriction_isIso` and
`exists_finiteType_subsheaf_restrict_isIso`.

A finite family of principal restrictions that are finite modules is realized by one
finitely generated submodule. The compact-open form assumes an explicitly compact open in
`Spec R` and finite type on that open. For a quasicoherent ambient sheaf, the resulting
finite-type subsheaf has a monic inclusion whose actual open restriction is an isomorphism.
The ring need not be Noetherian, and the ambient quasicoherent sheaf need not be finite type.

The algebraic input is [finite localized-submodule approximation](../../../../../Algebra/Module/LocalizedModule/README.md).
The [coherent extension family](../../../Coherent/Extension/README.md) adds the stated
Noetherian hypotheses for global extension.
