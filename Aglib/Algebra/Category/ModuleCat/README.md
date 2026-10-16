# Module categories and scalar constructions

This family extends the actual category `ModuleCat R` and its scalar, tensor,
presheaf and sheaf constructions. The category of finitely generated modules
and its Noetherian Serre/exact specialization have their focused
[FGModuleCat](../FGModuleCat/README.md) owner.

[ScalarExtensionUnit](ScalarExtensionUnit.lean) proves
`ModuleCat.restrictedExtensionUnit_apply`: for compatible commutative ring maps
`R → A → S`, the restricted extension/restriction unit is literally
`x ↦ 1 ⊗ x`. The equality expressing compatibility of the scalar maps remains
an input.

[Localization/Exactness](Localization/README.md) is the lower actual-localization
detection interface. [ChangeOfRings](ChangeOfRings/README.md),
[Monoidal scalar restriction](Monoidal/README.md),
[scalar-extension tensor](Tensor/README.md),
[module presheaves](Presheaf/README.md) and
[site module sheaves](Sheaf/README.md) retain their own scalar and site data.
The site tensor is canonical below scheme and invertible sheaves; finite-free,
retract-exactness and injective-preservation statements retain their separate
hypotheses.
