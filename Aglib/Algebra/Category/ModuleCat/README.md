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

[BaseChange](BaseChange.lean) identifies the actual scalar-extension/restriction mate over an arbitrary commutative-ring pushout with the canonical tensor comparison. Pure-tensor and original-unit equations preserve the same map; no flatness or finiteness hypothesis is used.

[KernelBaseChange](KernelBaseChange.lean), imported as `Aglib.Algebra.Category.ModuleCat.KernelBaseChange`, constructs the actual restricted and scalar-extended maps of ring kernels and their inclusion equation. Its canonical scalar-extension comparison is natural for actual module morphisms. Construction requires the displayed commutative square; flatness is reserved for the lower quotient-flat ideal theorem.

[FinitePresentation](FinitePresentation.lean) proves finite presentation of
the actual categorical cokernel of a map from a finite module to a
finitely presented module. Ring and carrier universes remain independent.
The proof transfers the native quotient presentation through the original
cokernel/range-quotient isomorphism. Free-locus and Grauert arguments use
this lower result without imposing Noetherianity.

[FiniteLength.Restriction](FiniteLength/Restriction.lean) separates surjectivity of module localization at units
from finite-length restriction along a surjective ring map. [FiniteLengthFamilies](FiniteLengthFamilies.lean)
constructs the actual finite-support, coordinatewise finite-length Serre
subcategory of dependent module families and its exact coordinate functors. The
finite-support property delegates to `CategoryTheory.Pi.FiniteSupport`; no
semisimple or residue-field category replaces the given module actions.
