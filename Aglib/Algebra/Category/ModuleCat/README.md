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

[KernelBaseChange/Epimorphism](KernelBaseChange/Epimorphism.md) gives
`ModuleCat.extendedKernelMap_epi_of_ker_eq_map`: in the original commutative
ring square, the canonical scalar-extended kernel map is epi when the target
kernel is the ideal extension of the original kernel. Its unit-tensor formula
retains the original kernel map. No flatness or surjectivity premise is
required; invertibility is not a conclusion.

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

[DirectSumMap](DirectSumMap.lean) constructs canonical direct-sum descent for
bundled module coefficients and the comparison induced by any module-valued
functor. Its summand equation is the actual functor image of the original
coproduct inclusion, without any preservation assumption on the functor.

[FunctorTransport](FunctorTransport.lean) proves functor laws for specified
original arrow families from compatible stagewise linear equivalences. It also
transports native `sectionsSubmodule` families coordinatewise along a natural
isomorphism, without introducing another limit model.

[NatTower](NatTower.lean) defines `ModuleCat.sectionsEval` on the native
compatible-section submodule and proves it surjective at every stage when all
adjacent tower maps are surjective. Ring and module universes are independent.
The maps retain every original transition; no preservation of kernels is assumed.

[Minimal finite free covers and resolutions](MinimalFiniteFreeResolution.md)
constructs a minimal finite free cover of any finite module over a commutative
local ring, without Noetherianity. Over a Noetherian local ring, a finite module
with actual projective dimension at most `n` has an actual minimal projective
resolution with finite free terms and zero terms above `n`.

[StablyFreeBaseChange](StablyFreeBaseChange.md) constructs a finite free
stable complement after an actual flat scalar extension of a finite module
of bounded projective dimension over a Noetherian local ring, whenever that
same scalar extension is projective. The exact scalar-extended short sequence
and splitting maps retain their original module structures. This lower result
is used by regular-local factoriality.
