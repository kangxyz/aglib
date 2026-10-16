# Exactness through actual module localizations

Import `Aglib.Algebra.Category.ModuleCat.Localization.Exactness`; [Exactness](Exactness.lean) extends `ModuleCat` using actual categorical module diagrams.

`ModuleCat.isLocalizedModule_piMap` proves that a finite categorical product of supplied localization maps is a localization map. The finite product index and actual localized coefficient maps remain inputs.

`ModuleCat.shortComplex_exact_of_isLocalized_span` detects exactness of an actual module short complex from compatible localized short complexes. The localizing elements must span the unit ideal, and the localized complexes must be exact. It does not infer these premises from a merely chosen set of elements.

The consumers are [generic basis/sheaf exactness](../../../../Topology/Sheaves/README.md) and affine section/Cech arguments. The lower objects are native commutative-ring localizations and module short complexes; no finite-generation or geometric hypothesis is added beyond the source statement.

[Submodule](Submodule.lean) identifies when the actual localized inclusion of a submodule
is an isomorphism, through equality of its localized underlying submodule with the top.
