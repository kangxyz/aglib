# Finite submodules and localization

[FiniteSubmodule](FiniteSubmodule.lean), imported as
`Aglib.Algebra.Module.LocalizedModule.FiniteSubmodule`, supplies three results in
`IsLocalizedModule`. A localized module finite over its localization ring has a finitely
generated submodule before localization with the same localization. A finitely generated
submodule of the localized module can likewise be lifted. The third theorem realizes this
simultaneously for a finite family of localizations.

The statements use the specified `IsLocalizedModule` linear maps and the actual
`Submodule.localized'` images. Their original independent ring, module and indexing universes
are retained. The rings are commutative; no Noetherian hypothesis is required.
