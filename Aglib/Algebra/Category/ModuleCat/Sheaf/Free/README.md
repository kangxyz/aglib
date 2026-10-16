# Sections of the original finite free module sheaf

Import `Aglib.Algebra.Category.ModuleCat.Sheaf.Free.Sections`.
For any ringed site, finite index type `I` and object `X`,
`SheafOfModules.freeSectionsIso` identifies the section module of the
original `free I` with the native finitely supported module on `I` over
the original ring of sections. It uses original evaluation, its finite
coproduct comparison and the native coproduct/direct-sum comparison.

`freeSectionsIso_ι` preserves each original free inclusion and its singleton
map. `freeSectionsBasis` is the resulting actual basis; its `i`th vector is
exactly `(freeSection i).val X`. The restriction formula sends this vector
to the same original free section at the restricted object.

The coefficient sheaf is ring-valued; commutativity, affineness and
Noetherianity are unnecessary. The ring, index and section-module size is
the universe used by Mathlib's native free sheaf, while the site's object
and morphism universes are independent. The native weak sheafification
and locally-bijective hypotheses are explicit. Empty index sets are included.
The immediate consumer is the actual top exterior trivialization over a
commutative ringed site, with determinant normalization.
