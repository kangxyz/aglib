# The original function-field map from a nonempty isomorphism open

Import `Aglib.AlgebraicGeometry.FunctionField.Restriction`.

`Scheme.functionFieldMap_isIso_of_isIso_restrict` takes integral schemes,
an original dominant morphism, a nonempty target open, and invertibility of
the actual restricted morphism. It proves invertibility of the ORIGINAL
function-field homomorphism of that morphism.

The proof uses the same actual source and target open inclusions and their
original field maps, together with the original restriction triangle. No
properness, normality, Noetherianity, dimension bound, chosen field
isomorphism or replacement model is needed.

This is the one proof formerly owned by `Descent.LocalModification`. Its
old `Scheme.LocalModification` theorem retains its unchanged public statement
as a thin caller. The literal completed-model consumer uses this native
lower owner without importing local-modification construction.
