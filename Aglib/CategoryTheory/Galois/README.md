# Connected objects under equivalence

[Connected](Connected.lean), imported as `Aglib.CategoryTheory.Galois.Connected`,
adds `CategoryTheory.PreGaloisCategory.isConnected_obj_of_equivalence` to Mathlib's
actual connected-object interface. A supplied categorical equivalence preserves
connectedness by reflecting initiality and monomorphisms through its inverse.
Source and target object and hom universes remain independent; no fibre functor
or geometric classification is assumed.
