# Exactness reflected by scalar restriction

[Exactness](Exactness.lean), imported as `Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Exactness`, gives `ModuleCat.shortExact_of_restrictScalars`. An actual module short complex is short exact when its restriction along the supplied ring homomorphism is short exact. Source and target are rings; this lower statement has no scheme or commutativity premise merely from its geometric consumers.

The underlying maps are the original module maps. Tensor/direct-image and scalar comparison arguments use this reflection after constructing their actual coefficient action. Restriction does not supply an unstated finite-generation or Noetherian property.
