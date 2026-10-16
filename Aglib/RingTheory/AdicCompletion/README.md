# Adic completion

[FiniteModule](FiniteModule.lean), imported as `Aglib.RingTheory.AdicCompletion.FiniteModule`, proves completeness of finite modules over a Noetherian ideal-adically complete ring and of finite algebras for the extended ideal. Its base need not be local. [Formal-smooth lifting](../Smooth/AdicCompletion.lean) uses this completeness to lift actual quotient and tensor closed-fibre maps.

[DiscreteValuationRing](DiscreteValuationRing.lean), imported as `Aglib.RingTheory.AdicCompletion.DiscreteValuationRing`, equips `AdicCompletion (IsLocalRing.maximalIdeal R) R` with domain, DVR, and henselian local-ring structures for a domain DVR `R`. It uses the canonical completion algebra map and `FractionRing` carrier. The residue identification is the inverse of the induced residue-field map; selected residue markings and the fraction-field/constants triangles retain those actual maps.

The domain/DVR proof uses the [separated principal-maximal-ideal criterion](../LocalRing/SeparatedPrincipal.lean). The new declarations are a source migration from the identified R5 snapshot; source correspondence does not assert native elaboration or independent proof acceptance.
