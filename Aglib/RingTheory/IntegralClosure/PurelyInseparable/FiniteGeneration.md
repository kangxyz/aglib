# Finite generation from a scalar quotient

For a normal domain `R`, its fraction field `K`, and a finite purely
inseparable extension `E/K`, `isHausdorff_of_isPurelyInseparable` proves that
the literal `integralClosure R E` is separated for the original action of
any ideal `I` for which `R` is separated. A single purely inseparable
exponent works for all elements. Normality puts their powers in the actual
coefficient image; [Frobenius separatedness](../../AdicCompletion/FrobeniusSeparated.md)
then applies to the original algebra map.

`finite_of_isPrecomplete_of_finite_scalar_quotient` assumes additionally that
`R` is `I`-adically precomplete and that `QuotSMulTop x (integralClosure R E)`
is finite over `R`, for some `x ∈ I`. Its literal quotient map onto the
quotient modulo `I` is surjective. The proved separatedness and
[adic coefficient lifting](../../AdicCompletion/FiniteGeneration.md) give
finiteness of the original normalization.

The namespace is `integralClosure`. Neither theorem assumes the
normalization is Noetherian or complete, and neither uses finite generation
of that normalization as a premise. The current normal complete local
surface consumer must still prove the finite scalar quotient by its actual
DVR residue-layer filtration; no two-dimensional normalization theorem is
asserted here.
