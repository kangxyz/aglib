# Denominators of finite fractional coordinates

`FractionalIdeal.denominatorIdeal L` is the native submodule colon
`(1 : FractionalIdeal R⁰ K) : L`. It consists of the original elements of
`R` that multiply every element of `L` into the image of `R` in `K`.
The definition retains its ordinary meaning for the zero fractional ideal.

`mem_denominatorIdeal_spanFinset_iff_dvd` uses an actual common denominator
and its actual numerators to express membership by divisibility in the
original ring. `numeratorLinearMap` gives the actual `R`-linear map from
this denominator ideal to `R` for each specified element of `L`, with its
original coefficient-map equation.

For a GCD domain, `exists_denominatorIdeal_spanFinset_generator` constructs
a nonzero generator when the specified finite coordinate family contains
the original coordinate one. The proof takes the gcd of the actual
common-denominator numerators and divides that denominator by the gcd.
No principal-ideal-ring or Noetherian hypothesis is required. The fraction
field and finite index may have independent universes.

This algebraic supplier is intended for the actual denominator and base
ideals of rational maps on regular schemes. Sheaf gluing, local generator
comparisons and finite point-blowup resolution are separate constructions.

`denominatorProductIdeal L` is the integral ideal corresponding to the
literal fractional product `denominatorIdeal L * L`. Each specified
coordinate gives its original numerator map into this ideal. If `L`
contains one and its denominator ideal has a nonzero generator,
`denominatorProductIdeal_not_le_span_singleton` proves that no proper
principal ideal contains the normalized base ideal. This primitivity
statement uses neither a dimension nor a Noetherian hypothesis.

For finite coordinates,
`denominatorProductIdeal_spanFinset_eq_iSup_range` identifies this ideal
with the supremum of the ranges of the original coordinate numerator
linear maps. This provides the intrinsic image-ideal comparison required
when gluing the same coordinates into a coherent sheaf.
