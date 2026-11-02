# Original generic-map finiteness from a finite base triangle

`ProjectiveSpace.isDominant_of_injective_base_triangle` derives dominance of
`i ≫ toSpec R iota` from an actual injective map `sigma : R →+* A`, a dominant
`f : X → Spec A`, and the exact triangle
`i ≫ toSpec = f ≫ Spec.map sigma`. No integral, local, finite or geometric
embedding assumption is needed for this dominance statement.

`ProjectiveSpace.genericImageBaseMap_finite_of_finite_base_triangle` adds that
R and A are domains, X is integral, sigma is finite, and the original
function-field map of f is invertible. It derives finiteness of the ORIGINAL
`genericImageBaseMap R iota i`. Its proof is the actual composition equation
for the same scheme maps and the finite field map of `Spec.map sigma`.

No properness, closed immersion, dimension, regularity or completeness is
assumed. The original chosen-embedding GR proof supplies exactly this data;
its private names remain thin wrappers around these single extracted bodies.
The trace-annihilator consumer can therefore construct its genuine generic
input rather than assume a field-finiteness oracle or choose a replacement
function field.
