# Conditional canonical Cartier ideal interfaces

`Interfaces.lean` records the general codimension-one, avoidance, product and
DVR-fibre statements on the actual native kernel ideal modules. It does not
prove those theorem families. `Restriction.lean` records their exact
restriction application. The product comparison retains its multiplication
and inclusion triangle. The product-equals-intersection statement requires
Cartierness of the actual intersection on the second divisor.

These interfaces are distinct from the proved smooth-relative-curve supplier
in `EffectiveCartierDivisor/Smooth/Ideal.lean`. The relative graph and
base-change adapters reuse that supplier and the actual native ideal map.
General regular codimension-one Cartierness, avoidance and product results
remain explicit conditions when no matching producer is imported.

Source: R5 packet revision `f8a3314ddecffcada2ec721d26d56a937bed9690`,
`R5Lab.Aglib.AlgebraicGeometry.Divisors.Cartier.{Interfaces,Restriction}`.
