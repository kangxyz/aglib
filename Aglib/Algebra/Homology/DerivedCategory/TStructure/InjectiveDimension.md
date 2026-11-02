# Finite injective dimension and actual bounded cohomology

Let `C` be an abelian category with its selected native derived category.
Let `X` have original cohomology only in degrees `[a,b]`, and let `N` have
native injective dimension at most the natural number `d`. For an integer
`t` satisfying `d < t+a`,

`Hom_D(X, N[0][t]) = 0`.

`subsingleton_hom_single_shift_of_injectiveDimension` proves the Hom type
is a subsingleton; `hom_single_shift_eq_zero_of_injectiveDimension` gives
its pointwise zero form. Category object, category morphism, Ext, and
selected derived-category universes are independent.

The proof reuses `Plus.property_of_homology_bounds` on the original
bounded-below inclusion. Vanishing of Hom into the fixed target is closed
under isomorphisms, contains zero, and is closed under extensions by the
native `Triangle.yoneda_exact₂`. A degree-`j` original homology single is
tested by `Ext^(t+j)(H^j X,N)`, through the original fully faithful shift
functor and native single/shift comparisons. Since `j ≥ a`, intrinsic
injective dimension kills this group.

The upper bound is used to make the homology-layer reduction finite.
No upper term bound, finite-generation condition, representative complex,
chosen injective resolution, or enough-injectives hypothesis is assumed.
The application to the original coinduced canonical coefficient must
separately prove the actual dual's homology bounds and retain its original
comparison maps. This general vanishing theorem supplies neither a
duality equivalence nor a Gorenstein conclusion.
