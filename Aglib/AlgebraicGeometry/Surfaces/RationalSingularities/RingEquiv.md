# Universal modification vanishing under a ring equivalence

Import `Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.RingEquiv`.
The namespace is `AlgebraicGeometry.Scheme.RationalSingularities`.

For commutative domains `A` and `B` in the original predicate's universe and
an actual `e : A ≃+* B`,
`normalModificationH1Vanishing_iff_of_ringEquiv` proves equivalence of their
universal normal-modification structure-H1 vanishing properties.

The forward proof composes each actual `f : Z -> Spec B` with the ORIGINAL
`Spec.map e : Spec B -> Spec A`. Its actual function-field map is compared
by `functionFieldMap_comp`. The same scheme `Z`, its original structure
module and its H1 group remain unchanged; no cohomology transport is assumed.
The reverse proof uses `e.symm` in the identical construction.

There are no local, Noetherian, Nagata, completeness, regularity or dimension
premises. This transports a proved universal vanishing property; it does not
construct that property from a desired rationality conclusion or supply any
resolving chain.
