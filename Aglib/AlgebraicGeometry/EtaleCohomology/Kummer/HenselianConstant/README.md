# Constant roots over a strictly henselian base

These leaves use the existing multiplicative/root coefficients and the native
henselian finite-etale suppliers. They do not create a new Kummer sequence,
Picard group, classification functor or arithmetic marking interface.

- [Sections](Sections.lean) proves that restriction of actual global root sections to the
  residue point is a multiplicative equivalence. Native separably closed field
  primitive roots then give `globalRootCoordinates` without a marking input.
- [Cover](Cover.lean) defines the actual map from the constant `ULift.{u} (ZMod n)`-labelled cover to
  the original root scheme, by those global sections. Its residue fibre is
  bijective. The native finite-etale fibre equivalence reflects its
  isomorphism; no claim of conservativity for arbitrary sheaves is used.
- The [parent HenselianConstant leaf](../HenselianConstant.lean) defines the abelian coefficient
  map through the native constant-sheaf adjunction. Its underlying set map is
  compared to the actual split-cover map, proving it invertible. Its
  `constantRootIsoOver` pulls this same coordinate to any scheme over the base.
- [Naturality](Naturality.lean) transports the source coordinate to the target through the
  original constant and root inverse-image comparisons. It proves their
  exact coefficient square and the square on original `Sheaf.H` in every
  degree, with independent source and target Ext universes.

The assumptions are a commutative henselian local ring, separably closed
residue field, positive `n`, and invertibility of `n` in the global sections of
its spectrum. No Noetherianity, completeness, perfectness or characteristic-zero
assumption is imposed. Schemes and morphisms over this base are arbitrary.

The target coordinate is deliberately transported from the source coordinate;
it is not a second independent choice that is silently asserted to agree.
These comparison leaves do not assert cohomology vanishing or surjectivity of
a Kummer boundary or a higher-degree restriction.

The finite coefficient value uses `ULift.{u} (ZMod n)` to inhabit the scheme
universe required by the native finite-cover and `ConstantFinite` APIs.
This lift is transported by its actual additive equivalence and is not an
extra arithmetic hypothesis.
