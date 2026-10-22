# Finite-presentation modules over filtered ring colimits

[Models](Models.lean) constructs an actual stage model of a finitely presented
module over the specified filtered ring colimit, below any prescribed stage.
The model is an actual finite matrix cokernel. Its scalar-extension comparison
uses the original quotient projection and original unit tensors.

[Maps](Maps.lean) descends actual homomorphisms between given stage models and
eventual equality of those homomorphisms. Finite matrix coefficients and their
relation witnesses are synchronized at a common later arrow, including for
non-thin filtered categories. The recovery equation uses the native
`ModuleCat.extendScalarsCoconeCompIso` for the original cocone.

These statements impose finite presentation on the supplied coefficients.
No Noetherianity, coherence, flatness or injectivity of transition maps is
required. The module carrier universe in `Models` is independent of the ring
universe; each theorem retains its explicit universe bounds.

The [scheme module-Hom descent family](../../../../../AlgebraicGeometry/Descent/FinitePresentation/Modules/README.md)
transports these actual matrix constructions through native affine sections
and pullbacks, then glues the original local arrows.
