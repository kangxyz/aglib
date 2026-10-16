# Exterior powers of actual module sheaves

Import `Aglib.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic`.
`SheafOfModulesOfCommRing.exteriorPowerFunctor` takes the original pointwise
module exterior presheaf and applies the original module sheafification.
Its objects remain actual `SheafOfModules`; the underlying ring sheaf is
the original commutative ring sheaf composed with the native forgetful
functor. Ring, module, site-object and site-morphism universes remain
independent, with output module carrier in their required ring/module maximum.

The site is arbitrary. The interface retains the explicit sheaf-composition,
additive sheafification and locally-bijective characterization hypotheses
needed by the native sheafification API. No field, scheme, finite type,
local freeness or quasicoherence assumption is made. Local injectivity and
surjectivity of the original ring identity are proved internally.

`exteriorPowerHomEquiv` proves the universal property against every target
module sheaf of the displayed size: morphisms from the actual exterior
sheaf are equivalent to compatible families of native sectionwise
alternating maps. It is exactly the original `sheafificationHomEquiv`
followed by the proved presheaf universal property. The canonical
`exteriorPowerMk` is the original sheafification unit on a native wedge.
Its restriction formula, descent evaluation, morphism extensionality and
coefficient-map formula are public and retain those exact maps.

The lower implementations are the
[presheaf exterior power](../../Presheaf/README.md) and native module
sheafification. Local exterior frames, the top exterior line and
determinant transition formulas are the next consumers. Relative
canonical bundles will use this same general ringed-site object, with
the actual relative differential sheaf; this leaf does not yet assert
canonical-bundle identification or relative duality.

`FreeTop` constructs `exteriorTopFreeIso`: the same actual exterior sheaf
of the rank-`n` native free sheaf, in degree `n`, is the actual structure
module. The finite free index is `ULift (Fin n)`, retaining arbitrary
coefficient universe. The original section basis is proved from finite
free sections, rather than assumed. The forward map evaluates the native
determinant on each original wedge; the inverse sends a scalar to its
multiple of the wedge of the original free sections. Both inverse
equations are proved. Rank zero and arbitrary commutative rings are
included, and the global compatible-section construction needs no
terminal object in the site. The original restriction comparison and
local top-line frames are the next scheme-level consumers.
