# Properties of original finitely presented stage modules

The module proves the properties below using the actual global Hom and
equality supplier in `Maps`. Its native module check passes with the same
unrestricted morphism hypotheses.

`Scheme.Modules.exists_isIso_pullback_above_of_isLimit` detects eventual
invertibility of the original finitely presented stage map. It descends an
actual inverse to its literal limit pullback, then both inverse equations,
and returns invertibility of the original map after an actual later
pullback. The stage map is retained through native pullback composition.

`Scheme.Modules.exists_relative_iso_above_of_isLimit` retains the specified
relative coefficient system, its actual structural maps, and both original
triangle recovery equations. Its hom equation and inverse equation use the
same `pullbackHomOfTriangle` comparisons. The inverse equation follows from
uniqueness of the inverse of the recovered actual isomorphism.

`Scheme.Modules.exists_iso_pullback_above_of_isLimit` specializes that
relative construction to two already-given original stage models. The
forward and inverse recovery equations use their original
`pullbackConeCompIso`; neither model is replaced.

`Scheme.Modules.exists_isLocallyRankOne_pullback_above_of_isLimit` concerns
an already-given finitely presented stage module whose literal limit
pullback has local rank one. It constructs actual affine open frames on
that limit sheaf. The native finite affine-cover descent theorem supplies a
genuine finite affine cover at a stage, with exact preimage equalities.
After moving to a stage mapping to both the original coefficient stage and
that cover stage, these same frame isomorphisms are descended on the native
`AlgebraicGeometry.opensDiagram` and `opensCone` systems.

Each frame is a specified relative isomorphism between the original module
and the original structure module along the actual restricted coefficient
map. The inverse and its inverse equations descend through the preceding
isomorphism theorem. A common later stage carries all finitely many actual
frames. Their original preimage opens cover that whole stage, so their
restriction isomorphisms construct local rank one there. Native pullback
composition identifies the result with the literal pullback of the
original input module. No stage free-locus pullback or freeness certificate
is used in place of this cover and these actual maps.

All systems are arbitrary native cofiltered qcqs scheme systems with affine
transition maps and their specified actual limit cone. Only actual finite
presentation of the input modules is imposed; no Noetherianity, coherence,
flatness or injectivity premise is added. The module depends on the actual
global Hom/equality supplier in `Maps`, and never on `Objects`.
