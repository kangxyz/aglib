# Original derived flat base change

[Resolution](Resolution.lean), imported as
`Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Resolution`, retains
the actual ordinary cartesian mate on a supplied injective resolution,
followed by pushforward of the native exact-pullback resolution comparison.
`flatBaseChangeResolutionMapPlus_hom_f` records its literal components.

`flatBaseChangeResolutionSourceIso` and
`flatBaseChangeResolutionTargetIso` use the original installed derived
units, original resolution augmentations and native exact-single
comparison. `flatBaseChangeResolutionMapPlus_derived` identifies this
actual chain map with the existing `derivedFlatBaseChangeMap` on the
coefficient single. The statement applies to an arbitrary supplied
cartesian square and arbitrary module. The base map is flat; flatness of
the pulled-back leg follows from that square. No quasicoherence,
Noetherianity, finiteness or preservation of the image comparison's
quasi-isomorphism by pushforward is assumed. Invertibility of the
geometric derived base-change map is a subsequent assertion.

[Shift](Shift.lean) proves that the EXISTING `derivedFlatBaseChangeMap`
commutes with native integer shifts. The original ordinary mate and both
installed composition units are shift-compatible; the original defining unit
square and native derived uniqueness give this same map's compatibility.
Only flatness of the base map is required; flatness of the pulled-back leg
is derived from the supplied Cartesian square. No quasicoherence,
Noetherianity, cohomological dimension or invertibility premise is used.
The native flat-pullback shift instance is `derivedFlatPullbackPlusCommShift`;
`derivedFlatPullbackPlus_commShift` remains a transparent deprecated alias without
a second instance. The native triangulated structure is retained.
The lower bounded-below quasi-isomorphism shift stability is proved in
`CochainComplexPlus.QuasiIsoShift`, respecting the irreducible native induced
shifts. Shared Postnikov comparisons consume this original transformation.

[Restriction](Restriction.lean) gives the original derived flat-pullback
composition isomorphism and its exact installed-unit formula. For open
base change, `isIso_derivedFlatBaseChangeMap_of_isOpenImmersion` proves
invertibility of the existing natural transformation on every bounded-below
module complex. It uses the original ordinary mate and the native
right-derived uniqueness property; no QC or Noetherian premise is needed.
`derivedFlatBaseChangeMap_comp` proves the exact pasting identity for two
successive flat changes of base. Its pullback-composition maps are the same
native maps normalized by the displayed units; the proof reduces their
original units to `cartesianBaseChangeMap_comp`. No quasicoherence,
finiteness, Noetherianity or invertibility hypothesis is imposed on this
identity. The public original-map consumer passed with the three standard
axioms at the default proof budget.

[Affine/Postnikov](Affine/Postnikov.lean) extends the affine single theorem
to every bounded-below object with quasicoherent original homology,
through the same original shift-compatible transformation and the shared
Postnikov comparison. [Locality](Locality.lean) proves
`derivedFlatBaseChangeMap_isIso_of_quasicoherent_homology` over arbitrary
base schemes. Its hypotheses are exactly a supplied Cartesian square,
a flat base map, a qcqs direct-image map and quasicoherence of each
original homology sheaf. An affine refinement of the pulled-back target
cover and two applications of `derivedFlatBaseChangeMap_comp` reduce to
the affine endpoint; native derived open-cover reflection finishes the
descent. No termwise QC, upper bound, cohomological dimension,
Noetherianity or finite-generation hypothesis is added. The raw public
consumer, including the literal native fibre product, passed with receipt
`1792123092673396000-53359` and the three standard axioms.

[HigherDirectImage](../HigherDirectImage.lean) defines
`higherDirectImageFlatBaseChangeMap` on the actual native
`(pushforward f).rightDerived n`. Its component formula is literally
homology of the same `derivedFlatBaseChangeMap` on the native degree-zero
single, conjugated by the installed single and exact-pullback homology
comparisons. The component is invertible for qcqs `f`, a flat base map
and arbitrary QC coefficients, in every natural degree and on arbitrary
base schemes. `higherDirectImageFlatBaseChangeIso_hom` is a literal equality
to that map. The leaf also exposes the original derived comparison on QC
singles in every integer placement. The raw native-map, coefficient
naturality, homology formula and isomorphism consumer passed with receipt
`1792123356895699000-56376`; all four inspected declarations use only the
three standard axioms.
