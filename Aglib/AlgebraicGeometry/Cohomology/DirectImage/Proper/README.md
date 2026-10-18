# Proper coherent higher direct images

[Coherent](Coherent.lean) proves
`Scheme.Modules.moduleHigherDirectImage_coherent_of_proper`: every original
`(pushforward f).rightDerived q` sends a coherent coefficient to a coherent
sheaf for a proper map with locally Noetherian target. The target need not
be quasi-compact, and the coefficient need not be relatively flat.

The proof descends the actual affine-base
[proper finiteness theorem](../../Proper/Finiteness.lean) along target affine
charts. It uses the original
[higher-image open comparison](../Restriction.lean) and the native affine
finite-sheaf comparison. There is no new cohomology construction or supplied
proper-finiteness family. The arbitrary-universe public consumer checks the
proper and finite specializations; the inspected theorem uses only the
three standard axioms. A uniform global derived upper bound on a target
that is not quasi-compact is not claimed by this interface.

[Grauert](Grauert.lean) proves
`Scheme.Modules.moduleHigherDirectImage_finiteLocallyFree_of_isLocallyConstant_of_proper`:
the actual `((pushforward f).rightDerived q).obj M` is
`SheafFiniteLocallyFree` when the target is reduced and locally Noetherian,
`f` is proper, the original coefficient is coherent and relatively flat,
and its intrinsic `modulePointFiberCohomologyDimension f M q` is locally
constant. The target need not be quasi-compact, and no uniform global
cohomological bound or flatness of `f` is assumed.

The proof uses actual affine target opens. The original higher-image open
comparison and ordinary coefficient comparison identify each restricted
higher image. Its small native section module is finite by proper coherence
and projective through the original affine-sections/cohomology equivalence
and the affine proper Grauert theorem. Native tilde of these small sections,
followed by the actual quasicoherent counit, supplies finite local bases of
the unchanged sheaf. The general-target conclusion descends along the
original affine open cover, including an empty target. This theorem does not
construct the separate nonflat higher-direct-image base-change sheaf map.

[BaseChange](BaseChange.lean) proves three general-base proper base-change
theorems for that actual [nonflat comparison](../../BaseChange/HigherDirectImage/Nonflat.lean).
The common hypotheses are a locally Noetherian target, proper `f`, coherent
coefficient `M` (`affineLocallyFiniteType X M`), and `relativeFlat f M`.

- On a reduced target, locally constant intrinsic fibre-cohomology dimension
  implies invertibility after every Cartesian base change.
- Epimorphy of the actual global-section residue comparison at a point gives
  a genuine open neighbourhood on which every base change has invertible
  comparison. This does not require a reduced target.
- Epimorphy of those actual residue comparisons at every point implies
  invertibility after every Cartesian base change, also for nonreduced targets.

The new base scheme is arbitrary: no flatness, Noetherianity, quasi-compactness
or nonemptiness condition is added. The residue comparison is
`higherDirectImageResidueBaseChangeMap`; its affine criterion retains the
original scalar map and the actual residue-field isomorphism. The global
comparison is glued from internally proved chart compatibility, using the
ordinary module-Hom sheaf.
