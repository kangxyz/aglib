# Functors and native extension by zero

Import `Aglib.Algebra.Homology.Embedding.MapExtend` for
`HomologicalComplex.mapExtendIso K F e`. It compares mapping the original
`K.extend e` with extending the original mapped complex. The source and target
categories have zero objects and zero morphisms; the only functor hypothesis
is `F.PreservesZeroMorphisms`. Neither abelianness, additivity, kernel
preservation nor homology preservation is assumed. Category, morphism and
index universes remain independent.

On every retained degree, `mapExtendIso_hom_f_extendXIso` and
`mapExtendIso_hom_f_eq` retain the original native `extendXIso` on both sides.
Outside the image, the component is the unique zero map between the actual
zero objects. The native optional extension terms and differentials underlie
these same components; no replacement complex is introduced.

`mapExtendIso_hom_naturality` keeps the literal original `extendMap` of each
coefficient chain map. `ComplexShape.Embedding.mapExtendNatIso` packages these
same components into a natural isomorphism of the original functors.

The current consumer transports the actual finite-family Cech base-change
map from natural-number complexes to the original integer extension before
good truncation. The separate good-truncation comparison still retains its
own proved boundary-kernel preservation condition.

The leaf passed alone through the shared guarded wrapper, receipt
`1792093270740858000-59900`.
The external `work/proper-validation/MapExtendConsumer.lean` checks the
minimal zero-object hypotheses, independent universes, retained/native and
outside-zero components, coefficient naturality and the same functor
comparison. It passed with receipt `1792093342064637000-61130`; the inspected
declarations use only `propext`, `Classical.choice` and `Quot.sound`.

`MapExtend.Naturality` supplies the same comparison's two-naturality under
an actual natural transformation and its coherence under composition of
zero-preserving functors. `mapExtendIso_hom_natTrans_square` transports an
actual chain square through native extension, keeping the original functor
comparison, coefficient maps and extended arrows. It has no additivity or
homology-preservation hypothesis. The leaf passed alone with receipt
`1792102056800320000-21230`. Its immediate geometric consumer is the
original scalar-forgetting unit square for the integer Cech complex.
The independent-universe external `MapExtendNaturalityConsumer.lean` passed
with receipt `1792102087756923000-21584`; all five inspected declarations
use only the three standard axioms above.

`MapExtend.Homology` proves that this same chain comparison commutes with
the native retained-degree cycle and homology isomorphisms. For abelian
categories and a zero-preserving functor preserving homology,
`mapExtendIso_hom_cyclesMap` and `mapExtendIso_hom_homologyMap` keep the
original `extendCyclesIso`, `extendHomologyIso`, `mapCyclesIso` and
`mapHomologyIso`. No alternative homology object is used. The leaf passed
with receipt `1792102513411127000-28018`. Scalar forgetting is the exact
functor in its geometric consumer; scalar extension need not preserve
homology in that application.
The separate-ring/carrier-universe `MapExtendHomologyConsumer.lean` passed
with receipt `1792102692231320000-30802`; both public declarations use only
the three standard axioms.
