# Original affine and Serre transport for canonical restriction

This module transports the original relative closed-embedding Serre comparison
through a specified canonical reconstruction and the original affine derived
sections. Its intended consumer is the surface-to-curve canonical restriction.
This transport module does not complete that comparison.

`restrictionModuleSerreMap` starts with native Ext into the supplied canonical
module and uses the original relative Serre map, its actual own-object
reconstruction, and the installed single-functor shift comparisons. The affine
step is the actual derived sections map, transported through the original
global-sections composition isomorphism and the original acyclic coefficient
single. A specified comparison from the coefficient's actual affine sections
to its retained module gives the final target. For the intended consumer,
this input is the original spectrum unit comparison or `tilde.isoTop`;
no coefficient orientation is selected here.

The output degree is the integer `r-d`, including negative values. The affine
Hom bijection is derived from the installed native comparison on shifted
quasicoherent singles. It imposes no projectivity or injectivity assumption on
the source module or its derived sections. The required quasicoherence and
quasi-compact, quasi-separated geometry remain explicit in the internal affine
producer. A closed projective embedding supplies that geometry for the public
Serre family.

`restrictionClosedSerreMap` retains an additional actual closed immersion. Its
source comparison is exactly `relativeClosedEmbeddingPushforwardSingleIso`,
including the original derived pushforward composition and exact closed-image
single. It is suitable for the surface Ext group produced by the original
positive Cartier row.

The `_bijective` results assume the actual source is affine locally of finite
type and the base is Noetherian. Their forward maps are the displayed original
maps. The `_comp` results preserve arbitrary source Ext composition, including
the native shifts and unsigned Yoneda products. The unit factorizations derive
compatibility of the original derived comparison transformations with shifts;
no compatibility predicate is supplied as a hypothesis. Pure categorical
recipes remain private except for the three actual shift-transport laws needed
by the parent finite-scalar comparison.

The scheme and module derived models are the installed standard models of
size `u+1`, matching the native affine comparison. `restrictionSerreObject` is
the original closed right-adjoint value with the supplied relative coefficient,
and `restrictionDerivedSections` uses the original structural coefficient map.
The public maps are deliberately not exposed as unfoldable implementation
terms; their proved bijectivity and source-composition laws form the interface.

The internal transport remains additive throughout. Its input is the original
`Ext.homAddEquiv` followed by the same single-reindexing and canonical
reconstruction arrows; its output is postcomposition by the same inverse
single-reindexing arrow. Their source-composition laws are proved from these
original constructors. No alternate integer module structure is introduced.
The original field actions are retained through actual coefficient morphisms
and the arbitrary source Ext law. The standard derived-category instance is
available to the public signatures. Finiteness of the projective
index is derived locally from the supplied equivalence with `Fin (n+1)`; it is
not an additional public hypothesis. The componentwise natural isomorphism on
complexes is identified with its original natural transformation before proving
shift compatibility from the derived-unit equation.

The full-faithful shifted-Hom equivalence has the original shifted functor map
as its literal forward function. Its inverse is the native preimage after the
original inverse shift comparison. A private categorical calculation handles
source naturality and coefficient postcomposition before the affine geometry
is instantiated; the actual global-sections units determine its shift hypothesis.
The entire affine Hom equivalence and its source-composition proof are first
constructed for variable functors and typed endpoints. The geometric declaration
instantiates that constructor with the actual affine bijectivity theorem,
original derived sections isomorphism, native inclusions and original coefficient single.

This module does not construct a new canonical module, prove a geometric
concentration theorem, or assume the desired surface-to-curve comparison. The
surface-to-curve consumer must supply the actual canonical reconstructions
from normal-surface and coefficient-valued CM-curve concentration and retain
the original Cartier mate and finite-coinduction counit. Canonical
restriction, its trace identity, generation and RDP conclusions are outside
this lower transport family.
