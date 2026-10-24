# Original canonical cohomology and the native derived dual

[Cohomology.lean](Cohomology.lean) constructs the actual A-linear
comparison needed in degrees zero and one:

    H^r(X, omega_X) ≃ₗ[A] H^r(D_J(C_A)),

where `C_A` is literally `moduleDerivedStructure X alpha_A`,
`alpha_A` is the original structural map from `g : X → Spec A`, and
`omega_X` is the actual `normalSurfaceCanonicalModule`. The construction
works for every natural r. The final degree-zero normalization against
the section trace is a remaining adapter, described below.

The original concentration conditions and coefficient are retained.
In particular K is `normalSurfaceDualizingObject`, formed with the literal
`normalSurfaceAmbientCoefficient`, and its reconstruction is the original
homology-normalized `normalSurfaceCanonicalIso`. The canonical module
need not be invertible.

The inputs include actual supplied native resolutions `I_X` of `O_X`
and `I_R` of the regular base module R. Their original complexes give

    C_chain = moduleResolutionSectionComplex X alpha_A I_X,
    J = coinducedCoefficientComplex sigma I_R.cochainComplex.

`normalSurfaceStructureResolutionIso` uses the original bounded-below
resolution comparison to identify `Q(C_chain)` with the actual `C_A`.
`normalSurfaceStructureResolutionUnit` is the original structural section
map, followed by the native inverse single comparison and `I_X.ι'`.
Its normalization theorem identifies its localization with the original
`moduleDerivedStructureUnit`.

The geometric half uses the original cohomology/Ext equivalence, the
actual concentration isomorphism and native single shifts. It applies
`relativeClosedEmbeddingSerreMap` in degree `n+r` with its existing
coherent-source bijectivity theorem. Actual affine derived sections use
the same functor and `affineDerivedStructureTargetIso` as the original
trace. The affine Hom supplier proves bijectivity of this actual map;
it does not introduce a separately selected comparison. The source model
and `coefficientShiftIso` retain the original `I_R.ι'` augmentation.

The algebraic half uses `coinductionComplexIso`, native homology under
restriction, and the additive map underlying the original
`moduleHomologyDerivedLinearEquiv`. Its underlying forward and inverse
functions are those of `moduleHomologyDerivedAddEquiv`. The original
dual factorization and `homologyFunctorFactors` identify its source with
native homology of `D_J(C_A)`. These are the maps in
`normalSurfaceCohomologyModelAddEquiv` and
`normalSurfaceDualModelAddEquiv`.

The A-action is checked on the original source maps. The scalar lift of
`a • id_OX` is `a • id` on the supplied resolution itself. Ordinary
global sections carry it to `a • id_C_chain`, and original model
naturality identifies its actual derived action. Native coinduction
carries the intrinsic A-scalar on Hom-complex homology to precomposition
by that same restricted chain map. The two scalar equations prove
`normalSurfaceCohomologyDualLinearEquiv` A-linear. No A-action is installed
on an intermediate R-derived Hom group and no general linearity of the
whole right-derived sections functor is assumed.

The ring map sigma and the actual triangle
`i ≫ toSpec = g ≫ Spec.map sigma` are preserved. The trace leaf derives
the structural compatibility from this triangle. The intended finite
injective local map is used unchanged; additional finite-normal ring
conditions enter the regular-source coefficient normalization for the
degree-zero trace consumer.

The degree-zero trace/unit comparison requires two further normalizations:
identification of the geometric comparison with section-level Phi0 under
H0/sections, and identification of `coinducedRegularHomologyZeroIso` with the
original functional after `coinducedRegularHomAugmentation` and `I_R.ι'`.
The [unit-trace module](Cohomology/UnitTrace.md) supplies these original-map
identities. The A-linear equivalence alone is not the trace/unit identity.

The separate shared `HomComplex/Cohomology/Derived` bridge is used for
native chain-source naturality and supplies unrestricted derived-arrow
naturality to the original unit/Postnikov consumers. This leaf does not
replace the original Postnikov boundary delta, assert an
embedding-independent proper/finite trace identity, or conclude GR
vanishing.

The source fixes the original structure unit as an object of
`X.Modules` through the transparent `normalSurfaceUnit` abbreviation. Its
finite-presentation fact comes from the native free module on one generator;
it does not assert that the canonical module is free or invertible. Native
homology isomorphisms, Ext carriers, shifts and resolution maps are typed
before categorical pasting. The coinduction scalar proof and final linear
upgrade are proved on generic constructor data before specialization. The
common R-derived Hom group receives no new A-action.

Original concentration conditions and the geometric triangle `hg` are
retained where the comparison uses them. No map-compatibility assumption or
replacement Serre, trace or model map is introduced. The degree-zero
normalizations and Grauert–Riemenschneider vanishing have separate consumers.

The affine Hom value and source-precomposition calculations use the original
inclusions, functor map, bijectivity proof and source/target isomorphisms.
The concrete comparison fixes the original composition isomorphism endpoints
before specialization; its forward and inverse maps retain those factors.

The coinduction scalar calculation uses a compact function proven equal to
the existing comparison through the original class-value identity.
Resolution unit and coefficient naturality, scalar conjugation, and mapped
commuting squares are proved generically before the concrete sheaf data are
supplied. The Serre composite uses its two original source-naturality
equations. The canonical cohomology module instance and the supplied IR
parameter are retained explicitly at the final model construction.

No compatibility premise, replacement coefficient, source model or canonical
invertibility is introduced.

The native resolution comparison arrows now receive their full-derived
endpoints before generic functorial composition is applied. The affine Hom
calculation uses the actual left-associated `Linear.homCongr` value. The
restricted scalar model uses three native commuting squares, pasted before
specializing their concrete geometric objects. The final scalar proof fixes
the original derived scalar as an endomorphism of literal
`moduleDerivedStructure`, and transports the two original scalar equations
through a generic source square.

The coinduction comparison is represented by
`normalSurfaceIsoAddEquivOfValue`. Its forward function is the compact value
already identified by the original class/localization theorem; its
inverse is literally the inverse of the original composite linear
equivalence. The generic theorem `normalSurfaceIsoAddEquivOfValue_eq` proves
that this constructor is the same original composite before supplying
concrete homology objects. Consequently the concrete coinduction value
equation is definitional and no second expanded whole-function comparison
is required. The internal function identity is discharged from the original
provider, not assumed from the geometric consumer.

The final geometric comparison retains its concentration conditions and
original structure triangle. Degree-zero unit normalization and the
chosen-embedding Grauert–Riemenschneider theorem belong to their separate
consumer modules.
