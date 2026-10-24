# Commutative algebra

The objects are actual Mathlib rings, algebras, ideals, prime spectra, localizations and modules. Declarations use their native mathematical owners, including `Algebra`, `Ideal`, `Module`, `Localization`, `IsLocalRing`, `IsRegularLocalRing` and `IsIntegrallyClosed`.

| Subject | Main results and interfaces |
| --- | --- |
| [Descent](Descent/README.md) | Effective coaction/equalizer reconstruction, actual algebra maps, nilpotent overlaps and finite fields of definition |
| [TensorProduct](TensorProduct/README.md) | Tensor domains over algebraically closed fields, flat equalizer base change and purely inseparable overlap kernels |
| [RegularLocalRing](RegularLocalRing/README.md) and [LocalRing](LocalRing/README.md) | Regular-local domain/normality, scalar-regular parameters, parameter quotients and prime avoidance |
| [KrullDimension](KrullDimension/README.md) | Integral/going-down heights, polynomial local rings and principal-open dimension bounds |
| [IntegralClosure](IntegralClosure/README.md) | Faithfully flat descent of integral closedness between domains |
| [FiniteLength](FiniteLength/README.md), [Support](Support/README.md) and [Localization](Localization/README.md) | Finite length from maximal support, localized minimal support and actual scalar/localized-length comparisons |
| [PrimeFiltration](PrimeFiltration/README.md) and [Multiplicity](Multiplicity/README.md) | Prime cyclic filtrations, local occurrence counts and finite-scalar-homology Euler formulae |
| [Finiteness](Finiteness/README.md) | Finite middle modules in exact pairs with a finite source and Noetherian target, without surjectivity |
| [Spectrum](Spectrum/README.md) | Open residue-fibre surjectivity, upper semicontinuity of finite-module fibre dimension and local constancy under finite-presentation flatness |
| [Ideal/MinimalPrime](Ideal/MinimalPrime/README.md), [Flat](Flat/README.md), [MonoidAlgebra](MonoidAlgebra/README.md), [RootsOfUnity](RootsOfUnity/README.md), [Smooth](Smooth/README.md), [Etale](Etale/README.md) | Actual minimal-prime, flat-module, finite-type monoid algebra, root-adjoin, reducedness and formal-etale ring-map prerequisites |
| [FittingIdeal](FittingIdeal/README.md) | Fitting ideals of finitely generated modules: presentation independence, base change, stalkwise freeness criteria and fibre-rank strata |
| [PicardGroup](PicardGroup/README.md) | Actual invertible-module lifting and bijectivity of the original ring Picard map across a surjective square-zero extension |
| [GenericFreeness](GenericFreeness/README.md) | Free localizations from filtrations; generic freeness of finite modules over finite-type algebras over a Noetherian domain (Stacks 051R) |
| [Grassmannian](Grassmannian/README.md) | Charts and Zariski descent of Mathlib's `Module.Grassmannian.functor`, with the base-change formula class `BaseChangeMkQFormula` |

[Binomial](Binomial.lean) holds integer facts about Mathlib's `Ring.choose`: Pascal's rule in
difference form, `0 ≤ C(y, i) ≤ yⁱ` for `y ≥ 0`, and the integration of a binomial forward
difference (`Int.eq_sum_choose_of_fwdDiff`); the Hilbert-function and Mumford-bound leaves of
`AlgebraicGeometry/Cohomology/Projective` consume them.
[Binomial/Uniqueness](Binomial/Uniqueness.lean) proves that binomial coefficients are unique:
`Int.eq_of_forall_sum_mul_choose_eq`; the Hilbert-scheme regularity bound consumes it.

[TrivSqZeroExt](TrivSqZeroExt.lean): Mathlib's trivial square-zero extension `R ⊕ M` is local for
local `R` (`TrivSqZeroExt.isLocalRing`, with the local projection `TrivSqZeroExt.isLocalHom_fstHom`)
and Noetherian for Noetherian `R` and finite `M` (`TrivSqZeroExt.isNoetherianRing`). The
tangent-space leaf [Picard/Tangent/Points](../AlgebraicGeometry/Picard/Tangent/Points.lean) uses
them for the test schemes `Spec L[ε]` and `Spec L[ε, ε']`.

[Generic exact-sequence length](Length/README.md), [scalar homology](ScalarHomology/README.md), fraction and filtration calculations belong to their lower object owners; the multiplicity proofs consume them. No Grayson cycle, principal-face, curve or K/G/Q/S application object is introduced. Scheme smooth/stalk/connectedness results consume the regular-local, polynomial and tensor-domain leaves; other admitted interfaces remain available as public standalone results.

The Milnor norm prerequisites also include actual root-field branch/tensor
comparisons, complete DVR extensions, integral-closure towers and determinant
norm/valuation formulas. They retain their native algebraic namespaces and
explicit finite, flat, irreducible, ramification and scalar-tower hypotheses.
[Adic completion](AdicCompletion/README.md) and
[finite-algebra length](FiniteLength/README.md) describe the lower interfaces.

Focused incoming algebra guides are [AdjoinRoot](AdjoinRoot/README.md),
[FiniteType](FiniteType/README.md), [Polynomial](Polynomial/README.md),
[DiscreteValuationRing](DiscreteValuationRing/README.md) and
[localization away from an element](Localization/Away/README.md).
Their ring maps, chosen fraction fields, finite-type and local hypotheses remain
explicit; the guides do not replace those inputs by geometric assumptions.

Focused interface guides: [Derivations on actual fraction fields](Derivation/README.md).

[Excellence](Excellent/README.md) defines the standard G-ring, J-2 and
universal-catenarity conditions, with the finite-type test universe explicit.
Its DVR formal-fibre projection supplies the intrinsic completed-fraction
condition used by [DVR Artin approximation](Henselian/DVRArtinApproximation.md).
The public endpoints cover characteristic-zero or standard-excellent domain
DVRs, arbitrary finite-type algebras and their actual geometric local
Henselizations; an original-ring endpoint additionally assumes Henselianity.
The field-origin results and the other completion interfaces retain their
separate hypotheses.

The algebraic construction uses actual parameter coordinates:
[Generators/Parameters](Extension/Generators/Parameters.lean) absorbs
coordinates from the coefficient algebra, and
[Generators/RetainedFittingEquality](Extension/Generators/RetainedFittingEquality.lean)
retains the evaluated Fitting ideal for the selected original relations.
[Kaehler/SeparatingBasis](Kaehler/SeparatingBasis.lean) constructs the
differential basis over the displayed separating rational function field;
[Kaehler/GenericFittingNonzero](Kaehler/GenericFittingNonzero.lean) derives
nonvanishing from the separably generated generic fraction extension and
injective evaluation. These interfaces keep their actual scalar actions
and presentations. [Nilpotent/GeometricallyReduced](Nilpotent/GeometricallyReduced.lean)
tests geometric reducedness on finite field extensions in the base universe,
with the other algebra in an independent universe.

[Pure degree-p differential trace](Kaehler/PureDegreePTrace.md) constructs the
original one-form trace for a monic presentation `X^p-a` in prime
characteristic, with its original base-change and localization equations.
[Presentation](Kaehler/PureDegreePTrace/Presentation.md) computes the actual
relative differential decomposition, and
[Exterior](Kaehler/PureDegreePTrace/Exterior.md) extends the trace to positive
exterior degrees with the original wedge normalization. These allow arbitrary
coefficient towers, including characteristic two; smoothness, finite p-rank
and nonzero `da` are not substituted for the explicit presentation. The
surface differential comparison remains a geometric consumer.

[Finite coefficient expansion](MvPowerSeries/FiniteCoefficientExpansion.md)
constructs an actual two-variable power-series basis over the original
coefficient map followed by nonzero variable expansion. It retains a finite
coefficient-field basis and requires no characteristic hypothesis. The
pure degree-p completion application must supply its actual coefficient
family; this module does not construct an arbitrary Cohen presentation.

[BasisOfDerivations](Kaehler/BasisOfDerivations.md) constructs a basis of the
ordinary algebraic Kähler module from finitely many actual algebra generators
and derivations dual to them. Its basis values are the original universal
differentials and its coordinates on `d a` are those derivations at `a`;
generation and duality are genuine inputs, without a smoothness or freeness
assumption. [Expanded-series derivation](MvPowerSeries/FiniteCoefficientExpansion/Derivation.md)
extends an actual coefficient-field derivation coefficientwise to two-variable
series and makes it a derivation over the original nonzero-expanded series
scalar map. It retains the given field algebra, kills both spatial variables
and needs no characteristic or continuity hypothesis. The differential-basis
consumer must still supply algebraic generation and the spatial derivations;
the full field/series rank conclusions and fixed-family applications remain
separate obligations.
