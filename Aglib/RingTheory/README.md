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
| [GenericFreeness](GenericFreeness/README.md) | Free localizations from filtrations; generic freeness of finite modules over finite-type algebras over a Noetherian domain (Stacks 051R) |
| [Grassmannian](Grassmannian/README.md) | Charts and Zariski descent of Mathlib's `Module.Grassmannian.functor`, with the base-change formula class `BaseChangeMkQFormula` |

[Generic exact-sequence length](Length/README.md), [scalar homology](ScalarHomology/README.md), fraction and filtration calculations belong to their lower object owners; the multiplicity proofs consume them. No Grayson cycle, principal-face, curve or K/G/Q/S application object is introduced. Scheme smooth/stalk/connectedness results consume the regular-local, polynomial and tensor-domain leaves; other admitted interfaces remain available as public standalone results.

The Milnor norm prerequisites also include actual root-field branch/tensor
comparisons, complete DVR extensions, integral-closure towers and determinant
norm/valuation formulas. They retain their native algebraic namespaces and
explicit finite, flat, irreducible, ramification and scalar-tower hypotheses.
[Adic completion](AdicCompletion/README.md) and
[finite-algebra length](FiniteLength/README.md) describe the lower interfaces.
