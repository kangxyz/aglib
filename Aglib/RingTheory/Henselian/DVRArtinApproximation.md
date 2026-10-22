# Artin approximation over DVRs

These interfaces concern a domain discrete valuation ring and the actual
Henselizations of local rings of finite-type algebras over it. They also give
approximation directly in an original Henselian DVR. The excellent variants
use standard excellence; the separate characteristic-zero variants require
no excellence hypothesis.

## Geometric local rings

Let `R : Type u` have `CommRing R`, `IsDomain R` and
`IsDiscreteValuationRing R`. Let `B : Type v` be a commutative finite-type
`R`-algebra, let `q : Ideal B` be prime, and put

```text
H = Henselization (Localization.AtPrime q).
```

The source algebra `B` may have zero divisors and need not be flat or smooth
over `R`. The prime may lie over either the generic or the closed point of
`R`. The universes `u` and `v` are independent.

Import [DVRGeometricLocalArtinApproximation](DVRGeometricLocalArtinApproximation.lean)
for
`GeometricLocalHenselization.exists_solution_ideal_completion_with_precision_of_charZeroDVR`.
It adds `CharZero R` to the hypotheses above. In particular it does not assume
characteristic zero or perfectness of the residue field.

Import
[ExcellentDVRGeometricLocalArtinApproximation](ExcellentDVRGeometricLocalArtinApproximation.lean)
for
`GeometricLocalHenselization.exists_solution_ideal_completion_with_precision_of_excellentDVR`.
It instead takes the explicit standard excellence hypothesis
`hexcellent : IsExcellentRing.{u, e} R`. This theorem does not require
`CharZero R`.

Both results apply to every proper ideal `I : Ideal H`, every finite
polynomial system with coefficients in the actual `H`, and an exact formal
solution in the native `AdicCompletion I H`. The unknown type `σ : Type w`
and equation type `ι : Type t` need only have `Finite σ` and `Finite ι`;
their universes are independent of each other and of the coefficient rings.
For every `c : ℕ`, they return `x : σ → H` with all three conclusions:

```text
∀ i, MvPolynomial.eval x (F i) = 0

∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)

∀ j, algebraMap H (AdicCompletion I H) (x j) - y j ∈
  (I ^ c).map (algebraMap H (AdicCompletion I H)).
```

Thus both the quotient equation and the ideal-power error use the original
ideal, canonical coefficient map and completion. No supplied approximation
solver, finite local model, cofinality bound or chosen completion equivalence
is a premise of either public theorem.

## Original Henselian DVRs

Now let the original coefficient ring additionally have
`HenselianLocalRing R`. The exact root can be taken in this same `R`, with
`I : Ideal R`, `y : σ → AdicCompletion I R` and both original precision
conclusions above with `H` replaced by `R`.

Import [HenselianDVRArtinApproximation](HenselianDVRArtinApproximation.lean)
for
`HenselianLocalRing.exists_solution_ideal_completion_with_precision_of_charZeroDVR`.
It requires `CharZero R` and no excellence hypothesis.

Import
[ExcellentHenselianDVRArtinApproximation](ExcellentHenselianDVRArtinApproximation.lean)
for
`HenselianLocalRing.exists_solution_ideal_completion_with_precision_of_excellentDVR`.
It instead takes `hexcellent : IsExcellentRing.{u, e} R`. No separate
coefficient-completion or stability premise is required.

[HenselianNativeGeometricEquiv](HenselianNativeGeometricEquiv.lean) constructs
the actual equivalence between `R` and the Henselization of its localization
at its original maximal ideal. The native-ring results transport the
geometric theorem through this equivalence and return the solution and both
precision conditions to the original `R` and `I`.

## Coefficient condition and construction

The reusable intrinsic intermediate theorem is in
[DVRGeometricApproximation](DVRGeometricApproximation.lean). Its explicit
coefficient premise
`AdicCompletion.HasGeometricallyReducedFractionCompletion R` says that the
fraction field of the actual maximal-adic completion is geometrically reduced
over the original `FractionRing R`, under the canonical lifted coefficient
action. It is a geometric field-extension condition, not an approximation
or desingularization assumption.

[Excellent/Defs](../Excellent/Defs.lean) defines the standard G-ring,
quasi-excellent and excellent predicates from regular completion maps, J-2
and universal catenarity. The auxiliary universe `e` in
`IsExcellentRing.{u,e} R` records finite-type test algebras in
`Type (max u e)`; no invariance under changing that universe is assumed.
[Excellent/DiscreteValuationRing](../Excellent/DiscreteValuationRing.lean)
proves the intrinsic coefficient condition from the G-ring component of
excellence. Characteristic zero supplies it separately through perfectness
of the original fraction field. These are proofs of the condition, not extra
premises added to the excellent or characteristic-zero endpoints.

For a generic prime, the construction uses the actual fraction-base
localization and the existing [field theorem](GeometricLocalArtinApproximation.md).
For a vertical prime, it constructs residue parameters, a parameter DVR and a
finite local model over its polynomial-origin Henselization. The model and
its coefficient ring share an internal common universe; this does not impose
an equality of the original universes of `R` and `B`. Polynomial-origin
approximation and the shared finite-local transfer supply the root, and the
actual ring and completion equivalences preserve both precision equations.
The uniformizer and model are constructed internally.

These statements cover DVRs and the specified geometric local
Henselizations. They do not assert Artin approximation for arbitrary
excellent Henselian local rings or a general Popescu theorem.
