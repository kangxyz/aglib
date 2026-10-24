# An actual finite complete regular subring in dimension two

`IsLocalRing.exists_finite_complete_regular_subring` constructs an actual
finite injective local ring map R→A whenever A is a complete Noetherian
local domain of Krull dimension two. The source R is a complete regular
local domain of dimension two. No normality, excellence, perfect-residue,
finite p-basis, or separability assumption is imposed on A.

The source is literally the maximal-adic completion of a localized
polynomial ring. A private `ParameterSource` record retains that ring,
its proved regularity and dimension, the actual map to A, the exact
maximal-radical equation, and surjectivity of the original residue
composite. This record is constructed in every characteristic case;
its existence is not a hypothesis of the public theorem.

The common construction starts with a PID domain D, an irreducible
element t, and an actual map f:D→A such that its residue composite is
surjective and has kernel (t). Choose x in maximalIdeal A so that
(f(t),x) has radical maximalIdeal A. Evaluate D[X] at x and let q be
the literal kernel of its original residue point. This point is the
coefficient residue point composed with polynomial constant coefficient.
It is surjective, so q is maximal, and

```text
q = Ideal.span {Polynomial.C t} ⊔ Ideal.span {Polynomial.X}.
```

This equality is proved by the actual split constant-coefficient map,
native ideal map/comap formulas, and `Polynomial.ker_constantCoeff`.
An element outside q has nonzero residue after evaluation, hence is
a unit in A. This verifies the actual localization-lift unit condition.
The resulting map from B=Localization.AtPrime q extends precisely the
original evaluation. Its extended maximal ideal is exactly (f(t),x).

D is a regular ring because it is a PID domain. Native polynomial
regularity makes B regular local. The maximal ideal ker(D→ResidueField A)
has height one, and q lies over this actual ideal. Native
`Polynomial.height_eq_height_add_one` gives ht(q)=2, and the native
prime-localization dimension equality gives dim(B)=2.

In equal characteristic, the existing coefficient-section theorem gives
the actual section k=ResidueField A→A. Choose a nonzero element a in
maximalIdeal A and use `ParameterIdeal` to complete it to (a,x) with
maximal radical. Take D=k[T], t=T, and evaluate T at a. Its residue
point is exactly constant coefficient, with kernel (T). The generic
construction therefore uses the actual iterated polynomial ring
k[T][X] and its original parameter point. Algebraic independence of
a and x is not assumed; injectivity is proved later from dimension.

In mixed characteristic, the existing `CohenMap` theorem constructs the
actual complete Cohen DVR C→A with the original natural p as uniformizer
and surjective residue composite. The original point has kernel (p).
The actual parameter-pair theorem completes p:A to (p,x). Taking D=C
and t=p supplies the same generic polynomial/localization construction.

The native characteristic dichotomy for domains supplies the exhaustive
cases: positive characteristic of A, characteristic zero of both A and
its residue field, and characteristic zero of A with positive residue
characteristic. Thus the argument includes arbitrary imperfect residue
fields in equal and mixed characteristic.

Finally define R=AdicCompletion (maximalIdeal B) B. The original
completion map and cofinal ideal-power comparison give its actual map
to A, with the original B→A equation retained by
[CompleteParameterMap](../AdicCompletion/CompleteParameterMap.lean).
That module proves the resulting map finite from its literal residue
point and parameter ideal, local from its actual maximal-ideal image,
and injective from integral incomparability and the nonzerodivisor
dimension drop. Existing completion theorems preserve regularity,
dimension two, and maximal-adic completeness.

The current normalization consumer is
[CompleteLocalSurface](../Nagata/CompleteLocalSurface.lean). It installs
the actual scalar action from this constructed finite map, applies
regular-local normality and the complete normal-surface Nagata theorem
to R, then uses finite ascent to reach the original A. The construction
here supplies the finite regular source without requiring A to be
normal or its normalization to be finite.
