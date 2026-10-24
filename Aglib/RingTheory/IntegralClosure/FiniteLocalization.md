# Finite normalization from the maximal localizations

`integralClosure.finite_of_normal_away_of_finite_atMaximal R K f hf hlocal`
proves finiteness of the literal `integralClosure R K` over R. Its inputs
are a Noetherian domain R, its supplied fraction field K, a nonzero f
whose literal `Localization.Away f` is integrally closed, and finiteness
of the literal normalization of every maximal localization in K.
There is no dimension bound in this patching theorem.

The original R→K action is retained. The public map
`integralClosure.atPrimeFractionMap R K p` constructs the actual
R-algebra map R_p→K by localization. Elements outside p are nonzero
and therefore map to units of K. The local finiteness hypothesis uses
the algebra structure induced by this specific map. It does not choose
another field or supply a finite model of the global normalization.

Write N for the original normalization. Normality of R[1/f] places N
inside the image of R[1/f]→K: each original integral equation remains
integral after extending coefficients, and the actual fraction-field
localization map supplies the comparison. Every x in N therefore has
some f-power denominator.

The private filtration consists of the actual submodules

```text
N_n = {x ∈ N : f^n • x lies in the original image of R in N}.
```

Multiplication by f^n injects N_n into that finite image of R.
Noetherianity of R makes every N_n finite. The filtration is increasing
and exhaustive. It has the exact recurrence

```text
x ∈ N_(n+1) ↔ f • x ∈ N_n.
```

Consequently one-step stabilization forces all later stabilization:
if N_n=N_(n+1), then f*x in N_n puts x in N_(n+1), and the same argument
propagates to every later denominator bound. Exhaustivity then gives
N=N_n.

The successive quotient is implemented as the image of N_(n+1) in
N/N_n. It is finite, so its support is closed. Its complementary open
locus is characterized directly by clearing actual local denominators:
every x in N_(n+1) has a scalar outside the prime carrying it into N_n.
The recurrence proves these open loci increase with n.

At a maximal ideal m, the original `scalarExtensionHom` from
[Localization](Localization.lean) identifies the literal local
normalization in K with the localization of N as a module. Localizing
the same filtration commutes with its increasing supremum. Finite
generation of that actual localized normalization gives a finite stage
containing all its generators. The localized-module fraction equations
then clear a common scalar for each element of the successive quotient.
Thus some stabilization open contains m. Generization gives a cover of
the whole prime spectrum, and quasi-compactness gives a finite subcover.
A single largest index has zero successive quotient globally, so the
one-step argument proves that N itself is finite.

The statement is the reverse implication of
[Stacks, Lemma 10.161.15 (0333)](https://stacks.math.columbia.edu/tag/0333).
This proof uses finite denominator quotients and their support. General
normal-locus openness, excellence, J-2, and finite-type Nagata stability
are not premises of the module.

The current consumer is bounded rational adjunction. For a normal domain
E and an actual t=b/a in its fraction field, a≠0 gives
E[t][1/a]=E[1/a] under the original inclusions. The same denominator
persists after the specified normal splitting extension. This supplies
the normal principal open, while
[AdicCompletion/Normalization](../AdicCompletion/Normalization.lean)
supplies local finiteness after reducedness of the actual local
completions and their dimension bound have been proved. The
[Nagata rational-adjunction theorem](../Nagata/RationalAdjunction.md)
constructs those local inputs under its own dimension-two Nagata
hypotheses; the present local-to-global criterion retains them explicitly.
