# Descent of finite integral closure

Import `Aglib.RingTheory.IntegralClosure.FiniteDescent`.

`integralClosure.finite_of_finite_extension R S K L` starts with a finite
commutative algebra R -> S, Noetherian R, and fields K and L. The original
coefficient maps form the compatible towers R -> K -> L and R -> S -> L.
The field map K -> L is injective. No injectivity of R -> S, R -> K, or
S -> L is required.

The upper integral closure must already be finite:

```text
Module.Finite S (integralClosure S L).
```

The conclusion is finiteness of the literal lower integral closure:

```text
Module.Finite R (integralClosure R K).
```

All rings and fields lie in the same ambient universe. R and S need not
be domains, and K and L need not be their fraction fields. No normality,
separability, locality, completeness, dimension bound, or Japanese
predicate is assumed. Noetherianity of S need not be supplied.

The proof restricts the finite upper integral closure to a finite R-module.
The original K -> L algebra map sends an element integral over R to an
element integral over R in L. The existing
[`scalarExtensionHom`](Localization.md) then includes it in the integral
closure of S in L, without changing its ambient value. This gives an
injective R-linear map from the lower closure to a finite R-module.
Noetherianity of R supplies finite generation of its image.

When R and S are domains and K and L are their compatible fraction fields,
the literal integral closures are normalizations. This specializes to
the N-1 descent assertion of
[Stacks, Lemma 10.161.7 (032K)](https://stacks.math.columbia.edu/tag/032K).
The source also states Japanese descent; that additional N-2 assertion is
not supplied here. The proof reuses the actual integral-closure maps and
Noetherian submodule theorem. It does not introduce a new normalization
predicate or replace the upper finiteness premise by a normality premise.

The current consumer is descent from a finite splitting normalization in
the bounded rational-adjunction argument for surface charts. That argument
must first establish finiteness of the upper closure by its separate
analytic and completion results. This lemma does not discharge those
premises or the missing nonnormal complete-surface normalization theorem.
