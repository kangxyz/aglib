# Complete normal local surfaces are Nagata

Import `Aglib.RingTheory.Nagata.CompleteSurface`.

`IsNagataRing.of_complete_local_normal_dimLE_two` proves
`IsNagataRing.{u, v} R` for a commutative Noetherian normal local domain
`R : Type u` that is complete for its maximal ideal and has Krull dimension
at most two. The auxiliary test universe v is arbitrary and explicit.

The proof applies the
[prime-quotient normalization theorem](../IntegralClosure/CompleteSurface/PrimeQuotient.md)
to every actual quotient `C = R ⧸ p`, using exactly
`K = FractionRing C`. For every finite extension field L in
`Type (max u v)`, with its original C-action and scalar tower through K,
that theorem supplies

```text
Module.Finite C (integralClosure C L).
```

This is the Japanese condition on C. Together with the original
Noetherianity of R, it proves the
[Nagata definition](Defs.md) directly. The proof does not choose a new
finite algebra in place of the integral closure, transport L to a
different field, or assume separability.

The prime-quotient supplier handles p=0 by normality and the
complete-surface normalization theorem. For p nonzero, the quotient has
dimension at most one and the complete-curve theorem applies even when
that quotient is not normal. The current theorem consumes those proved
cases without repeating their dimension or completeness arguments.

This closes the definition bridge for the original complete normal local
ring. It does not prove that every complete Noetherian local ring is
Nagata, nor finite-type or localization stability. In particular the
normalization of a finite-type graph or blowup algebra still requires the
separate stability and scheme-normalization results. The classical
finite-type equivalence is
[Stacks, Proposition 10.162.15](https://stacks.math.columbia.edu/tag/0334);
it is not used as an assumption in this proof.
