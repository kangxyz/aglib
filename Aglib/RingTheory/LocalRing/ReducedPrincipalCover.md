# Reduced principal covers on normal local surfaces

The source contains `IsLocalRing.exists_reduced_principal_cover hdim a ha0 hna`.
For a Noetherian normal local domain `R` of dimension two and a nonzero nonunit
`a`, its conclusion is an actual `c` satisfying

```text
c ≠ 0, c ∈ maximalIdeal R, IsReduced (R ⧸ Ideal.span {c}),
and ∃ r : ℕ, 0 < r ∧ a ∣ c^r.
```

There is no Nagata, completeness, unique-factorization, coefficient-field,
resolution or rationality hypothesis. The assertions concern the
ring-theoretic reduced-principal-cover construction.

`exists_stable_parameter_pair` completes `a` to a parameter pair `(a,g)` and
chooses a positive `N` such that `(a+h,g)=(a,g)` and `a+h≠0` for every
`h∈m^N`. The proof retains the original ideals and uses the unit `1+s` in the
explicit perturbation formula. The existing principal-cokernel associativity
formula gives `principal_minimalPrimes_card_le_parameter_length`: the number
of actual minimal primes of `(f)` is bounded by the length of `R/(f,g)`.
Normality makes `g` regular on `R/(f)` through the principal associated-prime
height theorem. Each localized minimal-prime weight and each prime-factor
parameter quotient length is positive. The original parameter quotient
therefore supplies a fixed bound for the stable family.

Finite prime avoidance constructs an element of each height-one prime outside
its second symbolic power and the other primes in the finite list. The second
symbolic power is the actual comap of the square of the maximal ideal in the
canonical prime localization. Another avoidance argument supplies a multiplier
in `m^N` outside all those primes. Their product is an actual perturbation
which makes the equation belong to each old prime but not its symbolic square.
`Nat.findGreatest` chooses a maximal prime count in the bounded family;
the retained-prime inclusion and the cardinal inequality exclude extra primes.

In each height-one DVR, the resulting equation generates the maximal ideal;
outside its divisor support it is a unit. The existing normal height-one
intersection theorem yields reducedness of the original principal quotient.
The unchanged parameter ideal gives `c≠0` and `c∈m`. Membership in every
original minimal prime over `(a)` gives `c∈radical(span {a})`, hence divisibility
of a positive power by `a`. This last step uses the original radical and
requires no factorization in `R`.

The mathematical route follows Stacks Project, Lemmas 15.127.4–6, tags
[0BWV](https://stacks.math.columbia.edu/tag/0BWV),
[0AXH](https://stacks.math.columbia.edu/tag/0AXH), and
[0AXI](https://stacks.math.columbia.edu/tag/0AXI), with the parameter-length
input [0BWT](https://stacks.math.columbia.edu/tag/0BWT). The nonzero witness
from 0AXH is retained in the endpoint.

The current consumer is the uniform fixed-scalar torsion argument for original
`H¹(X,O_X)` on normal proper birational surface models. The actual total-divisor
comparison through its proper transform is a separate B1 geometric obligation;
this ring theorem does not assert that uniform cohomological bound.
