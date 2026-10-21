# Idempotents in finite algebras over a Henselian local ring

[FiniteAlgebraIdempotents.lean](FiniteAlgebraIdempotents.lean) proves
`HenselianLocalRing.exists_idempotent_lift_of_finite`:

```text
R commutative Henselian local, A a finite commutative R-algebra,
I = (maximalIdeal R).map (algebraMap R A),
e0 ∈ A/I idempotent
  ⇒ ∃ e ∈ A, e idempotent and Ideal.Quotient.mk I e = e0.
```

The actual algebra, quotient ideal and quotient homomorphism are retained.
The finite algebra need not be étale, flat, reduced, local or nontrivial.
There is no Noetherianity or completeness assumption on the base.

The supporting theorem `exists_etale_retraction_comap` starts with an actual
étale `R`-algebra `T` and a prime `P` over the maximal ideal for which the
native residue-field map is bijective. It produces `ρ : T →ₐ[R] R` with
`(maximalIdeal R).comap ρ.toRingHom = P`. The residue-valued point comes from
the inverse residue-field equivalence; [residue_comp_bijective_of_etale](Etale.lean)
lifts it to the same original base ring.

The finite-algebra theorem applies Mathlib's proved
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`
from `Mathlib/RingTheory/Etale/QuasiFinite.lean`. That theorem supplies such
an étale neighborhood and complete orthogonal idempotents in `T ⊗[R] A`
which separate the primes over `P`, with one extra idempotent vanishing on
that fibre. Evaluation along `ρ` maps this family to actual orthogonal
idempotents of `A`.

Choose a preimage `a ∈ A` of the prescribed `e0`. Sum those evaluated
idempotents whose corresponding fibre prime does not contain `a`. For every
prime of `A/I`, its inverse image in `A` lies over the maximal ideal. Its
further inverse image under tensor evaluation therefore lies over `P`, so
the splitting theorem identifies the unique contributing component. The sum
and `e0` have the same basic open in `Spec (A/I)`. The injectivity of basic
opens on idempotents gives their exact equality in the quotient.

This construction does not assume Henselianity of `A` at `I`, a finite-algebra
lifting family, or an equivalence of cover categories. It provides the
finite-algebra step for the separate proper-residue graph-lifting route.
It does not identify global functions modulo the maximal ideal with global
functions on a proper scheme's actual closed fibre. The separate
[proper-residue fullness construction](../../AlgebraicGeometry/Morphisms/FiniteEtale/ProperResidue/Fullness.md)
uses finite cohomology to lift the needed clopen patches for proper flat
models over a Henselian DVR.
