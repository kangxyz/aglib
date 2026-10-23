# Associated primes under flat base change of a finite module

Import `Aglib.RingTheory.Ideal.AssociatedPrime.FlatBaseChange`.

Let R be Noetherian, S a flat commutative R-algebra, and M a finite
R-module. `IsAssociatedPrime.exists_quotient_of_flat_tensorProduct`
starts with an actual associated prime q of the S-module `S ⊗[R] M`.
It produces an ideal p of R with all three properties:

- p is associated to M;
- p is exactly `q.comap (algebraMap R S)`;
- q is associated to the original S-module
  `S ⧸ p.map (algebraMap R S)`.

This is the inclusion needed from
[Stacks, Lemma 10.65.3 (0312)](https://stacks.math.columbia.edu/tag/0312)
for finite M. Finiteness of M remains an explicit hypothesis. The result
does not implement the arbitrary-module directed-union argument.
Noetherianity of S is unnecessary in this implementation.

The proof has three parts. First,
`IsAssociatedPrime.maximalIdeal_of_isBaseChange_of_flat_local` treats a
flat local algebra R -> S and an original map `f : M →ₗ[R] N` with
`IsBaseChange S f`. If the maximal ideal of R were not associated to M,
finite prime avoidance would supply an element of that ideal regular on
M. Flat base change preserves its regularity on N. Its image belongs to
the maximal ideal of S, so an associated radical-annihilator witness
would make a power of it annihilate a nonzero element. This contradiction
uses no Noetherianity of S.

Second, `IsAssociatedPrime.comap_of_isBaseChange_of_flat` derives
contraction for arbitrary actual primes q. It uses
`Localization.localRingHom` for R_p -> S_q, where p is the actual
contraction. The original R-actions on the localizations are retained,
and the commuting coefficient square is proved by
`Localization.localRingHom_to_map`. Localized flatness is derived from
the original flat algebra.

The module map M_p -> N_q is the lift of the original composite M -> N
-> N_q through M -> M_p. The native `IsBaseChange.comp`, `lift_comp`, and
`of_comp` theorems prove that this same map gives scalar extension to
S_q. Associated-prime localization transports the local result back to
the original p. No associated-prime lifting property is added as an
unproved hypothesis.

Finally, a finite prime filtration of M gives a filtration after flat
tensoring. Associated primes of the middle term of an exact sequence
belong to the union of those of its outer terms. Consequently q is
associated to one prime-quotient factor. The native S-algebra equivalence

```text
S ⧸ p.map (algebraMap R S) ≃ₐ[S] S ⊗[R] (R ⧸ p)
```

is `Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p`. Its maps are
the original quotient and tensor maps. Contraction applied to R/p
identifies the filtration prime with q's actual contraction; contraction
applied to M proves it is associated to M.

The current consumer is the associated-prime criterion for reducedness
of the actual completion in the bounded Nagata surface argument, with
M the original principal quotient. To apply this theorem there, the
caller must still identify the actual completed quotient with its tensor
base change. Ambient regularity at the contracted associated prime,
reducedness of the completed prime quotient, and the local uniformizer
argument remain separate premises and proofs. This module supplies no
normalization finiteness, completion normality, F2 coefficient theorem,
or arbitrary finite-type Nagata stability.
