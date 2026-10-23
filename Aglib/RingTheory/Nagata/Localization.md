# Japanese and Nagata localization

Import `Aglib.RingTheory.Nagata.Localization`.

The predicates are the existing `IsJapaneseRing.{u, 0}` and
`IsNagataRing.{u, 0}`. All rings and tested extension fields lie in `Type u`;
no invariance under changing the auxiliary test universe is assumed.

`IsJapaneseRing.of_isLocalization M h` proves that a domain S which is
an actual localization of a Japanese domain R at M is Japanese. The
localization algebra is supplied by `[Algebra R S] [IsLocalization M S]`.
No Noetherianity, normality, completeness, or separability premise is used.
The domain hypothesis on S includes nontriviality; it rules out localizing
a domain at a multiplicative set containing zero.

Given an original finite extension L of `FractionRing S`, the proof regards
that same fraction field as a fraction field of R. Indeed, localizing R at
M and then at the nonzero elements of S inverts exactly the nonzero elements
of R. Injectivity of R -> S is derived from the localization and domain
hypotheses. The canonical R-action on `FractionRing S` is retained.
The [fraction-field comparison](Basic.md) gives finiteness of the literal
`integralClosure R L` with the same L and the induced R-action through S.

The [integral-closure localization theorem](../IntegralClosure/Localization.md)
identifies the original inclusion

```text
integralClosure R L -> integralClosure S L
```

as a localized-module map. Localizing its finite set of generators gives
`Module.Finite S (integralClosure S L)`. This is the N-2 statement of
[Stacks, Lemma 10.161.3 (032G)](https://stacks.math.columbia.edu/tag/032G).

`IsNagataRing.of_isLocalization M h` applies to arbitrary commutative rings
R and S. It derives Noetherianity of S from the original Nagata hypothesis.
For each actual prime q of S, put p = q.comap (algebraMap R S). The proof
uses the canonical map R/p -> S/q and proves that it localizes at the image
of M: the quotient maps commute with R -> S, and localization gives
`p.map (algebraMap R S) = q`. Japanese localization applies to these actual
prime quotients. The assertion includes the zero ring, whose prime condition
is vacuous. This proves the content of
[Stacks, Lemma 10.162.6 (032U)](https://stacks.math.columbia.edu/tag/032U)
within the stated universe contract.

The current consumers are localizations of finite normalizations and prime
quotients in the dimension-two Nagata and rational-adjunction arguments.
Together with [finite ascent](Finite.md), this supplies finite and
localization closure independently of arbitrary finite-type stability.
It does not supply the missing normalization theorem for nonnormal complete
two-dimensional domains, the associated-prime completion criterion, or
monogenic Nagata stability. In that later criterion regularity concerns the
ambient local ring at an associated prime, not the localized principal
quotient. Scheme applications still require the actual dominating,
generically finite chart maps.
