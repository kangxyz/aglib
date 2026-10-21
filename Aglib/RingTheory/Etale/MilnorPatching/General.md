# General component reconstruction and formal unramifiedness

`Aglib.RingTheory.Etale.MilnorPatching.General` works with the existing literal
`fiberRing` and `fiberMap`. Write

\[
P=R\times_T S,\qquad Q=C\times_U D,\qquad \alpha:P\longrightarrow Q.
\]

The input consists of the original seven ring maps, their two commutative
squares, a surjection \(f:R\to T\), and the specified compatible equivalences
\(T\otimes_R C\simeq U\) and \(T\otimes_S D\simeq U\). Compatibility means
that \(1\otimes c\) and \(1\otimes d\) map to the original boundary maps
\(b(c)\) and \(v(d)\). All six commutative rings may be arbitrary in the
same universe. The reconstruction results need no flatness, finite-module,
Noetherian, or faithfulness hypothesis.

The general reconstruction namespace uses `Fact` instances for the two
commutative squares and the native component scalar towers. The final
seven-map theorem takes the squares as ordinary explicit proof arguments
and installs the canonical actions, towers, and instances internally.

## Canonical maps and proof

The first and second tensor maps send

\[
a\otimes(c,d)\longmapsto r(a)c,\qquad
s_0\otimes(c,d)\longmapsto s(s_0)d.
\]

`General.ker_snd_eq_map` identifies the kernel of \(Q\to D\) with the extension
of the kernel of \(P\to S\). The existing boundary theorem identifies
\(\ker b\) with \((\ker f)C\), and the existing generation theorem says that
the first projections of elements of \(Q\) span \(C\) over \(R\).
Two span inductions then express every kernel pair as an element of the
extended conductor. The quotient/tensor comparison gives
`General.sndTensorEquiv` with the displayed second-component map.

For the first comparison, base change of the second equivalence gives
\(T\otimes_P Q\simeq U\). Tensor right exactness identifies the kernel of
\(R\otimes_P Q\to T\otimes_P Q\) with the extension of \(\ker f\).
Every tensor in that ideal has the form \(1\otimes q\), with the second
coordinate of \(q\) zero: on a pure tensor, move a conductor coefficient
through the tensor relation using the element \((a,0)\in P\), and extend
by the two span inductions. If the first tensor comparison also kills this
element, both coordinates of \(q\) vanish. Surjectivity follows from the
generation theorem. This constructs `General.fstTensorEquiv` with the
displayed first-component map.

`RingHom.Etale.MilnorPatching.formallyUnramified_fiberMap` applies these two
equivalences to the actual module of differentials \(\Omega_{Q/P}\).
If \(r\) and \(s\) are formally unramified, both component tensors of this
module vanish. The existing conductor-based joint tensor conservativity
theorem implies \(\Omega_{Q/P}=0\). This is the literal seven-map conclusion,
without an input patching theorem or a component finiteness restriction.

## Etale conclusion and upper suppliers

`etale_fiberMap_of_flat_of_finitePresentation` combines the proved formal
unramifiedness with flatness and finite presentation of the original map.
The [flatness companion](Flat.md) proves the first condition from the two
component flatness hypotheses. The [finite-presentation companion](FinitePresentation.md)
proves the second from that flatness and the component finite presentations.
Together they give `etale_fiberMap` and the inhabitant
`RingHom.Etale.MilnorPatching.etalePatching` of the original universal
`EtalePatching` proposition, without either output property as an assumption.
Finite split-power projectivity is not used to supply these general conditions.

## Primary source correspondence

The primary Stacks pages were inspected on 2026-10-21.
[Situation 08KH](https://stacks.math.columbia.edu/tag/08KH) corresponds to
\(A'=R\), \(A=T\), \(B=S\), \(I=\ker f\), with its fiber-product order
swapped. The existing `quotientBoundaryEquiv` and its pure-tensor equation
identify the actual quotient \(C/IC\) with \(U\), so the hypotheses of
[Lemma 08KQ(5)](https://stacks.math.columbia.edu/tag/08KQ) match the universal
tensor interface. Its boundary isomorphism is the tensor commutor
\(D\otimes_S T\simeq T\otimes_S D\), followed by the specified second
equivalence and the inverse quotient-boundary equivalence. The coordinate
swap identifies its resulting fiber map with the original map here.
That source theorem has no extra finite-module or
Noetherian premise; it is not imported as a Lean proof.

[Lemma 07RU](https://stacks.math.columbia.edu/tag/07RU) gives the general
component reconstruction statement. The flatness and finite-presentation
routes correspond to [Lemma 0D2I](https://stacks.math.columbia.edu/tag/0D2I)
and [Lemma 08KP](https://stacks.math.columbia.edu/tag/08KP), respectively.
The companion proofs establish their required module statements and the
actual presentation-kernel comparison before deriving the universal result.
