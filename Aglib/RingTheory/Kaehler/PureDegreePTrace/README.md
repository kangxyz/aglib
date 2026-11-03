# Differential trace in purely inseparable prime degree

[Exterior](Exterior.lean) uses the original monic presentation
`S=R[z]/(z^p-a)` in characteristic `p`.
The positive-degree differential trace is normalized by
`η ∧ z^(p-1) dz ↦ η ∧ da` and vanishes on the lower powers.
Its uniqueness, coordinate independence and localization use the same
Kähler exterior maps. This is a differential coefficient trace, not an
identification with ordinary field trace.

[Field](Field.lean) constructs the presentation on the original purely
inseparable degree-`p` field extension and its scalar-multiplication
transpose.
[IntegralClosure](IntegralClosure.lean) starts with a normal Noetherian
domain `A`, its original fraction field `K`, that extension `L/K` and
compatible coefficient ring `Λ`. For finite `B=integralClosure A L` and
finite `M=∧^(n+1) Ω_(A/Λ)`, it constructs the original transpose into
`Hom_A(B,M**)`. The raw source need not be reflexive or torsion-free.
[Coinduction](Coinduction.lean) retains this carrier and makes the map
`B`-linear for the native coextension action `(bφ)(c)=φ(cb)`; no
`B`-action is assigned to `M**`. Ring, coefficient and field universes
retain the source's independent bounds.

[Localization](Localization.lean) compares the same trace through actual
integral-closure and exterior localization maps.
[Cokernel](Cokernel.lean) keeps the genuine top-rank, nonzero differential
and generic-surjectivity data in its finite torsion-cokernel and
annihilator conclusions.
[CompleteRegularEntrance](CompleteRegularEntrance.lean) constructs the
integral generator and expanded-series differential data from an original
complete regular dimension-two local ring of characteristic `p` and the
specified pure prime-degree fraction extension.
These algebraic interfaces do not supply the remaining all-model
geometric trace or resolution argument.

Present consumers include [Birational surface maps, common domination and factorization](../../../AlgebraicGeometry/Surfaces/Birational/README.md).
