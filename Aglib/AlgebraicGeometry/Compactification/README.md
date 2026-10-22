# Compactification of scheme morphisms

Import `Aglib.AlgebraicGeometry.Compactification.QCQS` for Nagata
compactification of a separated finite-type morphism over a quasi-compact
quasi-separated base. The [qcqs guide](QCQS.md) gives the exact statements and
the approximation and descent route.

In `AlgebraicGeometry.Scheme.Hom`, [Basic](Basic.lean) defines
`Compactification f` for `f : X ⟶ S`, with `X S : Scheme.{u}`. Its data are an
actual scheme `Xbar : Scheme.{u}`, an open immersion `j : X ⟶ Xbar`, a proper
map `p : Xbar ⟶ S`, and `fac : j ≫ p = f`. Density is a separate property of
`j`. The qcqs existence theorem supplies `IsSchemeTheoreticallyDominant j`,
so it retains the scheme structure, including nilpotents.

| Import | Reusable interface |
| --- | --- |
| `Aglib.AlgebraicGeometry.Compactification.Basic` | `Compactification.ofImmersion f j p h` takes a quasi-compact immersion into a proper scheme and its specified triangle, then takes its native schematic image. The resulting open immersion is schematically dominant. |
| `Aglib.AlgebraicGeometry.Compactification.BaseChange` | `C.baseChange b` compactifies the literal map `pullback.fst b f`; `C.ofSourceIso f' e h` transports along `e : X' ≅ X` with `h : e.hom ≫ f = f'`. |
| `Aglib.AlgebraicGeometry.Compactification.Noetherian` | `exists_compactification_of_isNoetherian` and `exists_schematicallyDense_compactification_of_isNoetherian` assume a Noetherian base and a separated, quasi-compact, locally finite-type morphism. |
| `Aglib.AlgebraicGeometry.Compactification.NoetherianLimit` | `exists_compactification_of_noetherian_isLimit` compactifies a separated finitely presented morphism over a supplied affine-transition limit of Noetherian schemes. |

The [base-change constructor](BaseChange.lean) fixes both original projections:

```lean
(C.baseChange b).j ≫ pullback.fst b C.p = pullback.fst b f
(C.baseChange b).j ≫ pullback.snd b C.p = pullback.snd b f ≫ C.j
```

These are `baseChange_j_fst` and `baseChange_j_snd`. This constructor transports
the open immersion and proper structural map; it supplies no general
preservation theorem for schematic density under arbitrary base change. The
qcqs proof obtains density by its final schematic-image construction.

The [closed finite-presentation hull](../Morphisms/FiniteType/README.md) and
[arithmetic approximation](../Approximation/FinitePresentationEnvelope/README.md)
are reusable inputs. The Noetherian geometric construction uses actual
admissible blowup sequences, a finite common enlargement and proper-surjective
descent. This family concerns compactification of scheme morphisms; the
Nagata/Japanese ring condition and finiteness of normalization have separate
owners.
