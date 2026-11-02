# Godement open base change

The [original facade](../OpenBaseChange.lean) retains the original source
provenance and all 29 public declaration names, statements, maps and hypotheses.

| Leaf | Responsibility |
| --- | --- |
| [Basic](Basic.lean) | Three original Plus facts, total-term flasqueness and the two existing named standard-derived-category constants. |
| [Geometry](Geometry.lean) | The original Cartesian pushforward/pullback comparisons and geometric unit equation. |
| [Bridge](Bridge.lean) | The original bridge, quasi-isomorphism/flasqueness suppliers and degreewise value. |
| [SpanData](SpanData.lean) | Eight original span objects/maps, unit factorization and the two quasi-isomorphic legs. |
| [FirstSquare](FirstSquare.lean) | Comparison naturality and the geometric unit, evaluated before native specialization. |
| [SecondSquare](SecondSquare.lean) | The original augmentation naturality equation and its original pushforward view. |
| [SpanComponent](SpanComponent.lean) | Generic categorical pasting of the two proved original component squares. |
| [SpanFactorized](SpanFactorized.lean) | The whole original equality from the faithful inclusion and equality in every degree. |
| [Span](Span.lean) | The original unit span and its conditional quasi-isomorphism descent consequence. |

`Basic` and `Geometry` use their original lower providers independently.
`Bridge` imports both and `SpanData` imports `Bridge`. The first square needs
only `Geometry`, the existing Godement total/unit provider and the generic
factory; the second square consumes `SpanData`. The component imports the two
proved squares, the factorized equality imports that component, and the two
final consequences import the completed equalities.

The [generic factory](../../../../CategoryTheory/Functor/NatTrans/UnitInsertionSpan.lean)
constructs complete unit, mate and augmentation comparison laws over variable
categories and functors. Its point/map view retains only the actual arrows and
independent geometric unit equation needed by the native first square.
Degree evaluation uses the original Plus inclusion and cochain evaluation.
The second square and final assembly retain the original faithful thin views.

The two pre-existing `openBaseChangeDerivedStandard` constants occur once in
`Basic`, under the original `Modules.Plus` and `Modules.Godement` namespaces.
Leaves activate those original constants locally when required; `Geometry`
and `FirstSquare` need no derived model.

Ordinary iteration compiles a changed leaf and its actual necessary consumers,
reusing compatible producer artifacts. Exact compilation and performance
conditions, failed approaches and preserved evidence belong to the
[performance case](../../../../../docs/performance/cases/godement-unit-insertion/README.md).
