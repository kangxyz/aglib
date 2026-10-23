# Completed etale continuity and local-comparison suppliers, 2026-10-24

This integration follows `f464f6b13dce9776829f9b20e514cc674cddd6fc` and
preserves the operational/cache changes through
`aa4c265bd5725ebd935ecf89855e50cec59b8965`. Lean remains 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Admitted scope

The cut contains 109 completed source versions: 42 internal suppliers and
67 selected versions from final external A, including one unchanged baseline
cokernel supplier. There are 108 new production modules. Its archive is
`continuity-finite-source-20261023T192904Z.tar.gz`, SHA256
`96c3cc1de0677fc9ba4c255083c6e28dff20c95338e98d752eb05df22758a02e`.
The latter comprises 65 new geometric sources, one required generic
`CoconeDoubleOpposite` helper and the baseline cokernel supplier. Its redundant
new simp attributes were not retained. Eleven explicitly uncompiled auxiliaries are excluded.
The current `MappedCoverModel` field docstrings are retained.

| Family | Actual completed output |
| --- | --- |
| Continuity | All-degree original cohomology on qcqs inverse scheme limits with affine transitions. The public wrapper constructs its degree-zero and qcqs right-tail cocone inputs; actual limit and size/Ext/group-colimit premises remain. |
| Higher-image stalks | Actual marked strict-local limit comparison, coefficient naturality, every pointed-neighborhood germ and original derived-zero unit normalization. The native pointed-neighborhood ring model is used literally. |
| Constructible presentations | General finite-arrow finite-colimit closure; actual affine-etale strata; positive genuine constructible/ambient-FP stages on separated bases and FP on every original affine open. All-modulus scalar equivalence and cocone transport are distinct from positive-modulus constructibility. |
| Finite cogenerators | An actual original finite constant product embedding for constructible ambient-FP coefficients on affine Noetherian schemes, without finite normalization or Japanese assumptions. |
| Proper reductions | Universal bounded exchange and independent-model transport; conditional reduction from native projective-line exchange to arbitrary proper maps over the same spectrum. Original finite cohomology tests and genuine-module annihilator/product adapters retain their actual maps. |

General nonaffine finite cogeneration, the actual all-coefficient projective-line
local comparison, and general torsion proper base change remain mainline work.
No unbounded six-operation formalism is asserted. Optional strict-local `D+`
comparison and a new identification with a separately named strict
henselization are outside the external A delivery.

## Validation boundary

Independent ordinary reviews accepted these fixed versions and their actual
premises. Native incremental graph `remote-d980a4cfdeda4f1f9ddf3a69ec6945fe`
passed all 66 invoked frontends, with no failures; matching prior artifact
coverage was retained for the other selected sources. An actual anonymous
instance-name collision was repaired, then five native lint source repairs
and their affected consumers passed 23 frontends in
`remote-4a990481bbe1449cb6734161aca0c57a`. Source-only guards on the repaired
cut passed in `run-d781886a5e6c44cbb4369e6138dd56d7`. Final native
generated-entry and text-style checks passed in
`remote-69bf7c7008f64cc885add841b5cec796`. Its 15 declaration linters found
no errors in 758 declarations and 525 generated declarations across the 109
selected origins. The pinned axiom check audited 36,580 declarations and
reported only `propext`, `Classical.choice` and `Quot.sound`, with no
violations. No AglibTest, downstream/client check, kernel replay, pin change
or public CI redesign is part of this integration.
