# Normal actual stages of the original ordinary chain

`PointBlowupChain.NormalStages` is a recursive proposition on the existing
native ordinary point-blowup chain. The empty chain imposes no condition.
Each nonempty step requires `Scheme.NormalStalks` of its actual post-blowup
scheme and the same property of its actual tail. The initial base need not
be normal.

The native refl/cons equations expose exactly these conditions.
`PointBlowupChain.NormalStages.comp` preserves them through the existing
concatenation on the original composite map. No second chain datatype,
parallel concatenation or replacement model is introduced.

Normality is genuine input to this predicate, not a claim that arbitrary
ordinary point blowups preserve normality. A rational-surface producer must
derive whole-source normality using the actual local blowup, the original
Cartesian localization square and the original isomorphism away from the
centre. The normalized-presentation consumer uses precisely this retained
stage data and the native normalization-isomorphism theorem.

The exact initial source `4963662cd6508b3fe1dc414dbdd834a5e103fde4b38154260ba2cc8fc1d1aefc`
passed its own native selected check in recovery graph 68 (2.0 seconds,
2026-10-31). This individual result does not assert success of unrelated
selected roots in the same graph.
