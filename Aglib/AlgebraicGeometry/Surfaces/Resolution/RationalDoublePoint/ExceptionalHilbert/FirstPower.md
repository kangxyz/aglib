# Exceptional Hilbert numerics from cotangent rank three

API: [exceptional_hilbert_of_cotangent_finrank_three](FirstPower.lean#L49).

`MaximalIdealBlowup.exceptional_hilbert_of_cotangent_finrank_three` works on an
original commutative normal Noetherian Nagata local domain of dimension two
with universal rationality. Its sole extra numerical input is the actual
cotangent dimension three over the original residue field. It derives every
original maximal-ideal graded rank `2r+1`.

The original first-power quotient/cotangent equivalence and exceptional
power-section map identify three sections of the actual positive exceptional
line. Genuine rational blowup geometry gives unit H0 dimension one, unit H1
vanishing, the tautological projective embedding, and closed-stalk CM
parameters. The ordinary first-power curve theorem then computes all line
powers, and the original power-section comparisons return to the associated
graded components. Both the scheme and all scalar maps are retained.

There is no Gorenstein, canonical-frame, inverse-line H0/H1, coefficient-field,
normal-completion, or target-kernel input. Nor does rationality alone supply
the cotangent-rank premise. For singular successors, actual three-generation
and nonregular dimension two provide it before Hilbert or kernel recognition.
Initial rational Gorenstein recognition remains a separate geometric task.

The theorem is evaluated on the literal local ring required by its consumer.
No degreewise rank transport is inferred from an ungraded associated-graded
ring equivalence. Existing algebraic producers may use the resulting honest
Hilbert function to determine the entire original quadratic kernel.

Present consumers: [CaseOneNonreturn](../CaseOneNonreturn.md), [OriginalPathCones](../OriginalPathCones.md).
