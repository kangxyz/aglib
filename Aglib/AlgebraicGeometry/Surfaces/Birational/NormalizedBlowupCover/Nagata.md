# The same normalized blowup cover in an arbitrary finite extension

[Nagata.lean](Nagata.lean) proves finiteness, normality, local Noetherianity,
and properness for the existing `Cover` and `FiniteBase` objects of
`Finite.lean`. It introduces no replacement normalization, field, pullback,
or structural map. Separability is absent from every new wrapper.

`Cover.Nagata.fieldAlgebra` is the original inverse blowdown field map
followed by the original field map of `s`, acting on the unchanged original
function field of the source of `s`. `fieldAlgebra_finite` proves finite
dimensionality from that original finite field map. `genericMap_eq` identifies
the existing original generic map with the common
`Scheme.FiniteFunctionField.genericMap` for this exact action. Transporting
properties along this equality proves finiteness of the existing `Cover.pi`
and normal domain stalks of the existing `Cover.normalization`.

`Base.affineChart_isNagata` derives the needed property for every actual
nonempty affine open of the original `Base.normalization A J hJ`. Its scalar
map is `affineBaseMap (Base.a A J hJ) U`. Properness gives finite type. The
original germ equation and original birational field map give injectivity
and algebraicity over A. The public GF2 theorem
`IsNagataRing.of_finiteType_isAlgebraic_of_dimLE_two` then proves Nagata for
that very chart ring. The parent's private chart helper remains unchanged.

The specialization `FiniteBase.Nagata` supplies these results:

| Declaration | Premises beyond the original domain and dominant-map data |
| --- | --- |
| `Y_normalStalks` | Finiteness of the original function-field map of s |
| `pi_isFinite` | The preceding finiteness, Nagata A, and dimension A at most two |
| `Y_isLocallyNoetherian` | The same premises as `pi_isFinite` |
| `b_isProper` | The same premises and finiteness of the original spectral map s |

Noetherianity of A is extracted from its Nagata property. Normality of Y
does not require a normality assumption on the intermediate base. All new
statements concern `FiniteBase.Y`, `FiniteBase.pi`, and `FiniteBase.b`.
Consequently their existing dominance instances, `b_fieldMap_isIso`,
`imageIdeal` identities, and nonzero original coefficient-ideal frames
remain applicable without an additional comparison isomorphism.

The original universal map into the literal fibre product is still
`Cover.toPullback`. Its first projection equals `Cover.pi` by
`Cover.toPullback_fst`; its second projection is the definition of `Cover.b`.
Thus the original `FiniteBase.square` and `FiniteBase.eta_b` remain exactly

    pi ≫ Base.a = b ≫ s
    eta ≫ b = the original generic inclusion of Spec B.

The same original pi is dominant by the constructed instance. No finite-étale
or finite-flat conclusion is inferred for an inseparable extension.
[FiniteDomination](../FiniteDomination.md) uses these wrappers with the same
original field action.
