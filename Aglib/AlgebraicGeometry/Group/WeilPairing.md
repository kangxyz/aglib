# Actual Weil pairing on multiplication torsion

`WeilPairing.lean` constructs the pairing on the original
`MultiplicationKernel.finiteTorsionPoints E n`, with values in
`Field.absoluteGaloisGroup.RootsOfUnity.Mu F n`. Its current consumer is the
elliptic torsion/character comparison specified by `EG-WEIL-PAIRING`.
The constructor returns all six fields of the native `PerfectWeilPairing`
record.

The hypotheses are the original commutative group scheme over a field,
`Curve.Properties E.X`, native `Curve.coherentGenus F E.X = 1`, and a
positive level `n` with `IsUnit (n : F)`. Native curve properties and coherent
genus one remain explicit until the independent genus comparison is supplied.
The construction includes composite and even levels and level one.

The multiplication isogeny has geometric degree `n * n`. `degreePairing`
uses the genuine Cartier evaluation and multiplication triangle
`[n] ≫ [n] = [n*n]`. Every character of the literal group killed by `n`
already has values in the actual `n`th roots. `rootCharacterEquiv` performs
that restriction without changing the underlying unit. `pairing` uses the
canonical `ZMod n` structures, and `pairing_bijective` transports the proved
Cartier perfectness through these actual equivalences.

For alternation, work over the original algebraic closure. Let `P` be a
literal kernel point, choose an actual point `Q` with `nQ = P`, and put
`M = I_0 = O(-0)`. The positive translation formula is
`[t_P^* M] - [M] = pointDivisorClass P`. Thus the exact existing
`kernelPointLineBundle` admits an isomorphism `R ⊗ M ≅ t_P^* M`.
The exact frame already used by `evaluationCharacter` defines a lift `A`
of `t_Q` on `[n]^* M`. Its `n`th power and the canonical `t_P` deck lift
cover the same scheme automorphism. Their ratio is a scalar automorphism,
and proper-curve constants make that scalar central. The lifts commute.

The actual Cartesian projection equations and native tensor-pullback
comparisons identify that commutation with invariance of the original
frame. Tensoring by the invertible module `[n]^* M` is faithful, so the
frame itself is fixed. Its positive transport scalar is therefore one.
`evaluationCharacter_self`, `degreePairing_self`, and `pairing_alternating`
retain this identity through the original point and root comparisons.
The lower argument is in
[`TranslationLift.lean`](../Picard/TranslationLift.lean).

`pairing_galois` retains the original torsion precomposition and actual
field-automorphism action on roots. The root carrier is exactly
`Additive (rootsOfUnity n (AlgebraicClosure F))`; `rootAction` applies the
same automorphism as the source's `cyclotomicGalois`.
`perfectWeilPairing` packages the map, alternation, perfectness, equivariance,
and the independently proved `torsionBasis`. No Galois invariance of that
chosen basis is used.

Source interface: packet `AGLIB_PROOF_TASKS.json`, `EG-WEIL-PAIRING`, lines
16404–16444; frozen R5 `EllipticCurve/Torsion/WeilPairing.lean`, SHA-256
`9f642c9bb1545875b1465e66aefd5018bda6509ad7d54b7ffc9e9184fb1479c5`.
The original cyclotomic action is in `RootsOfUnity/CyclotomicPoints.lean`,
SHA-256 `dd97b421f92ad095393899588dc11976b376ca60c55ed25619b148a073df0636`.
