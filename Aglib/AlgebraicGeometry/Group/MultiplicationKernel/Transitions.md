# Actual multiplication-cover transitions

`Transitions.lean` compares levels `d*e` and `d` of the same commutative group
scheme over `F : Type u`. `multiplication_comp` is the literal composition
identity. `reductionCoverMap` is multiplication by `e` on the source cover;
`reductionCoverMap_fiber` is exactly multiplication by `e` on actual geometric
torsion points. `quotientMap_reduction` is its naturality square for the
original arithmetic projection kernel. It retains independently supplied
finiteness and etaleness at both displayed levels. Neither `d` nor `e` needs to
be positive, and no coefficient-reduction map is substituted for this cover map.

`torsionLowering` uses `(n / d) • t` when `d ∣ n`. Its point-group construction
is meaningful in the original zero cases; `quotientMap_lowering` retains the
source guard `0 < d`. These maps and their proofs need no characteristic
hypothesis. No rank, degree, character or direct-limit assertion is made.

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Torsion.MonodromyTransitions`,
packet lines 44–83 and 106–121, SHA-256
`a52a08afbb28fb5c54f19ddf4f769508430da72afc801fbe58581986b79b71a9`.
The actual torsion-reduction/lowering formulas used by that source are proved
directly on the same point subgroups. Source lines 84–96 and 122–135 involve
R5 coefficient insertion/inflation and remain downstream. Current consumer:
[AglibTest/MultiplicationKernelGeometry.lean](../../../../AglibTest/MultiplicationKernelGeometry.lean).
