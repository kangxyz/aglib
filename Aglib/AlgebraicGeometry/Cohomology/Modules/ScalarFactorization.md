# Scalar factorizations on structural cohomology

The input factorization consists of actual module-sheaf arrows `φ` and `ψ`
whose composite is multiplication by the displayed global scalar. The
original coefficient functor proves the same composite equation on
`Sheaf.H`, for its specified structural ring action. The length inequality
then uses the original scalar-torsion submodule and actual target length.
All lengths lie in `ℕ∞`; no finiteness or splitting premise is introduced.

`moduleCohomologyScalarTower` constructs the scalar tower associated to an
original map `B → Γ(X, ⊤)` and its actual composite with `A → B`. It does
not choose another scalar action or identify unrelated structural maps.
When applied to a geometric square, that square's original equality of
global scalar maps must still be used.
`moduleCohomologyScalarTowerOfEq` transports exactly that proved ring-map
equality; its cohomology group and the two specified actions are unchanged.

The current consumer is the finite trace-coordinate factorization. Its
actual sheaf arrows supply the input equation; the affine cohomology
comparison and original structural scalar square are separate suppliers.
This module alone does not prove a uniform finite-extension H1 bound.
