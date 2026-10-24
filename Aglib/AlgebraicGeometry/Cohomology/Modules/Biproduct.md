# Finite biproducts on structural cohomology

The scalar map is the specified ring homomorphism `R → Γ(X, ⊤)` throughout.
`moduleCohomologyBiproductLinearEquiv` uses the native additive functor
`moduleCohomologyFunctorOfHom`, its finite-biproduct comparison and the
concrete product comparison in `ModuleCat`. Its source and target are the
original `Sheaf.H` groups with their original structural actions.

`moduleCohomologyBiproduct_length` gives the sum of the component lengths.
`moduleCohomologyFiniteCopies_length` specializes this to `r` copies of one
coefficient. Lengths take values in `ℕ∞`; no finiteness hypothesis is needed.
The family index is a small finite type, including the original `Fin r`
index used by trace coordinates.

The current consumer is the cohomology of the native finite biproduct in
the original trace-coordinate construction. This module alone supplies no
finite-extension bound or geometric domination theorem. It uses ordinary
additive-functor preservation of finite biproducts, with no new scalar or
comparison-map premise.
