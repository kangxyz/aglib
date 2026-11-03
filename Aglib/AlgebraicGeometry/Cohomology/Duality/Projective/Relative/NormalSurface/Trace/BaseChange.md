# Actual counit evaluation after base change

`BaseChange.lean` isolates the ordinary adjunction part of local canonical
pullback from the larger cohomology comparison in `Localization.lean`.
For an invertible actual sheaf trace `tau : f_*M → N`, its pullback is the
original adjoint of `tau.inverse`, equivalently `f*(tau.inverse); counit`.
The open-restriction theorem retains the original restriction comparison.

For an actual Cartesian square `(a,b,f,j)`, its base-change theorem is

    a*(c_tau) = kappa ; b*(j*(tau.inverse) ; beta_M) ; counit_b,

where beta is the original ordinary base-change mate and kappa is the
composite-pullback isomorphism determined by the original pushforward square
and four native adjunctions. This is equality of sheaf maps, valid without
flatness or properness. Applied to j=fromSpecStalk it is the actual local
counit/evaluation identity; identifying beta on sections with the particular
mu in `Localization.lean` is a further degree-zero comparison obligation.

This general helper is used for the actual canonical trace from `Proper.lean`.
No invertibility or surjectivity of that trace is asserted here. The proof is
ordinary mate calculus (`Adjunction.squareAdjoint_eq`) rather than equality
detected by global sections. Current compilation is recorded by the integrator.
