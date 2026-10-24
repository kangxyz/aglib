# Annihilation from the original dual-unit image

[Annihilator.lean](Annihilator.lean) compares the original single-one dual
homology with native A-Ext-two into the coinduced coefficient. It then uses
the actual unit Postnikov row to detect scalars annihilating the original
first homology module.

Let sigma:R→A be a homomorphism of commutative rings in Type u. The actual
restricted regular A-module is assumed projective over R. Let I be the
supplied injective resolution of the literal R-module R, Omega the native
coinduced A-module Hom_R(A,R), and J the termwise coinduction of I. The
coefficient augmentation is exactly the inverse native single comparison
followed by coinduction of I.ι'. Its quasi-isomorphism follows from the
existing projectivity theorem for coinduction.

## Original A-linear comparison

`CochainComplex.HomComplex.TwoLayerDual.singleOneExtTwoLinearEquiv`
composes the original single-one shift comparison, the original
single-model homology isomorphism, and `singleHomologyExtLinearEquiv`
with base ring A, coefficient Omega, and that original augmentation:

    H1(D_J(M[1])) ≃ H2(D_J(M[0]))
      ≃ H2(HomComplex_A(single_0 M,J)) ≃ Ext_A^2(M,Omega).

Every comparison is linear for the existing A-actions. The final Ext
carrier is literally `Ext.{u}`, while the native standard derived category
uses universe u+1. The forward-value theorem retains all three original
maps. The coefficient is not replaced by a chosen dual module.

## The actual unit row and scalar conclusion

Let X be a native bounded-below derived A-module in degrees [0,1], with
original unit eta:A[0]→X inducing an isomorphism on H0. Let M be its literal
native H1 module. Assume R is regular local of dimension two and the actual
restriction of M has finite R-length.

`unitPostnikovExtBoundary` is the original unsigned boundary of
`unitPostnikovTriangle X eta`, followed by the A-linear Ext-two comparison.
Under vanishing of the actual H1(D_J(X)),
`unitPostnikovExtBoundary_exact` proves the original short exact row

    0 → H0(D_J(X)) → Omega → Ext_A^2(M,Omega) → 0.

The first map is the existing `unitMap` for the inclusion of eta. The
triangle, its boundary and its projection are constructed from that actual
unit; no exact-row or triangle-model hypothesis is supplied.

For a fixed a:A, `unitPostnikov_scalar_annihilates_of_image` assumes that
every a*phi in Omega lies in the image of this original unit map. The
A-linear boundary then kills a times every Ext-two class. The existing
`ModuleCat.coinducedExtTwo_scalar_annihilates_iff` implies a*m=0 for every
m in the original M. There is no Matlis or injective-hull identification,
transported scalar action, or scalar-annihilation premise.

## Geometric consumer and current boundary

The intended B7 consumer takes X to be the original derived structure
sections and eta its structural unit. The actual finite normal extension
over a regular local surface supplies restricted projectivity; the
original cohomology comparison supplies finite restricted length of M.
The canonical cohomology/dual comparison and GR supply the required dual
vanishing when their geometric hypotheses are met.

Containment in the original unit image is a separate geometric obligation.
It must use the fixed differential map, its actual finite/proper trace
square, and the original H0/section trace normalization. Any coefficient
line comparison must be applied through native coinduction before the
models. This algebraic module does not assert that containment or close
geometric B7, and it does not assert embedding independence of a trace.
