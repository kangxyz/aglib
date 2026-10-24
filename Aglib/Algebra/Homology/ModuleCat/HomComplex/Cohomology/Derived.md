# Native dual homology and original derived Hom

[Derived.lean](Derived.lean) supplies the common comparison needed by the
original unit-Postnikov row and chosen-embedding Serre comparison:

    derivedDualHomologyLinearEquiv J n X :
      H^n((derivedDual J).obj(op X)) ≃ₗ[A] Hom_D(A)(X, Q(J)[n]).

J is the actual supplied K-injective A-complex, n is any integer, and X is
any object of the original A-derived category. The source module, target
Hom module, scalar action and original arrows are all native. No chosen
representative, concentration, evaluation, trace or naturality premise is
added.

The original module-valued model isomorphism is unchanged. On Q(K), it
applies native homology to `derivedDualFactors J`, then applies the original
`homologyFunctorFactors`. The original Hom-complex homology/class comparison
and `cohomologyDerivedEquiv` send the result to the original localized
cocycle. Postcomposition uses the raw original component
`(Q.commShiftIso n).hom.app J`.

The internal comparison descends as a natural isomorphism of additive
functors. Additive ULifts reconcile the two carrier universes.
`Localization.liftNatIso` is applied to the original opposite localization
Q.op.

A-linearity is then proved, rather than transported. The original source
functor `derivedDual` followed by native homology is A-linear by
`Localization.functor_linear_iff`, using the unchanged model isomorphism
and the `moduleHomologyFunctor_linear`. The generic
`ModuleCat.linearEquivOfLiftedAddIso` combines that source linearity with
source naturality and the literal Hom precomposition action. Its forward
function is still the same unlifted original additive component.

`derivedDualHomologyLinearEquiv_naturality` holds for every original derived
arrow f:X→Y:

    Phi_X(H^n(D_J(f.op))(x)) = f ≫ Phi_Y(x).

The `_Q`, `_Q_factors`, `_iso` and `_cocycle` declarations retain the
original model, factorization, representative inverse and literal localized
shifted cocycle. `moduleHomologyDerivedLinearEquiv_precomp` retains original
chain precomposition for the module comparison. These maps
apply to the original eta, kappa and delta, without supplying a representative
for any of them.

No endpoint premise or external argument is added by the new internal
representation. The source-linear instance is derived from the existing
original model, and native module structures are unchanged. This bridge
alone does not assert a trace identity, dual amplitude, finite length,
biduality or Grauert--Riemenschneider vanishing.

The retained public precomposition formula uses one compact native component
function. `moduleHomologyDerivedValue` unpacks the original chain-comparison
component and postcomposes with the inverse of the same original Q-shift
isomorphism. The generic `ModuleCat.liftedHomIsoValue` constructs that function
with literal source and target types, and its naturality follows directly
from the original categorical naturality square.

`moduleHomologyDerivedLinearEquiv_coe` identifies the entire original linear
comparison function with this compact value function. The equality is now
proved at the generic constructor stage: the same variable class isomorphism,
localization equivalence and shift produce both
`ModuleCat.natIsoAddEquivTransLinear` and the lifted native component. The
generic class value equation and inverse-isomorphism cancellation identify
their functions before any concrete module homology or derived category is
substituted. The concrete theorem supplies those original constructor data;
its class-to-shift equation is reflexivity from the original definitions.

This equality retains the original class/localization map and A-action;
no action is reconstructed or transported. The public precomposition proof
applies generic naturality to the compact function, then rewrites by this
function equality. The generic equation no longer takes two separately
instantiated concrete functions or their pointwise comparison as input.


This dependency is non-circular: the chain comparison is constructed from
the original class functor and `cohomologyDerivedEquiv_precomp`, and its value
formula is proved from the original generic class/linear constructor. Neither
uses the public module-precomposition wrapper. Original maps, scalar actions,
premises and the public statement are unchanged.

The retained Q-normalization evaluates
the already-proved categorical model-component equation and composes it with
the original class constructor within one generic theorem, before
specialization. The cocycle formula then uses generic cancellation of that
actual module isomorphism. No expanded concrete class-formula proof is passed
through a higher-order transport, and the concrete Q proof no longer composes
two separately evaluated components.
