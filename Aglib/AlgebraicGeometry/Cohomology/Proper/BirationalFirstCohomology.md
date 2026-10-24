# Injectivity of the original first cohomology map

`moduleCohomologyMapAlongLinear_unit_injective_of_isProper_birational`
proves injectivity of the exact original degree-one geometric cohomology
map with coefficient arrow
`SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom`.
The structural action is an arbitrary specified ring map
`α : R → Γ(X,O_X)` from a commutative ring; the target action remains
`g.appTop.hom.comp α`.

The assumptions are that `X` and `Y` are integral, `g : Y → X` is proper
and dominant, `X` has normal stalks, and its original function-field map is
an isomorphism. The original pushforward structure unit already supplies
the general Leray triangle in `Proper/DerivedStructure`.

Only its first adjacent vanishing is used. The actual derived pushforward
of the structure single is nonnegative. Its positive truncation is at
least one, and the same native derived global-sections functor preserves
that lower bound. Thus H0 of the third triangle object vanishes. The
native homology sequence makes the first degree-one arrow a monomorphism.
The original source and middle linear equivalences transfer injectivity,
and the public original-map comparison gives exactly the displayed
geometric map.

There is no complete-base, Nagata, dimension, H2-vanishing, flatness or
source-regularity premise. The
[regular-local universal H1-vanishing theorem](../../Surfaces/RationalSingularities/Regular.md)
uses this injection after constructing a dominating regular point chain.
The injection alone asserts no rationality or resolution theorem.
