# Finite singular sets on actual normal surface models

API: [finite_singularSet_inter_affine_of_isJ2Ring](FiniteSingularLocus.lean#L35), [finite_singularSet_of_finiteType_of_isJ2Ring](FiniteSingularLocus.lean#L67), [finite_singularSet_of_finiteType_complete_local](FiniteSingularLocus.lean#L96).

The model X is an integral Noetherian scheme with normal actual stalks and
topological dimension at most two. Its original morphism to Spec A is
locally of finite type. Given J-2 for A, the actual structural map on an
affine open U installs the original finite-type A-algebra on Gamma(X,U).
Normality of the original stalks gives integral closedness of that ring.
The affine open embedding gives its dimension bound.

[RegularLocus](RegularLocus.md) then proves finiteness of its nonregular
prime localizations. The original spectrum-stalk and open-immersion stalk
isomorphisms transport these points to the singular points of X in U.
The scheme's actual finite affine subcover gives a finite union containing
exactly all singular points.

The complete-local corollary derives the full J-2 hypothesis from the
existing complete Noetherian local dimension-at-most-two Nagata theorem
and semilocal Nagata J-2 criterion. No semilocality, completeness, or
module finiteness is imposed on the model's chart rings. No resolving model,
ADE classification, marker, or termination measure is an input.

The model's actual normality and dimension bound remain hypotheses of this
reusable theorem; rational-blowup consumers must supply their existing
geometric producers. This leaf asserts finiteness of the original singular
set, not a resolving chain or propagation of Gorensteinness/rationality.

The affine regular-locus-complement to scheme-singular-set transport is
owned by [Properties/Regular/Affine](../../../Properties/Regular/Affine.md).
The existing J-2 theorem supplies its finite ring-locus input and reuses that
original stalk comparison, retaining its public statement.

The affine theorem has no local-Noetherianity premise on `X`; the whole-scheme
theorem retains Noetherian `X` for its finite affine cover.
The J-2 input is `IsJ2Ring.{u,0} A` for a commutative base ring.
The complete-local specialization takes a commutative complete Noetherian
local `A` of dimension at most two; `A` need not be a domain.

Present consumers: [ClosedSingularPoints](ClosedSingularPoints.md), [FinitePrefixGeometry](FinitePrefixGeometry.md).
