# Finite original singular-prefix height

API: [exists_empty_singularPrefix_level_of_initial_cone_of_complete_base](FiniteHeight.lean#L36).

`exists_empty_singularPrefix_level_of_initial_cone_of_complete_base` starts
with a commutative Noetherian Nagata local domain `S` of dimension two
satisfying `NormalModificationH1Vanishing S`. The supplied
`f : X ⟶ Spec S` is proper and dominant, `X` is integral with normal
stalks, and the original `functionFieldMap f` is invertible.

At a singular `x : X`, the input is a triple `(t,g₀,g₁)` generating the
actual maximal ideal and a nonzero homogeneous quadratic `q` over that
stalk's original residue field, with
`RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q}`.
An earlier commutative local domain `A` is complete for its maximal ideal
and has dimension two. Its supplied map `a : A →+* O(X,x)` is local and
injective, with finite original residue-field map. No Noetherian hypothesis
on this earlier `A` is added.

The result is `∃ n, IsEmpty (SingularPrefix X x n)`.
`FinitePrefixGeometry` proves finite parent fibres on the original finite
prefixes. If every level were nonempty, native König and the existing path
realization would produce a compatible original `ClosedPointBlowupPath`.
`OriginalMixedPath` constructs a marked tail and contradicts its everywhere
singular points using that earlier complete base. The root scheme, point
and stalk remain the ones originally supplied.

`PointHeight` gives locality and strict decrease of the resulting least
empty levels; `HeightMultiset` supplies the multiset decrease.
`FiniteResolution` serializes these data, and `NormalizedResolution`
uses the proved normal stages and explicit terminal isomorphism.
Those endpoints retain their supplied initial cones and earlier complete map.

Present consumers: [FiniteResolution](FiniteResolution.md).
