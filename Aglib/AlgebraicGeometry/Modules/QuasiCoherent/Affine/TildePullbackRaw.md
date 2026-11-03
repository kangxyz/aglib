# Original tilde pullback data at raw scalar actions

Source: [TildePullbackRaw.lean](TildePullbackRaw.lean).

`tildePullbackHomRingHom f` has the literal scalar functor
`ModuleCat.extendScalars f` in its target type. Its value is exactly the
original `tildePullbackIso (CommRingCat.ofHom f)` hom on the original ring
objects, certified by a reflexive identity equation. No new adjunction, iso,
coefficient object or scalar action is constructed.

The whole natural law retains the original arbitrary Spec-triangle proof h,
pullback composition, scalar composition and associators. It transports the
existing whole natural producer through the same three identity equations.
The component law transports the existing public component theorem through
those identities; its generic component evaluator remains implemented once,
private and unchanged in `TildePullback`. There is no new component proof or
claim that the new component theorem literally invokes the new whole theorem.

Only the existing arbitrary-h natural producer is made public, without changing
its signature or body. The fundamental `Pullback` owner is unchanged. The
native presented-sheaf constructor and complete composition caller consume
these identical raw-view data while retaining their old public statements.

Direct consumers: [AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineSheaf](../../../Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineSheaf.lean).
