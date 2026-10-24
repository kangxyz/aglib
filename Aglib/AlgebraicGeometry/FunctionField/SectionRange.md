# Actual sections inside the original function field

For an integral scheme `X` and a nonempty open `U`,
`mem_range_germToFunctionField_iff_stalk` identifies the image of the
original section map `Γ(X,U) → K(X)` with those rational functions
represented in every original stalk at a point of `U`.
`range_germToFunctionField_eq_iInter_stalks` expresses this as an
intersection of the actual stalk images in the same field.

The proof chooses representatives of the given stalk elements, restricts
them to their intersections with `U`, and glues them using the original
structure sheaf. The original stalk injections into the function field
prove compatibility. The forward map remains `germToFunctionField` and
no fraction field or section ring is replaced by an abstract isomorphism.

No normality, affineness, Noetherianity, properness or finite-type assumption
is needed. The nonempty-open assumption is the one required by the
original generic-point section map. This does not claim that `K(X)` is
the fraction field of the section ring on every open.

The proof generalizes the gluing argument already used in
[normal global sections](../Properties/Normal/GlobalSections.lean), which
is left unchanged. The current consumer is ordinary finite-morphism trace:
affine-local field-trace values first give original stalk representatives,
then this criterion produces the unique section on an arbitrary open.
Constructing those trace values and their sheaf/module normalization is
a separate consumer obligation.
