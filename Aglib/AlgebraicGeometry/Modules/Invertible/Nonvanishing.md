# Nonvanishing of arbitrary line-bundle sections

[Nonvanishing.lean](Nonvanishing.lean) defines the geometric open of an arbitrary
section of an actual `LineBundle X`. Its global interface is
`nonvanishingOpen L s`, with `s : Γ(L.val, ⊤)`. The local-section interface
`nonvanishingOpenOn L U s` takes `s : Γ(L.val, U)` on an original open `U` of
the original scheme. A compatible-family global section can be evaluated at
`op ⊤` to supply the global input.

The definition takes the union of the actual coefficient basic opens in all
actual trivializing frames. It requires no generating family. The proof
`Nonvanishing.basicOpen_coefficient_eq` uses the existing
`LocalFrames.transitionUnitOn`: its unit coefficient changes one original
frame coefficient into the other. `Nonvanishing.basicOpen_coefficient_restrict`
uses the existing literal coefficient restriction formula and `Scheme.basicOpen_res`.

`inter_nonvanishingOpenOn` gives the exact local formula. For any actual frame
of `L.val` on `W`, the intersection of `W` with `nonvanishingOpenOn L U s` is
the basic open of the original coefficient on `U ⊓ W`, using the actual
restriction of `s`. The global formula is `inter_nonvanishingOpen`.
`mem_nonvanishingOpen` identifies membership with the coefficient germ being
a unit in the original structure-sheaf stalk.

`nonvanishingOpenOn_iso` and `nonvanishingOpen_iso` transport the section by
the original module-sheaf isomorphism and preserve the open.
`nonvanishingOpenOn_smul` and `nonvanishingOpen_smul` give the exact intersection
with the basic open of the original scalar function. The restriction theorems
retain the original section restriction maps: restricting a section from `U`
to `V ≤ U` gives `V ⊓ nonvanishingOpenOn L U s` in the original scheme.

The restriction result is an equality of original-scheme opens for sections
of the original module. A general scheme-pullback theorem additionally needs
the actual pullback section and a coefficient comparison with a transported
pullback frame. An equality stated on the restricted scheme itself additionally
needs that comparison through `restrictAppIso`, `overFunctorEquiv` and the
actual frame on the restricted module. These adapters are not asserted here.
Likewise, the tensor-intersection formula needs the sectionwise coefficient
identity for `moduleTensorSection` under `tensorOverTrivialization`; it is not
inferred merely from existence of a tensor bundle. No ampleness predicate or
relative-ampleness conclusion is introduced by this module.
