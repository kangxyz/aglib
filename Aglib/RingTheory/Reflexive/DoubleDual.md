# Actual double duals on regular local surfaces

For a finite module `M` over a regular local ring `R` of dimension at
most two, the actual module `Hom_R(Hom_R(M,R),R)` is free. The proof
uses finiteness of the dual over the Noetherian ring, reflexivity of
that dual's dual, and the existing projective-dimension bound for
finite reflexive modules. Dimensions zero and one are included.

If the specified original localization of `M` is a one-dimensional
vector space over the fraction field, the two actual localized Hom
maps prove that its double dual has rank one. Combining rank one with
the derived freeness gives a local trivialization of this actual module.
No line-bundle or canonical-module structure is assumed.

The height-one extension part works over a normal Noetherian domain.
Let `f : N -> V` be the original generic localization of a finitely
presented module. If a vector lies in the localized image at every
height-one prime, every original dual functional takes an integral
value on it by the normal height-one intersection theorem. The vector
therefore belongs to the image of `doubleDualToFraction f`.

For a specified linear map `g : P -> V` satisfying this pointwise
height-one condition, `liftLinearMapToDoubleDualOfHeightOne` constructs
its unique lift to the actual double dual of `N`. Its equation is

```text
doubleDualToFraction f (lift m) = g m.
```

When `g` already factors through `f`, the lift is the original bidual
evaluation of that factor. This fixes the normalization needed for
gluing the one-pole differential map. The height-one extension does
not assume that `N` is reflexive or that the source is torsion-free.
The sheaf comparison, local line assembly, and blowup application are
separate geometric consumers.
