# Opposite Kan extension and a closed essential image

[ClosedImage](ClosedImage.lean) gives
`Functor.lan_op_map_mono_of_closed_under_domains`. For a fully faithful
`L : C ⥤ D` between small categories, assume every arrow `d ⟶ L.obj c` has
its domain in the essential image of `L`. The native `L.op.lan` on
abelian-valued presheaves preserves actual monomorphisms. The coefficient
category is abelian with the stated small colimits; its object universe is
independent of the source categories.

At objects in the image the proof uses the original invertible Kan unit.
Outside the image the pointwise comma category is empty and the native Kan
value is zero. The [abelian open extension-by-zero construction](../../../Topology/Sheaves/ExtensionByZero.lean)
supplies the image condition for the inclusion of opens contained in an open
subspace, then applies sheafification. No topological or sheaf premise occurs
in this lower functor theorem.
