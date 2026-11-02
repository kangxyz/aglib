# Epimorphisms from the actual structure module

For an integral scheme `X`, an arbitrary module sheaf `M`, and an actual
epimorphism `φ : O_X → M`, `isIso_unitHom_of_epi_of_generic_mem_support`
proves `IsIso φ` when the original generic stalk of `M` is nonzero.
No quasicoherence, finite type, finite presentation, local freeness,
Noetherianity or properness hypothesis is needed.

`germ_unitHom_app` is the scalar formula for the original section and germ
maps, using the existing unit-Hom/global-section equivalence. Epimorphy on
the original stalk implies that the generator germ is nonzero at every
point of the target support. Over the function field, multiplication by
this nonzero vector is injective. Integral structure-ring germs then
detect the sectionwise kernel; sheaf separatedness also covers the empty
open. The original arrow is both mono and epi, hence an isomorphism.
No new stalk realization, unit-stalk comparison or choice of a generic
frame is constructed.

The surface-canonical consumer has nonzero generic stalk from
`normalSurface_generic_mem_support`. Once its genuine canonical
evaluation map, transported through the parent frame, is proved epi,
this lemma gives the actual global frame without first assuming that
the child canonical sheaf is invertible or that the child is Gorenstein.
It does not prove that evaluation is epi, and it does not produce the
exceptional-curve canonical identification on its own.
