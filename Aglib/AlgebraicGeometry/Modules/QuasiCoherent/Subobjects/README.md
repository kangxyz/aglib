# Quasicoherent subobjects on opens

The modules use `Scheme.Modules.QuasiCoherent` and the actual module-sheaf subobjects.

- [Gluing](Gluing.lean) proves `exists_quasicoherent_glued_subobject` on a locally Noetherian
  scheme. The ambient module and both local subobjects are quasicoherent; the compatible
  inclusions are monomorphisms. The two open immersions need not cover the scheme.
- [Preimage](Preimage.lean) proves `quasicoherent_subobject_preimage` for an open immersion
  between locally Noetherian schemes. A finite-type subobject on the open lifts to a
  quasicoherent subobject of the specified quasicoherent ambient sheaf, with its actual
  restriction isomorphism and commuting inclusion equation.

The lower [module-subobject gluing](../../Subobjects/README.md) uses the same obstruction
maps and chosen pullback. [Coherent extension](../../Coherent/Extension/README.md) adds
finiteness of the extended object under the stated hypotheses.
