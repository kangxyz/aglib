# Proper henselian sections and degree-zero cohomology

For a henselian local ring `R`, a proper `p : X ⟶ Spec R`, and a finite
additive commutative group `A`, let
`i := pullback.fst p (LocalRing.residueSpecMap R)` be the actual closed-residue
fibre arrow. The original sections map of the constant coefficient is
bijective. So is the original `Sheaf.H` degree-zero map, after its canonical
constant-inverse-image comparison:

- [ProperHenselian](ProperHenselian.lean) supplies
  `properHenselian_originalSections_bijective`,
  `properHenselian_pullbackSections_bijective`, and
  `properHenselian_pullbackH0_bijective`.
- [ProperHenselian/Sections](ProperHenselian/Sections.lean) retains the actual
  finite-cover sections comparison used by those endpoints.

The coefficient is the native constant sheaf with value
`AddCommGrpCat.of (ULift.{u+1} A)`. Section bijectivity needs no Ext premise;
for original `H0`, the source and closed-fibre `HasExt` universes `w` and `w'`
are explicit. No Noetherian, order-invertibility, finite-presentation,
excellence, completion, flatness, or residue-field-closure assumption is
added. The same section argument proves bijectivity for every actual finite
locally constant abelian sheaf; see the [finite-constant H1 owner](../H1/ConstantFinite/README.md)
for the corresponding H1 extension. This is a bounded coefficient result, not
an arbitrary-sheaf proper-base-change theorem.
