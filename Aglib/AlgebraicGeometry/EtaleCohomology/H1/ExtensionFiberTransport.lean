/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Classification
public import Aglib.CategoryTheory.Abelian.Ext1.Extension
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorPullback

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.ExtensionFiberTransport`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e01d7f1b9bdffd7cdcffcba34b7f452ad6762d7c41178ef8a5b97ca062079b19`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology

/-!
# Transport of actual extension fibres

On repository basis `1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e`, an
identity-endpoint isomorphism of short-exact abelian sheaf extensions restricts
to an equivariant isomorphism of their actual fibres over any global section.
This implements H1-04 of `B03_TORSOR_H1_PLAN.md` without any classification
premise. The existing extension-fibre and torsor-map constructions are reused.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {F L : AbelianSheaf.{u, u + 1} X}

/-- The middle sheaf map of an identity-endpoint extension isomorphism restricts
to an equivariant map on the actual fibres over the same global section. -/
abbrev extensionFiberHom
    {E E' : _root_.CategoryTheory.Abelian.Ext1.Extension F L}
    (e : _root_.CategoryTheory.Abelian.Ext1.Extension.Iso E E')
    (z : F.obj.obj (op (etaleTerminal X))) :
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.Hom (𝟙 L)
      (extensionFiberTorsor E.toShortComplex z E.shortExact)
      (extensionFiberTorsor E'.toShortComplex z E'.shortExact) :=
  CategoryTheory.Sheaf.extensionFiberHom e
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X)
      (underlyingSetSheaf F)).symm z)

/-- Identity-endpoint isomorphic short-exact extensions have equivariantly
isomorphic fibre torsors, with no Ext or cohomology classification input. -/
abbrev extensionFiberIso
    {E E' : _root_.CategoryTheory.Abelian.Ext1.Extension F L}
    (e : _root_.CategoryTheory.Abelian.Ext1.Extension.Iso E E')
    (z : F.obj.obj (op (etaleTerminal X))) :
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.Iso
      (extensionFiberTorsor E.toShortComplex z E.shortExact)
      (extensionFiberTorsor E'.toShortComplex z E'.shortExact) :=
  CategoryTheory.Sheaf.extensionFiberIso e
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X)
      (underlyingSetSheaf F)).symm z)

end AlgebraicGeometry.Scheme.EtaleCohomology
