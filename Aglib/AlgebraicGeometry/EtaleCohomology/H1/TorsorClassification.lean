/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Classification
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ExtensionFiberTransport
public import Aglib.CategoryTheory.Abelian.Ext1.Representability
public import Aglib.CategoryTheory.Abelian.Ext1.Equality

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorClassification` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9db5444be211c929643b5259966d6bab18f7aeb1d1d9da6c3e101ff4018ce34b`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology

/-!
# Actual fibre representatives of torsor isomorphism classes

Repository basis: `1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e`.
These constructions reuse the actual canonical torsor extension and its fibre
recovery isomorphism. The generic Ext1 representability and equality theorems
construct the quotient inverse in H1-05 of `B03_TORSOR_H1_PLAN.md`.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X}

/-- The existing actual canonical torsor extension with definitionally fixed
coefficient and constant-integer endpoints. -/
abbrev torsorExtensionRepresentative (P : Torsor L) :
    _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf X) L :=
  CategoryTheory.Sheaf.torsorExtensionRepresentative P

/-- The torsor isomorphism class of the actual fibre over integer one in a
short-exact extension with fixed endpoints. -/
def extensionFiberClass
    (E : _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf X) L) :
    TorsorClass L :=
  Quotient.mk (_root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.isomorphicSetoid L)
    (extensionFiberTorsor E.toShortComplex (constantIntegerOne X) E.shortExact)

/-- The original terminal-one fibre class equals the intrinsic class on the same carrier. -/
theorem extensionFiberClass_eq_generic
    (E : CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf X) L) :
    extensionFiberClass E = CategoryTheory.Sheaf.extensionFiberClass E := by
  exact congrArg
    (fun z : Topos.GlobalPoint (underlyingSetSheaf (constantIntegerSheaf X)) =>
      _root_.Quotient.mk (Torsor.isomorphicSetoid L)
        (CategoryTheory.Sheaf.extensionFiberTorsor E.toShortComplex z E.shortExact))
    (constantIntegerOne_asGlobalPoint (X := X))

/-- Identity-endpoint extension isomorphisms give the same actual fibre class. -/
theorem extensionFiberClass_eq_of_iso
    {E E' : _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf X) L}
    (e : _root_.CategoryTheory.Abelian.Ext1.Extension.Iso E E') :
    extensionFiberClass E = extensionFiberClass E' := by
  simpa only [extensionFiberClass_eq_generic] using
    CategoryTheory.Sheaf.extensionFiberClass_eq_of_iso e

/-- The actual fibre of the existing canonical extension recovers the original
torsor isomorphism class. -/
theorem extensionFiberClass_torsorExtension (P : Torsor L) :
    extensionFiberClass (torsorExtensionRepresentative P) =
      Quotient.mk (_root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.isomorphicSetoid L) P :=
  (extensionFiberClass_eq_generic (torsorExtensionRepresentative P)).trans
    (CategoryTheory.Sheaf.extensionFiberClass_torsorExtension P)

section ExtClass
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The fixed-endpoint packaging retains the already constructed torsor class. -/
theorem torsorExtensionRepresentative_extClass (P : Torsor L) :
    (torsorExtensionRepresentative P).extClass = torsorExtClass P :=
  CategoryTheory.Sheaf.torsorExtensionRepresentative_extClass P

/-- The class of any actual extension fibre maps to exactly that extension's
existing Ext class; no class-bijectivity premise is used. -/
theorem torsorClassToH1_extensionFiberClass
    (E : _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf X) L) :
    torsorClassToH1 L (extensionFiberClass E) = E.extClass := by
  simpa only [extensionFiberClass_eq_generic] using
    CategoryTheory.Sheaf.torsorClassToH1_extensionFiberClass E

/-- An actual short-exact extension representing the prescribed H1 class,
chosen from the generic proved Ext1 representability theorem. -/
abbrev h1ExtensionRepresentative (xi : H1Etale X L) :
    _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf X) L :=
  CategoryTheory.Sheaf.h1ExtensionRepresentative xi

/-- The chosen actual extension has exactly the input class. -/
theorem h1ExtensionRepresentative_extClass (xi : H1Etale X L) :
    (h1ExtensionRepresentative xi).extClass = xi :=
  CategoryTheory.Sheaf.h1ExtensionRepresentative_extClass xi

/-- The inverse classifier takes the actual one-fibre of an actual
short-exact representative of the H1 class. -/
def h1ToTorsorClass (L : AbelianSheaf.{u, u + 1} X) :
    H1Etale X L → TorsorClass L :=
  fun xi => extensionFiberClass (h1ExtensionRepresentative xi)

/-- The original terminal-fibre inverse is the single intrinsic representative inverse. -/
theorem h1ToTorsorClass_eq_generic (xi : H1Etale X L) :
    h1ToTorsorClass L xi = CategoryTheory.Sheaf.h1ToTorsorClass L xi :=
  extensionFiberClass_eq_generic (h1ExtensionRepresentative xi)

/-- The fibre of every representative of an H1 class gives the same inverse
class. This proves independence from the selected extension representative. -/
theorem h1ToTorsorClass_eq_extensionFiberClass
    (E : _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf X) L) :
    h1ToTorsorClass L E.extClass = extensionFiberClass E :=
  (h1ToTorsorClass_eq_generic E.extClass).trans
    ((CategoryTheory.Sheaf.h1ToTorsorClass_eq_extensionFiberClass E).trans
      (extensionFiberClass_eq_generic E).symm)

/-- Mapping the chosen actual one-fibre back to H1 recovers the input class. -/
theorem torsorClassToH1_h1ToTorsorClass (xi : H1Etale X L) :
    torsorClassToH1 L (h1ToTorsorClass L xi) = xi :=
  (congrArg (torsorClassToH1 L) (h1ToTorsorClass_eq_generic xi)).trans
    (CategoryTheory.Sheaf.torsorClassToH1_h1ToTorsorClass xi)

/-- The inverse class of the canonical torsor extension is the original
torsor isomorphism class, by identity-endpoint extension comparison. -/
theorem h1ToTorsorClass_torsorClassToH1 (a : TorsorClass L) :
    h1ToTorsorClass L (torsorClassToH1 L a) = a :=
  (h1ToTorsorClass_eq_generic (torsorClassToH1 L a)).trans
    (CategoryTheory.Sheaf.h1ToTorsorClass_torsorClassToH1 a)

/-- The existing canonical torsor-class-to-H1 map is bijective for every
abelian coefficient sheaf and every displayed Ext universe. -/
theorem torsorClassToH1_bijective (L : AbelianSheaf.{u, u + 1} X) :
    Function.Bijective (torsorClassToH1 L) :=
  CategoryTheory.Sheaf.torsorClassToH1_bijective L

/-- Proof of the retained `Stacks03AJ` interface in
`R5Lab/Cohomology/EtaleH1/TorsorClass.lean:158-162` at repository revision
`1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e`, encoding Stacks Project Tag 03AJ,
Lemma 21.4.3 for all abelian sheaves on this small-etale site. The only displayed
existence assumption is `HasExt` at the requested universe; no enough-injectives,
finite-coefficient, Galois, or torsor-classification premise is used. -/
theorem stacks03AJ (X : Scheme.{u})
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] : Stacks03AJ.{u, w} X :=
  ⟨torsorClassToH1_bijective⟩

/-- The existing canonical torsor-class equivalence, now instantiated by the
proved classification theorem rather than a supplied classification premise. -/
def torsorClassEquivProved (L : AbelianSheaf.{u, u + 1} X) :
    TorsorClass L ≃ H1Etale X L :=
  torsorClassEquiv (stacks03AJ X) L

@[simp] theorem torsorClassEquivProved_apply (a : TorsorClass L) :
    torsorClassEquivProved L a = torsorClassToH1 L a := rfl

/-- The existing equivalence's inverse is the actual extension-fibre inverse. -/
theorem torsorClassEquivProved_symm_apply (xi : H1Etale X L) :
    (torsorClassEquivProved L).symm xi = h1ToTorsorClass L xi := by
  apply (torsorClassEquivProved L).injective
  rw [Equiv.apply_symm_apply, torsorClassEquivProved_apply,
    torsorClassToH1_h1ToTorsorClass]

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology
