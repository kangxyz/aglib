/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Pushout
public import Aglib.CategoryTheory.Abelian.Ext1.Representability
public import Aglib.CategoryTheory.Abelian.Ext1.Equality

/-! # The actual torsor and Ext H1 classification

The inverse takes the same explicit one-fibre of one internally chosen actual
Ext1 representative. Identity-endpoint extension isomorphisms prove independence
for every supplied representative. Both inverse laws use the original maps.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w e
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable {L E : Sheaf J AddCommGrpCat.{w}}

variable (P : Torsor L) (r : P.carrier ⟶ underlyingSetSheaf E)

/-- The additive presheaf map freely induced by an actual map of sets. -/
def torsorFreeLiftPresheaf : torsorFreePresheaf P ⟶ E.obj where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift
    (fun t => (show E.obj.obj U from r.hom.app U t)))
  naturality {U V} f := by
    apply AddCommGrpCat.ext
    intro x
    change FreeAbelianGroup.lift (fun t => (show E.obj.obj V from r.hom.app V t))
        (FreeAbelianGroup.map (P.carrier.obj.map f) x) =
      E.obj.map f (FreeAbelianGroup.lift (fun t => (show E.obj.obj U from r.hom.app U t)) x)
    rw [← FreeAbelianGroup.lift_comp]
    have hn : (fun t => (show E.obj.obj V from r.hom.app V (P.carrier.obj.map f t))) =
        (fun t => E.obj.map f (show E.obj.obj U from r.hom.app U t)) :=
      funext (fun t => ConcreteCategory.congr_hom (r.hom.naturality f) t)
    rw [show (fun t => (show E.obj.obj V from r.hom.app V t)) ∘ P.carrier.obj.map f =
      (E.obj.map f).hom ∘ (fun t => (show E.obj.obj U from r.hom.app U t)) from hn]
    exact FreeAbelianGroup.lift_comp_apply _ _ _

/-- The actual free-abelian sheaf map. -/
def torsorFreeLiftSheaf : torsorFreeSheaf P ⟶ E :=
  ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv
    (torsorFreePresheaf P) E).symm (torsorFreeLiftPresheaf P r)

/-- The free-sheaf map has the specified values on generators. -/
theorem torsorFreeLiftSheaf_unit :
    toSheafify J (torsorFreePresheaf P) ≫
      (torsorFreeLiftSheaf P r).hom = torsorFreeLiftPresheaf P r := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorFreeLiftPresheaf P r)) = _
  exact (adj.homEquiv _ _).apply_symm_apply _

variable (i : L ⟶ E)
variable (heq : ∀ U a t, r.hom.app U (P.action U a t) =
  i.hom.app U a + (show E.obj.obj U from r.hom.app U t))

omit [HasSheafify J AddCommGrpCat.{w}] in
include heq in
/-- Equivariance identifies the free-map restriction to the augmentation kernel
with inclusion of the canonical torsor difference. -/
theorem torsorFreeLiftPresheaf_kernel :
    torsorKernelInclusion P ≫ torsorFreeLiftPresheaf P r = torsorKernelDifference P ≫ i.hom := by
  ext U x
  let := P.sectionAction U
  let := (trivialTorsor E).sectionAction U
  have h := AddAction.TorsorAugmentation.kernelDifference_naturality (P.unique_transport U)
    ((trivialTorsor E).unique_transport U) (i.hom.app U).hom (r.hom.app U) (heq U) x
  rw [AddAction.TorsorAugmentation.kernelDifference_eq_based
    ((trivialTorsor E).unique_transport U) (0 : E.obj.obj U)] at h
  have hb : AddAction.TorsorAugmentation.basedDifference ((trivialTorsor E).unique_transport U)
      (0 : E.obj.obj U) = FreeAbelianGroup.lift (fun t : E.obj.obj U => t) := by
    apply FreeAbelianGroup.lift_ext
    intro t
    change (E.obj.obj U : Type w) at t
    rw [AddAction.TorsorAugmentation.basedDifference_of]
    change AddAction.TorsorAugmentation.difference ((trivialTorsor E).unique_transport U)
        t (0 : E.obj.obj U) =
      FreeAbelianGroup.lift (fun t : E.obj.obj U => t) (FreeAbelianGroup.of t)
    rw [FreeAbelianGroup.lift_apply_of]
    exact AddAction.TorsorAugmentation.difference_eq _ t (0 : E.obj.obj U)
      (show E.obj.obj U from t)
      (add_zero (show E.obj.obj U from t))
  rw [hb] at h
  change FreeAbelianGroup.lift (fun t => (show E.obj.obj U from r.hom.app U t)) x.val = _
  exact (FreeAbelianGroup.lift_comp
    (fun t => (show E.obj.obj U from r.hom.app U t)) (fun t : E.obj.obj U => t) x.val).trans h

include heq in
/-- The sheafified kernel square follows from the actual adjunction. -/
theorem torsorFreeLiftSheaf_kernel :
    torsorKernelSheafInclusion P ≫ torsorFreeLiftSheaf P r = torsorDifferenceSheafMap P ≫ i := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  apply (adj.homEquiv (torsorKernelPresheaf P) E).injective
  change adj.homEquiv _ _
      ((presheafToSheaf J AddCommGrpCat.{w}).map
        (torsorKernelInclusion P) ≫ (adj.homEquiv _ _).symm (torsorFreeLiftPresheaf P r)) =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorKernelDifference P) ≫ i)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact torsorFreeLiftPresheaf_kernel P r i heq

variable (g : E ⟶ constantIntegerSheaf J)
variable (hover : ∀ U t, g.hom.app U (r.hom.app U t) =
  (constantIntegerOne J).hom.app U PUnit.unit)

include hover in
/-- An actual lift into the augmentation-one fibre commutes with augmentation. -/
theorem torsorFreeLiftPresheaf_projection :
    torsorFreeLiftPresheaf P r ≫ g.hom = torsorAugmentationPresheaf P ≫
      toSheafify J
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ))) := by
  ext U x
  change g.hom.app U
      (FreeAbelianGroup.lift (fun t => (show E.obj.obj U from r.hom.app U t)) x) =
    (toSheafify J
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)))).app U
        (FreeAbelianGroup.lift (fun _ : P.carrier.obj.obj U => (1 : ULift.{w} ℤ)) x)
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]
  | of t =>
    rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      hover, constantIntegerOne_app]
    rfl
  | neg t ht => simp only [map_neg, ht]
  | add x y hx hy => simp only [map_add, hx, hy]

include hover in
/-- The actual free-sheaf morphism lies over the identity of constant ℤ. -/
theorem torsorFreeLiftSheaf_projection :
    torsorFreeLiftSheaf P r ≫ g = torsorAugmentation P := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  apply (adj.homEquiv (torsorFreePresheaf P) (constantIntegerSheaf J)).injective
  rw [Adjunction.homEquiv_naturality_right]
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorFreeLiftPresheaf P r)) ≫ g.hom = _
  rw [Equiv.apply_symm_apply]
  change torsorFreeLiftPresheaf P r ≫ g.hom =
    toSheafify J (torsorFreePresheaf P) ≫
      (torsorAugmentation P).hom
  exact (torsorFreeLiftPresheaf_projection P r g hover).trans
    (toSheafify_naturality J (torsorAugmentationPresheaf P))

variable (hig : i ≫ g = 0)

/-- The actual augmentation sequence maps to the given extension. -/
def torsorAugmentationToExtension :
    torsorAugmentationComplex P ⟶ ShortComplex.mk i g hig where
  τ₁ := torsorDifferenceSheafMap P
  τ₂ := torsorFreeLiftSheaf P r
  τ₃ := 𝟙 _
  comm₁₂ := (torsorFreeLiftSheaf_kernel P r i heq).symm
  comm₂₃ := by
    change torsorFreeLiftSheaf P r ≫ g = torsorAugmentation P ≫ 𝟙 _
    rw [Category.comp_id]
    exact torsorFreeLiftSheaf_projection P r g hover

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

section ExtClass
variable [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

include r heq hover in
/-- A coefficient-equivariant map into an augmentation-one extension fibre
identifies the canonical class with that actual short exact extension. -/
theorem torsorExtClass_of_extensionLift (hS : (ShortComplex.mk i g hig).ShortExact) :
    torsorExtClass P = hS.extClass := by
  have hn := ShortComplex.ShortExact.extClass_naturality
    (torsorAugmentation_shortExact P) hS
    (torsorAugmentationToExtension P r i heq g hover hig)
  change (torsorAugmentation_shortExact P).extClass.comp
      (Abelian.Ext.mk₀ (torsorDifferenceSheafMap P)) (add_zero 1) =
    (Abelian.Ext.mk₀ (𝟙 _)).comp hS.extClass (zero_add 1) at hn
  rw [Abelian.Ext.mk₀_id_comp] at hn
  exact (torsorExtClass_eq P).trans hn

end ExtClass

variable {P r heq hover}

section ExtClass
variable [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- The augmentation-one fibre of an actual short exact extension has exactly
that extension's canonical Ext class, with no bijectivity assumption. -/
theorem torsorExtClass_extensionFiber (hS : (ShortComplex.mk i g hig).ShortExact) :
    torsorExtClass (extensionFiberTorsor (ShortComplex.mk i g hig) (constantIntegerOne J) hS) =
      hS.extClass :=
  torsorExtClass_of_extensionLift
    (extensionFiberTorsor (ShortComplex.mk i g hig) (constantIntegerOne J) hS)
    (extensionFiberInclusion (ShortComplex.mk i g hig) (constantIntegerOne J)) i
    (fun _ _ _ => rfl) g
    (fun _ t => t.property) hig hS

end ExtClass

section FiberTransport
variable {F : Sheaf J AddCommGrpCat.{w}}

/-- The middle sheaf map of an identity-endpoint extension isomorphism restricts
to an equivariant map on the actual fibres over the same global section. -/
def extensionFiberHom
    {E E' : _root_.CategoryTheory.Abelian.Ext1.Extension F L}
    (e : _root_.CategoryTheory.Abelian.Ext1.Extension.Iso E E')
    (z : Topos.GlobalPoint (underlyingSetSheaf F)) :
    Torsor.Hom (𝟙 L)
      (extensionFiberTorsor E.toShortComplex z E.shortExact)
      (extensionFiberTorsor E'.toShortComplex z E'.shortExact) where
  map := ⟨{
    app U := TypeCat.ofHom (fun t => ⟨e.middleIso.hom.hom.app U t.val, by
      exact (congrArg (fun q : E.middle ⟶ F =>
        q.hom.app U (show E.middle.obj.obj U from t.val)) e.comm_p).trans t.property⟩)
    naturality {U V} f := by
      ext t
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (e.middleIso.hom.hom.naturality f) t.val }⟩
  equivariant U a t := by
    apply Subtype.ext
    change e.middleIso.hom.hom.app U
      (E.i.hom.app U a + (show E.middle.obj.obj U from t.val)) =
      E'.i.hom.app U a + e.middleIso.hom.hom.app U t.val
    rw [map_add]
    exact congrArg (· + e.middleIso.hom.hom.app U t.val)
      (congrArg (fun q : L ⟶ E'.middle => q.hom.app U a) e.comm_i)

/-- Identity-endpoint isomorphic short-exact extensions have equivariantly
isomorphic fibre torsors, with no Ext or cohomology classification input. -/
def extensionFiberIso
    {E E' : _root_.CategoryTheory.Abelian.Ext1.Extension F L}
    (e : _root_.CategoryTheory.Abelian.Ext1.Extension.Iso E E')
    (z : Topos.GlobalPoint (underlyingSetSheaf F)) :
    Torsor.Iso
      (extensionFiberTorsor E.toShortComplex z E.shortExact)
      (extensionFiberTorsor E'.toShortComplex z E'.shortExact) :=
  (extensionFiberHom e z).toIso

end FiberTransport

/-- The existing actual canonical torsor extension with definitionally fixed
coefficient and constant-integer endpoints. -/
def torsorExtensionRepresentative (P : Torsor L) :
    _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf J) L where
  middle := (torsorExtension P).X₂
  i := (torsorExtension P).f
  p := (torsorExtension P).g
  zero := (torsorExtension P).zero
  shortExact := torsorExtension_shortExact P

/-- The torsor isomorphism class of the actual fibre over integer one in a
short-exact extension with fixed endpoints. -/
def extensionFiberClass
    (E : _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf J) L) :
    TorsorClass L :=
  _root_.Quotient.mk (Torsor.isomorphicSetoid L)
    (extensionFiberTorsor E.toShortComplex (constantIntegerOne J) E.shortExact)

/-- Identity-endpoint extension isomorphisms give the same actual fibre class. -/
theorem extensionFiberClass_eq_of_iso
    {E E' : _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf J) L}
    (e : _root_.CategoryTheory.Abelian.Ext1.Extension.Iso E E') :
    extensionFiberClass E = extensionFiberClass E' :=
  _root_.Quotient.sound ⟨extensionFiberIso e (constantIntegerOne J)⟩

/-- The actual fibre of the existing canonical extension recovers the original
torsor isomorphism class. -/
theorem extensionFiberClass_torsorExtension (P : Torsor L) :
    extensionFiberClass (torsorExtensionRepresentative P) =
      _root_.Quotient.mk (Torsor.isomorphicSetoid L) P :=
  _root_.Quotient.sound ⟨(torsorCanonicalExtensionIso P).symm⟩

section ExtClass
variable [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- The fixed-endpoint packaging retains the already constructed torsor class. -/
theorem torsorExtensionRepresentative_extClass (P : Torsor L) :
    (torsorExtensionRepresentative P).extClass = torsorExtClass P := rfl

/-- The class of any actual extension fibre maps to exactly that extension's
existing Ext class; no class-bijectivity premise is used. -/
theorem torsorClassToH1_extensionFiberClass
    (E : _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf J) L) :
    torsorClassToH1 L (extensionFiberClass E) = E.extClass :=
  torsorExtClass_extensionFiber E.i E.p E.zero E.shortExact

/-- An actual short-exact extension representing the prescribed H1 class,
chosen from the generic proved Ext1 representability theorem. -/
def h1ExtensionRepresentative (xi : H L 1) :
    _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf J) L :=
  Classical.choose (_root_.CategoryTheory.Abelian.Ext1.exists_extension xi)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The chosen actual extension has exactly the input class. -/
theorem h1ExtensionRepresentative_extClass (xi : H L 1) :
    (h1ExtensionRepresentative xi).extClass = xi :=
  Classical.choose_spec (_root_.CategoryTheory.Abelian.Ext1.exists_extension xi)

/-- The inverse classifier takes the actual one-fibre of an actual
short-exact representative of the H1 class. -/
def h1ToTorsorClass (L : Sheaf J AddCommGrpCat.{w}) :
    H L 1 → TorsorClass L :=
  fun xi => extensionFiberClass (h1ExtensionRepresentative xi)

/-- The fibre of every representative of an H1 class gives the same inverse
class. This proves independence from the selected extension representative. -/
theorem h1ToTorsorClass_eq_extensionFiberClass
    (E : _root_.CategoryTheory.Abelian.Ext1.Extension (constantIntegerSheaf J) L) :
    h1ToTorsorClass L E.extClass = extensionFiberClass E := by
  obtain ⟨e⟩ := _root_.CategoryTheory.Abelian.Ext1.extClass_eq_iso
    (h1ExtensionRepresentative E.extClass) E
    (h1ExtensionRepresentative_extClass E.extClass)
  exact extensionFiberClass_eq_of_iso e

/-- Mapping the chosen actual one-fibre back to H1 recovers the input class. -/
theorem torsorClassToH1_h1ToTorsorClass (xi : H L 1) :
    torsorClassToH1 L (h1ToTorsorClass L xi) = xi := by
  exact (torsorClassToH1_extensionFiberClass (h1ExtensionRepresentative xi)).trans
    (h1ExtensionRepresentative_extClass xi)

/-- The inverse class of the canonical torsor extension is the original
torsor isomorphism class, by identity-endpoint extension comparison. -/
theorem h1ToTorsorClass_torsorClassToH1 (a : TorsorClass L) :
    h1ToTorsorClass L (torsorClassToH1 L a) = a := by
  induction a using _root_.Quotient.inductionOn with
  | h P =>
    change h1ToTorsorClass L (torsorExtensionRepresentative P).extClass =
      _root_.Quotient.mk (Torsor.isomorphicSetoid L) P
    exact (h1ToTorsorClass_eq_extensionFiberClass (torsorExtensionRepresentative P)).trans
      (extensionFiberClass_torsorExtension P)

/-- The existing canonical torsor-class-to-H1 map is bijective for every
abelian coefficient sheaf and every displayed Ext universe. -/
theorem torsorClassToH1_bijective (L : Sheaf J AddCommGrpCat.{w}) :
    Function.Bijective (torsorClassToH1 L) :=
  ⟨Function.LeftInverse.injective h1ToTorsorClass_torsorClassToH1,
    Function.RightInverse.surjective torsorClassToH1_h1ToTorsorClass⟩

/-- The proved equivalence uses the one actual-extension representative inverse. -/
def torsorClassEquiv (L : Sheaf J AddCommGrpCat.{w}) : TorsorClass L ≃ H L 1 where
  toFun := torsorClassToH1 L
  invFun := h1ToTorsorClass L
  left_inv := h1ToTorsorClass_torsorClassToH1
  right_inv := torsorClassToH1_h1ToTorsorClass

@[simp] theorem torsorClassEquiv_apply (a : TorsorClass L) :
    torsorClassEquiv L a = torsorClassToH1 L a := rfl

@[simp] theorem torsorClassEquiv_symm_apply (xi : H L 1) :
    (torsorClassEquiv L).symm xi = h1ToTorsorClass L xi := rfl

end ExtClass
end CategoryTheory.Sheaf
