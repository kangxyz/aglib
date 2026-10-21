/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.DualIsogeny
public import Aglib.AlgebraicGeometry.Group.Kernel.DeckTranslation
public import Aglib.AlgebraicGeometry.Picard.FrameTensor
public import Aglib.AlgebraicGeometry.Picard.PowerBaseChange
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Evaluation characters from actual frames and kernel translations

Positive transport in the existing sheaf of O-linear frames supplies the
evaluation scalar. The construction retains the actual translation maps
and the native global constants map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology
open _root_.GroupCohomology.Kummer.Coefficients

universe u v

namespace AlgebraicGeometry.Scheme.Group.IsogenyPairing

namespace Transport

open Scheme.Modules.Invertible.AssociatedBundle Scheme.Modules.Invertible.UnitDescent

variable {X : Scheme.{u}} (P : Torsor (gm X)) (U : X.Etale)
variable {H : Type v} [Group H] (ρ : H →* Aut U)
variable (hunit : ∀ g : H, ∀ a : Γ(U.left, ⊤)ˣ, pullUnit (ρ g).hom.left a = a)

/-- The literal positive transport from a frame to its deck pullback. -/
def scalar (s : P.carrier.obj.obj (op U)) (g : H) : Γ(U.left, ⊤)ˣ :=
  transportUnit P (op U) s (P.carrier.obj.map (ρ g).hom.op s)

include hunit in
/-- Positive transport is multiplicative when deck maps fix the global units. -/
theorem scalar_mul (s : P.carrier.obj.obj (op U)) (g h : H) :
    scalar P U ρ s (g * h) = scalar P U ρ s g * scalar P U ρ s h := by
  have hm : P.carrier.obj.map (ρ (g * h)).hom.op s =
      P.carrier.obj.map (ρ h).hom.op (P.carrier.obj.map (ρ g).hom.op s) := by
    rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom, op_comp, CategoryTheory.Functor.map_comp]
    rfl
  dsimp only [scalar]
  rw [hm]
  rw [← transportUnit_trans P (op U) s (P.carrier.obj.map (ρ h).hom.op s)]
  rw [← transportUnit_naturality P (ρ h).hom.op]
  change scalar P U ρ s h * pullUnit (ρ h).hom.left (scalar P U ρ s g) =
    scalar P U ρ s g * scalar P U ρ s h
  rw [hunit, mul_comm]

/-- The character supplied by a chosen torsor frame. -/
def character (s : P.carrier.obj.obj (op U)) : H →* Γ(U.left, ⊤)ˣ where
  toFun := scalar P U ρ s
  map_one' := by
    simp only [scalar, map_one]
    change transportUnit P (op U) s (P.carrier.obj.map (𝟙 (op U)) s) = 1
    rw [CategoryTheory.Functor.map_id]
    exact transportUnit_self P (op U) s
  map_mul' := scalar_mul P U ρ hunit s

include hunit in
/-- The evaluation character is independent of the chosen frame. -/
theorem scalar_independent (s t : P.carrier.obj.obj (op U)) (g : H) :
    scalar P U ρ s g = scalar P U ρ t g := by
  let rs := P.carrier.obj.map (ρ g).hom.op s
  let rt := P.carrier.obj.map (ρ g).hom.op t
  have hn : transportUnit P (op U) rs rt = transportUnit P (op U) s t := by
    exact (transportUnit_naturality P (ρ g).hom.op s t).symm.trans (hunit g _)
  have h₁ := transportUnit_trans P (op U) s t rt
  have h₂ := transportUnit_trans P (op U) s rs rt
  rw [hn] at h₂
  apply mul_right_cancel (b := transportUnit P (op U) s t)
  change transportUnit P (op U) s rs * transportUnit P (op U) s t =
    transportUnit P (op U) t rt * transportUnit P (op U) s t
  rw [h₂, mul_comm (transportUnit P (op U) t rt), h₁]

/-- Equivariant torsor isomorphisms preserve the literal positive transport. -/
theorem transportUnit_iso {Q : Torsor (gm X)} (e : Torsor.Iso P Q)
    (s t : P.carrier.obj.obj (op U)) :
    transportUnit Q (op U) (e.carrierIso.hom.hom.app (op U) s)
      (e.carrierIso.hom.hom.app (op U) t) = transportUnit P (op U) s t := by
  have ht : transport Q (op U) (e.carrierIso.hom.hom.app (op U) s)
      (e.carrierIso.hom.hom.app (op U) t) = transport P (op U) s t := by
    apply transport_eq
    rw [← e.equivariant, action_transport]
  simp only [transportUnit, ht]

/-- Positive evaluation is natural under an actual equivariant torsor
isomorphism, before any frame is selected. -/
theorem scalar_iso {Q : Torsor (gm X)} (e : Torsor.Iso P Q)
    (s : P.carrier.obj.obj (op U)) (g : H) :
    scalar P U ρ s g = scalar Q U ρ (e.carrierIso.hom.hom.app (op U) s) g := by
  have hn : e.carrierIso.hom.hom.app (op U) (P.carrier.obj.map (ρ g).hom.op s) =
      Q.carrier.obj.map (ρ g).hom.op (e.carrierIso.hom.hom.app (op U) s) :=
    congrArg (fun a => a s) (e.carrierIso.hom.hom.naturality (ρ g).hom.op)
  dsimp only [scalar]
  rw [← hn, transportUnit_iso]

include hunit in
/-- Frame-independent evaluation agrees on equivariantly isomorphic torsors. -/
theorem scalar_iso_independent {Q : Torsor (gm X)} (e : Torsor.Iso P Q)
    (s : P.carrier.obj.obj (op U)) (t : Q.carrier.obj.obj (op U)) (g : H) :
    scalar P U ρ s g = scalar Q U ρ t g :=
  (scalar_iso P U ρ e s g).trans (scalar_independent Q U ρ hunit _ t g)

open Scheme.Modules.Invertible.EtaleDescent Scheme.Modules.Invertible.FrameTorsor

/-- Positive transport in tensor frames is the product of the two
literal transport units. -/
theorem frameTransport_tensor (L M : LineBundle X)
    (s s' : (frameSheaf etaleLineBundleDescent X L).obj.obj (op U))
    (t t' : (frameSheaf etaleLineBundleDescent X M).obj.obj (op U)) :
    transportUnit (frameTorsor etaleLineBundleDescent X (tensorLineBundle X L M)) (op U)
      (FrameTensor.tensorSection etaleLineBundleDescent X L M (op U) s t)
      (FrameTensor.tensorSection etaleLineBundleDescent X L M (op U) s' t') =
    transportUnit (frameTorsor etaleLineBundleDescent X L) (op U) s s' *
      transportUnit (frameTorsor etaleLineBundleDescent X M) (op U) t t' := by
  let a := transport (frameTorsor etaleLineBundleDescent X L) (op U) s s'
  let b := transport (frameTorsor etaleLineBundleDescent X M) (op U) t t'
  have ht : transport (frameTorsor etaleLineBundleDescent X (tensorLineBundle X L M)) (op U)
      (FrameTensor.tensorSection etaleLineBundleDescent X L M (op U) s t)
      (FrameTensor.tensorSection etaleLineBundleDescent X L M (op U) s' t') = a + b := by
    apply transport_eq
    change frameAction etaleLineBundleDescent X (tensorLineBundle X L M) (op U) (a + b)
      (FrameTensor.tensorSection etaleLineBundleDescent X L M (op U) s t) = _
    rw [← FrameTensor.tensorSection_equivariant]
    have ha := action_transport (frameTorsor etaleLineBundleDescent X L) (op U) s s'
    have hb := action_transport (frameTorsor etaleLineBundleDescent X M) (op U) t t'
    change frameAction etaleLineBundleDescent X L (op U) a s = s' at ha
    change frameAction etaleLineBundleDescent X M (op U) b t = t' at hb
    rw [ha, hb]
  dsimp only [transportUnit]
  rw [ht]
  exact congrArg Additive.toMul ((unitsSections X (op U)).map_add a b)

/-- Pullback of tensor frames and their positive transport give the
product character, with the native tensor comparison maps. -/
theorem scalar_tensor (L M : LineBundle X)
    (s : (frameSheaf etaleLineBundleDescent X L).obj.obj (op U))
    (t : (frameSheaf etaleLineBundleDescent X M).obj.obj (op U)) (g : H) :
    scalar (frameTorsor etaleLineBundleDescent X (tensorLineBundle X L M)) U ρ
      (FrameTensor.tensorSection etaleLineBundleDescent X L M (op U) s t) g =
    scalar (frameTorsor etaleLineBundleDescent X L) U ρ s g *
      scalar (frameTorsor etaleLineBundleDescent X M) U ρ t g := by
  dsimp only [scalar]
  exact (congrArg (transportUnit
    (frameTorsor etaleLineBundleDescent X (tensorLineBundle X L M)) (op U)
      (FrameTensor.tensorSection etaleLineBundleDescent X L M (op U) s t))
    (FrameTensor.tensorSection_naturality etaleLineBundleDescent X L M (ρ g).hom.op s t)).trans
      (frameTransport_tensor U L M s _ t _)

end Transport

namespace FramePullback

open Scheme.Modules.Invertible.EtaleDescent Scheme.Modules.Invertible.FrameTorsor
open Scheme.Modules.Invertible.AssociatedBundle Scheme.Modules.Invertible.UnitDescent
open Scheme.Modules.Invertible.PowerBaseChange
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPowerTorsor (nativePullFrame)

variable {X S : Scheme.{u}} (a : S ⟶ X) (L : LineBundle X)
variable (U : X.Etale) (V : S.Etale) (b : V.left ⟶ U.left)
variable (w : b ≫ U.hom = V.hom ≫ a)

/-- Pullback of an actual O-linear frame along an actual commuting square. -/
def sectionMap (s : (frameSheaf etaleLineBundleDescent X L).obj.obj (op U)) :
    (frameSheaf etaleLineBundleDescent S (pullbackLineBundle a L)).obj.obj (op V) :=
  (frameSectionsEquiv etaleLineBundleDescent S (pullbackLineBundle a L) (op V)).symm
    (pullbackFrame a L U.hom V.hom b w
      (frameSectionsEquiv etaleLineBundleDescent X L (op U) s))

@[simp] theorem sectionMap_sections
    (s : (frameSheaf etaleLineBundleDescent X L).obj.obj (op U)) :
    frameSectionsEquiv etaleLineBundleDescent S (pullbackLineBundle a L) (op V)
      (sectionMap a L U V b w s) =
    pullbackFrame a L U.hom V.hom b w
      (frameSectionsEquiv etaleLineBundleDescent X L (op U) s) :=
  (frameSectionsEquiv etaleLineBundleDescent S (pullbackLineBundle a L) (op V)).apply_symm_apply _

/-- Positive scalar postcomposition follows the literal map on global units. -/
theorem sectionMap_action (c : (gm X).obj.obj (op U))
    (s : (frameSheaf etaleLineBundleDescent X L).obj.obj (op U)) :
    sectionMap a L U V b w (frameAction etaleLineBundleDescent X L (op U) c s) =
      frameAction etaleLineBundleDescent S (pullbackLineBundle a L) (op V)
        ((unitsSections S (op V)).symm
          (Additive.ofMul (pullUnit b (unitsSections X (op U) c).toMul)))
        (sectionMap a L U V b w s) := by
  apply (frameSectionsEquiv etaleLineBundleDescent S (pullbackLineBundle a L) (op V)).injective
  rw [sectionMap_sections, frameAction_sections, frameAction_sections, sectionMap_sections,
    AddEquiv.apply_symm_apply]
  exact pullbackFrame_scalar a L U.hom V.hom b w
    (frameSectionsEquiv etaleLineBundleDescent X L (op U) s)
    (unitsSections X (op U) c).toMul

/-- Positive transport between frames commutes with arbitrary scheme
pullback, with the actual structural global-unit map. -/
theorem transportUnit_naturality
    (s t : (frameSheaf etaleLineBundleDescent X L).obj.obj (op U)) :
    transportUnit (frameTorsor etaleLineBundleDescent S (pullbackLineBundle a L)) (op V)
        (sectionMap a L U V b w s) (sectionMap a L U V b w t) =
      pullUnit b (transportUnit (frameTorsor etaleLineBundleDescent X L) (op U) s t) := by
  let P := frameTorsor etaleLineBundleDescent X L
  let Q := frameTorsor etaleLineBundleDescent S (pullbackLineBundle a L)
  let c := transport P (op U) s t
  let c' := (unitsSections S (op V)).symm
    (Additive.ofMul (pullUnit b (unitsSections X (op U) c).toMul))
  have ha := sectionMap_action a L U V b w c s
  have hst : frameAction etaleLineBundleDescent X L (op U) c s = t :=
    action_transport P (op U) s t
  rw [hst] at ha
  have ht : transport Q (op V) (sectionMap a L U V b w s)
      (sectionMap a L U V b w t) = c' :=
    transport_eq Q (op V) _ _ c' ha.symm
  change (unitsSections S (op V) (transport Q (op V) _ _)).toMul = _
  rw [ht]
  exact congrArg Additive.toMul ((unitsSections S (op V)).apply_symm_apply _)

/-- The frame pullback map intertwines the actual commuting deck maps. -/
theorem sectionMap_deck (i : Aut U) (j : Aut V)
    (hij : j.hom.left ≫ b = b ≫ i.hom.left)
    (s : (frameSheaf etaleLineBundleDescent X L).obj.obj (op U)) :
    (frameSheaf etaleLineBundleDescent S (pullbackLineBundle a L)).obj.map j.hom.op
      (sectionMap a L U V b w s) =
    sectionMap a L U V b w ((frameSheaf etaleLineBundleDescent X L).obj.map i.hom.op s) := by
  apply (frameSectionsEquiv etaleLineBundleDescent S (pullbackLineBundle a L) (op V)).injective
  rw [FrameTensor.frameSections_restriction, sectionMap_sections, sectionMap_sections,
    FrameTensor.frameSections_restriction]
  change nativePullFrame (pullbackLineBundle a L) V.hom V.hom j.hom.left j.hom.w
      (pullbackFrame a L U.hom V.hom b w
        (frameSectionsEquiv etaleLineBundleDescent X L (op U) s)) =
    pullbackFrame a L U.hom V.hom b w
      (nativePullFrame L U.hom U.hom i.hom.left i.hom.w
        (frameSectionsEquiv etaleLineBundleDescent X L (op U) s))
  rw [pullbackFrame_restriction]
  unfold pullbackFrame
  rw [nativePullFrame_comp]
  simp only [hij]

/-- Positive evaluation along commuting actual deck maps follows the
actual pullback of units. This is the geometric scalar comparison used
for field and semilinear specialization. -/
theorem evaluation_naturality (i : Aut U) (j : Aut V)
    (hij : j.hom.left ≫ b = b ≫ i.hom.left)
    (s : (frameSheaf etaleLineBundleDescent X L).obj.obj (op U)) :
    transportUnit (frameTorsor etaleLineBundleDescent S (pullbackLineBundle a L)) (op V)
        (sectionMap a L U V b w s)
        ((frameSheaf etaleLineBundleDescent S (pullbackLineBundle a L)).obj.map j.hom.op
          (sectionMap a L U V b w s)) =
      pullUnit b (transportUnit (frameTorsor etaleLineBundleDescent X L) (op U) s
        ((frameSheaf etaleLineBundleDescent X L).obj.map i.hom.op s)) := by
  rw [sectionMap_deck a L U V b w i j hij]
  exact transportUnit_naturality a L U V b w s _

end FramePullback

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {E D : Grp (FScheme k)} (f : E ⟶ D)

/-- Rational points of the actual categorical kernel group scheme. -/
abbrev KernelPoints := 𝟙_ (FScheme k) ⟶ (Scheme.Group.Kernel.group f).X

/-- Send a kernel point to translation by its image in the original source group scheme. -/
def kernelTranslationHom : KernelPoints f →* End E.X :=
  Translation.translationHom.comp
    (IsMonHom.monoidHom (Scheme.Group.Kernel.inclusion f).hom.hom (𝟙_ (FScheme k)))

theorem kernelTranslation_over (x : KernelPoints f) :
    kernelTranslationHom f x ≫ f.hom.hom = f.hom.hom := by
  have hx : (x ≫ (Scheme.Group.Kernel.inclusion f).hom.hom) ≫ f.hom.hom = 1 := by
    rw [Category.assoc, (Scheme.Group.Kernel.square f).w]
    simp only [← Category.assoc, comp_toUnit, Hom.one_def]
  change Translation.translation (x ≫ (Scheme.Group.Kernel.inclusion f).hom.hom) ≫
    f.hom.hom = f.hom.hom
  rw [Translation.translation, MonObj.mul_comp, Category.assoc, hx, MonObj.comp_one,
    Category.id_comp, _root_.one_mul]

variable [Etale f.hom.hom.left]

/-- The original étale group morphism as an object of the target scheme's étale site. -/
def cover : D.X.left.Etale := Scheme.Etale.mk f.hom.hom.left

/-- The actual kernel translation as a deck automorphism of the etale cover. -/
def kernelDeckAut (x : KernelPoints f) : Aut (cover f) where
  hom := MorphismProperty.Over.homMk (kernelTranslationHom f x).left
    (congrArg Over.Hom.left (kernelTranslation_over f x)) (by trivial)
  inv := MorphismProperty.Over.homMk (kernelTranslationHom f x⁻¹).left
    (congrArg Over.Hom.left (kernelTranslation_over f x⁻¹)) (by trivial)
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    have h : kernelTranslationHom f x ≫ kernelTranslationHom f x⁻¹ = 𝟙 E.X := by
      simpa only [inv_mul_cancel, map_one, End.one_def, End.mul_def] using
        ((kernelTranslationHom f).map_mul x⁻¹ x).symm
    exact congrArg (fun q : E.X ⟶ E.X => q.left) h
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    have h : kernelTranslationHom f x⁻¹ ≫ kernelTranslationHom f x = 𝟙 E.X := by
      simpa only [mul_inv_cancel, map_one, End.one_def, End.mul_def] using
        ((kernelTranslationHom f).map_mul x x⁻¹).symm
    exact congrArg (fun q : E.X ⟶ E.X => q.left) h

/-- Kernel points act by their literal deck translations. -/
def kernelDeckRepresentation : KernelPoints f →* Aut (cover f) where
  toFun := kernelDeckAut f
  map_one' := by
    apply Iso.ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun q : E.X ⟶ E.X => q.left) (kernelTranslationHom f).map_one
  map_mul' x y := by
    apply Iso.ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun q : E.X ⟶ E.X => q.left) ((kernelTranslationHom f).map_mul x y)

/-- Every original-field endomorphism of a proper curve fixes its actual
global units, because its global functions are the structural constants. -/
theorem curveUnits_pullback_eq_self (hE : Curve.Properties E.X) (g : E.X ⟶ E.X)
    (a : Γ(E.X.left, ⊤)ˣ) : Scheme.Modules.Invertible.UnitDescent.pullUnit g.left a = a := by
  apply Units.ext
  obtain ⟨b, hb⟩ :=
    (Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen E.X hE).surjective
      (a : Γ(E.X.left, ⊤))
  change g.left.appTop (a : Γ(E.X.left, ⊤)) = a
  rw [← hb, Curve.curveConstantsEquiv_apply, Cohomology.map_constants]

open Scheme.Modules.Invertible.EtaleDescent Scheme.Modules.Invertible.FrameTorsor

/-- Semilinear pullback of the actual global units is the structural
field map under the proved proper-curve constants equivalence. -/
theorem curveUnits_pullback_baseMap (hE : Curve.Properties E.X)
    (σ : k →+* k) (b : E.X.left ⟶ E.X.left)
    (hb : b ≫ E.X.hom = E.X.hom ≫ Spec.map (CommRingCat.ofHom σ))
    (z : Γ(E.X.left, ⊤)ˣ) :
    Units.map (Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen
        E.X hE).symm.toMonoidHom (Scheme.Modules.Invertible.UnitDescent.pullUnit b z) =
      Units.map σ.toMonoidHom (Units.map
        (Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen
          E.X hE).symm.toMonoidHom z) := by
  let c := Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen E.X hE
  apply Units.ext
  change c.symm (b.appTop (z : Γ(E.X.left, ⊤))) = σ (c.symm (z : Γ(E.X.left, ⊤)))
  apply c.injective
  rw [RingEquiv.apply_symm_apply]
  have h := Cohomology.map_constants_of_baseMap σ E.X E.X b hb
    (c.symm (z : Γ(E.X.left, ⊤)))
  change b.appTop (c (c.symm (z : Γ(E.X.left, ⊤)))) = c (σ (c.symm (z : Γ(E.X.left, ⊤)))) at h
  simpa only [RingEquiv.apply_symm_apply] using h

/-- An actual trivial pullback class supplies an O-linear frame on the
given etale cover. Only the already proved native descent supplier is used
to regard the frame as a section of its existing sheaf. -/
def frameOfPullbackClassZero (L : LineBundle D.X.left)
    (hL : pullbackClass f.hom.hom.left (classOf D.X.left L) = 0) :
    (frameSheaf etaleLineBundleDescent D.X.left L).obj.obj (op (cover f)) := by
  change classOf E.X.left (pullbackLineBundle f.hom.hom.left L) =
    classOf E.X.left (trivialLineBundle E.X.left) at hL
  let e := Classical.choice (Quotient.exact hL)
  refine (frameSectionsEquiv etaleLineBundleDescent D.X.left L (op (cover f))).symm ?_
  exact e ≪≫ coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit E.X.left.ringCatSheaf)

/-- Positive transport of a chosen actual frame along kernel translations,
as a character with values in actual global units. -/
def frameKernelCharacter (hE : Curve.Properties E.X) (L : LineBundle D.X.left)
    (s : (frameSheaf etaleLineBundleDescent D.X.left L).obj.obj (op (cover f))) :
    KernelPoints f →* Γ(E.X.left, ⊤)ˣ :=
  Transport.character (frameTorsor etaleLineBundleDescent D.X.left L) (cover f)
    (kernelDeckRepresentation f)
    (fun x a => curveUnits_pullback_eq_self hE (kernelTranslationHom f x) a) s

/-- Changing the O-linear trivialization does not change the kernel
character, by actual proper-curve constants. -/
theorem frameKernelCharacter_independent (hE : Curve.Properties E.X) (L : LineBundle D.X.left)
    (s t : (frameSheaf etaleLineBundleDescent D.X.left L).obj.obj (op (cover f))) :
    frameKernelCharacter f hE L s = frameKernelCharacter f hE L t := by
  apply MonoidHom.ext
  intro x
  exact Transport.scalar_independent (frameTorsor etaleLineBundleDescent D.X.left L) (cover f)
    (kernelDeckRepresentation f)
    (fun x a => curveUnits_pullback_eq_self hE (kernelTranslationHom f x) a) s t x

/-- The actual evaluation character for a line bundle whose pullback is
trivial, converted to base-field units by the structural constants map. -/
def lineBundleKernelCharacter (hE : Curve.Properties E.X) (L : LineBundle D.X.left)
    (hL : pullbackClass f.hom.hom.left (classOf D.X.left L) = 0) :
    KernelPoints f →* kˣ := by
  let c := Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen E.X hE
  exact (Units.map c.symm.toMonoidHom).comp
    (frameKernelCharacter f hE L (frameOfPullbackClassZero f L hL))

/-- An isomorphism of the original line bundles preserves their actual
kernel evaluation characters. -/
theorem lineBundleKernelCharacter_iso (hE : Curve.Properties E.X)
    (L M : LineBundle D.X.left) (e : L.val ≅ M.val)
    (hL : pullbackClass f.hom.hom.left (classOf D.X.left L) = 0)
    (hM : pullbackClass f.hom.hom.left (classOf D.X.left M) = 0) :
    lineBundleKernelCharacter f hE L hL = lineBundleKernelCharacter f hE M hM := by
  apply MonoidHom.ext
  intro x
  apply congrArg (Units.map
    (Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen E.X hE).symm.toMonoidHom)
  exact Transport.scalar_iso_independent
    (frameTorsor etaleLineBundleDescent D.X.left L) (cover f) (kernelDeckRepresentation f)
    (fun x a => curveUnits_pullback_eq_self hE (kernelTranslationHom f x) a)
    (AssociatedBundle.frameIsoOfBundleIso etaleLineBundleDescent e)
    (frameOfPullbackClassZero f L hL) (frameOfPullbackClassZero f M hM) x

/-- Tensor product of line bundles multiplies the actual evaluation
characters. The choices of all three frames are immaterial. -/
theorem lineBundleKernelCharacter_tensor (hE : Curve.Properties E.X)
    (L M : LineBundle D.X.left)
    (hL : pullbackClass f.hom.hom.left (classOf D.X.left L) = 0)
    (hM : pullbackClass f.hom.hom.left (classOf D.X.left M) = 0)
    (hLM : pullbackClass f.hom.hom.left (classOf D.X.left (tensorLineBundle D.X.left L M)) = 0) :
    lineBundleKernelCharacter f hE (tensorLineBundle D.X.left L M) hLM =
      lineBundleKernelCharacter f hE L hL * lineBundleKernelCharacter f hE M hM := by
  let s := frameOfPullbackClassZero f L hL
  let t := frameOfPullbackClassZero f M hM
  let r := FrameTensor.tensorSection etaleLineBundleDescent D.X.left L M (op (cover f)) s t
  have hi := frameKernelCharacter_independent f hE (tensorLineBundle D.X.left L M)
    (frameOfPullbackClassZero f (tensorLineBundle D.X.left L M) hLM) r
  apply MonoidHom.ext
  intro x
  let c := Units.map
    (Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen E.X hE).symm.toMonoidHom
  change c (frameKernelCharacter f hE (tensorLineBundle D.X.left L M)
      (frameOfPullbackClassZero f (tensorLineBundle D.X.left L M) hLM) x) =
    c (frameKernelCharacter f hE L s x) * c (frameKernelCharacter f hE M t x)
  rw [hi, ← map_mul]
  apply congrArg c
  exact Transport.scalar_tensor (cover f) (kernelDeckRepresentation f) L M s t x

omit [Etale f.hom.hom.left] in
/-- A commuting source square transports triviality of a pulled line
bundle class without choosing a new trivialization. -/
theorem pullbackKernelClass_zero (L : LineBundle D.X.left)
    (hL : pullbackClass f.hom.hom.left (classOf D.X.left L) = 0)
    (a : D.X.left ⟶ D.X.left) (b : E.X.left ⟶ E.X.left)
    (w : b ≫ f.hom.hom.left = f.hom.hom.left ≫ a) :
    pullbackClass f.hom.hom.left (classOf D.X.left (pullbackLineBundle a L)) = 0 := by
  change pullbackClass f.hom.hom.left (pullbackClass a (classOf D.X.left L)) = 0
  rw [← pullbackClass_comp, ← w, pullbackClass_comp, hL, pullbackClass_zero]

/-- Actual line-bundle evaluation follows a semilinear scheme square and
commuting kernel translations. All scalar maps are the structural ones. -/
theorem lineBundleKernelCharacter_semilinear (hE : Curve.Properties E.X)
    (L : LineBundle D.X.left)
    (hL : pullbackClass f.hom.hom.left (classOf D.X.left L) = 0)
    (a : D.X.left ⟶ D.X.left) (b : E.X.left ⟶ E.X.left)
    (w : b ≫ f.hom.hom.left = f.hom.hom.left ≫ a)
    (σ : k →+* k) (hb : b ≫ E.X.hom = E.X.hom ≫ Spec.map (CommRingCat.ofHom σ))
    (x y : KernelPoints f)
    (hxy : (kernelTranslationHom f y).left ≫ b = b ≫ (kernelTranslationHom f x).left) :
    lineBundleKernelCharacter f hE (pullbackLineBundle a L)
        (pullbackKernelClass_zero f L hL a b w) y =
      Units.map σ.toMonoidHom (lineBundleKernelCharacter f hE L hL x) := by
  let s := frameOfPullbackClassZero f L hL
  let t := FramePullback.sectionMap a L (cover f) (cover f) b w s
  have hi := congrArg (fun χ => χ y) (frameKernelCharacter_independent f hE
    (pullbackLineBundle a L)
    (frameOfPullbackClassZero f (pullbackLineBundle a L)
      (pullbackKernelClass_zero f L hL a b w)) t)
  have hn := FramePullback.evaluation_naturality a L (cover f) (cover f) b w
    (kernelDeckRepresentation f x) (kernelDeckRepresentation f y) hxy s
  have he : frameKernelCharacter f hE (pullbackLineBundle a L)
      (frameOfPullbackClassZero f (pullbackLineBundle a L)
        (pullbackKernelClass_zero f L hL a b w)) y =
    Scheme.Modules.Invertible.UnitDescent.pullUnit b (frameKernelCharacter f hE L s x) :=
    hi.trans hn
  exact (congrArg (Units.map
    (Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen
      E.X hE).symm.toMonoidHom) he).trans (curveUnits_pullback_baseMap hE σ b hb _)

omit [Etale f.hom.hom.left] in
/-- The source multiplication triangle kills the actual kernel points. -/
theorem kernelPoints_pow_eq_one (n : ℕ) (d : D ⟶ E)
    (hfd : f.hom.hom ≫ d.hom.hom = (𝟙 E.X) ^ n) (x : KernelPoints f) : x ^ n = 1 := by
  apply Kernel.DeckTranslation.inclusion_points_injective f (𝟙_ (FScheme k))
  change (x ^ n) ≫ (Kernel.inclusion f).hom.hom =
    (1 : KernelPoints f) ≫ (Kernel.inclusion f).hom.hom
  rw [MonObj.pow_comp, MonObj.one_comp]
  have hx : (x ≫ (Kernel.inclusion f).hom.hom) ≫ f.hom.hom = 1 := by
    rw [Category.assoc, (Kernel.square f).w]
    simp only [← Category.assoc, comp_toUnit, Hom.one_def]
  calc
    _ = (x ≫ (Kernel.inclusion f).hom.hom) ≫ ((𝟙 E.X) ^ n) := by
      rw [MonObj.comp_pow, Category.comp_id]
    _ = _ := by rw [← hfd, ← Category.assoc, hx, MonObj.one_comp]

/-- The evaluation character lands in the literal roots-of-unity group
when an actual source multiplication triangle is supplied. -/
def lineBundleKernelRootCharacter (hE : Curve.Properties E.X) (L : LineBundle D.X.left)
    (hL : pullbackClass f.hom.hom.left (classOf D.X.left L) = 0)
    (n : ℕ) (d : D ⟶ E) (hfd : f.hom.hom ≫ d.hom.hom = (𝟙 E.X) ^ n) :
    KernelPoints f →* rootsOfUnity n k :=
  (lineBundleKernelCharacter f hE L hL).codRestrict (rootsOfUnity n k) (fun x => by
    rw [mem_rootsOfUnity, ← map_pow, kernelPoints_pow_eq_one f n d hfd x, map_one])

end AlgebraicGeometry.Scheme.Group.IsogenyPairing

namespace AlgebraicGeometry.Scheme.Group.IsogenyPairing

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- Rational point sections of a finite group scheme cover its
product with any test scheme over an algebraically closed field. -/
theorem groupPointSections_cover [IsAlgClosed k] (A : Grp (FScheme k))
    [IsFinite A.X.hom] (X : FScheme k) (z : (A.X ⊗ X).left) :
    ∃ a : 𝟙_ (FScheme k) ⟶ A.X, ∃ x : X.left,
      (lift (toUnit X ≫ a) (𝟙 X)).left x = z := by
  let : IsLocallyArtinian A.X.left := .of_locallyQuasiFinite A.X.hom
  let q := (fst A.X X).left z
  have hq : IsClosed ({q} : Set A.X.left) := isClosed_discrete _
  let a : 𝟙_ (FScheme k) ⟶ A.X := Over.homMk
    (pointOfClosedPoint A.X.hom q hq) (pointOfClosedPoint_comp A.X.hom q hq)
  have ha : q ∈ Set.range a.left :=
    ⟨IsLocalRing.closedPoint k, pointOfClosedPoint_apply A.X.hom q hq _⟩
  have hz : z ∈ Set.range (a ▷ X).left := by
    rw [Over.whiskerRight_left]
    erw [Scheme.Pullback.range_map (Over.hom (𝟙_ (FScheme k))) X.hom
      A.X.hom X.hom a.left (𝟙 X.left) (𝟙 (Base k))]
    exact ⟨ha, ⟨(snd A.X X).left z, rfl⟩⟩
  obtain ⟨w, hw⟩ := hz
  have hj : (λ_ X).inv ≫ (a ▷ X) = lift (toUnit X ≫ a) (𝟙 X) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd,
        leftUnitor_inv_fst_assoc, leftUnitor_inv_snd, lift_fst, lift_snd]
  refine ⟨a, (λ_ X).hom.left w, ?_⟩
  rw [← hj, Over.comp_left, Scheme.Hom.comp_apply]
  have hu : (λ_ X).inv.left ((λ_ X).hom.left w) = w :=
    congrArg (fun m : 𝟙_ (FScheme k) ⊗ X ⟶ 𝟙_ (FScheme k) ⊗ X => m.left w)
      (λ_ X).hom_inv_id
  rw [hu]
  exact hw

variable {E D : Grp (FScheme k)} (f : E ⟶ D)

/-- The existing categorical kernel torsor identifies the actual kernel
pair with the product of the actual kernel group and the original source. -/
def kernelPairIso : ((Kernel.group f).X ⊗ E.X).left ≅
    pullback f.hom.hom.left f.hom.hom.left :=
  (((Kernel.marking f).toTorsorAction.action_isPullback).map (Over.forget (Base k))).isoPullback

theorem kernelPairIso_hom_fst :
    (kernelPairIso f).hom ≫ pullback.fst f.hom.hom.left f.hom.hom.left =
      ((fst (Kernel.group f).X E.X ≫ (Kernel.inclusion f).hom.hom) *
        snd (Kernel.group f).X E.X).left :=
  (((Kernel.marking f).toTorsorAction.action_isPullback).map
    (Over.forget (Base k))).isoPullback_hom_fst

theorem kernelPairIso_hom_snd :
    (kernelPairIso f).hom ≫ pullback.snd f.hom.hom.left f.hom.hom.left =
      (snd (Kernel.group f).X E.X).left :=
  (((Kernel.marking f).toTorsorAction.action_isPullback).map
    (Over.forget (Base k))).isoPullback_hom_snd

/-- The graph of a literal kernel translation in the actual kernel pair. -/
def translationPairMap (x : KernelPoints f) :
    E.X.left ⟶ pullback f.hom.hom.left f.hom.hom.left :=
  (lift (toUnit E.X ≫ x) (𝟙 E.X)).left ≫ (kernelPairIso f).hom

@[reassoc] theorem translationPairMap_fst (x : KernelPoints f) :
    translationPairMap f x ≫ pullback.fst f.hom.hom.left f.hom.hom.left =
      (kernelTranslationHom f x).left := by
  rw [translationPairMap, Category.assoc, kernelPairIso_hom_fst, ← Over.comp_left]
  apply congrArg (fun m : E.X ⟶ E.X => m.left)
  rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  rfl

@[reassoc] theorem translationPairMap_snd (x : KernelPoints f) :
    translationPairMap f x ≫ pullback.snd f.hom.hom.left f.hom.hom.left = 𝟙 E.X.left := by
  rw [translationPairMap, Category.assoc, kernelPairIso_hom_snd, ← Over.comp_left,
    lift_snd, Over.id_left]

/-- The actual kernel pair is covered by the graphs of rational kernel
translations over an algebraically closed field. -/
theorem translationPairMap_cover [IsAlgClosed k]
    [IsFinite f.hom.hom.left]
    (z : (pullback f.hom.hom.left f.hom.hom.left : Scheme.{u})) :
    ∃ a : KernelPoints f, ∃ x : E.X.left, translationPairMap f a x = z := by
  obtain ⟨a, x, hx⟩ := groupPointSections_cover (Kernel.group f) E.X ((kernelPairIso f).inv z)
  refine ⟨a, x, ?_⟩
  change (kernelPairIso f).hom ((lift (toUnit E.X ≫ a) (𝟙 E.X)).left x) = z
  rw [hx]
  exact congrArg (fun m : (pullback f.hom.hom.left f.hom.hom.left : Scheme.{u}) ⟶
    pullback f.hom.hom.left f.hom.hom.left => m z) (kernelPairIso f).inv_hom_id

variable [Etale f.hom.hom.left]

/-- The actual kernel pair, viewed in the small etale site of the target. -/
def kernelPairCover : D.X.left.Etale :=
  Scheme.Etale.mk (pullback.fst f.hom.hom.left f.hom.hom.left ≫ f.hom.hom.left)

/-- The first projection of the actual kernel pair in the etale site. -/
def kernelPairFirst : kernelPairCover f ⟶ cover f :=
  MorphismProperty.Over.homMk (pullback.fst f.hom.hom.left f.hom.hom.left)
    rfl (by trivial)

/-- The second projection of the actual kernel pair in the etale site. -/
def kernelPairSecond : kernelPairCover f ⟶ cover f :=
  MorphismProperty.Over.homMk (pullback.snd f.hom.hom.left f.hom.hom.left)
    (pullback.condition (f := f.hom.hom.left) (g := f.hom.hom.left)).symm (by trivial)

/-- The graph of a kernel translation as a morphism in the etale site. -/
def translationPair (x : KernelPoints f) : cover f ⟶ kernelPairCover f :=
  MorphismProperty.Over.homMk (translationPairMap f x) (by
    change translationPairMap f x ≫
      (pullback.fst f.hom.hom.left f.hom.hom.left ≫ f.hom.hom.left) = f.hom.hom.left
    rw [translationPairMap_fst_assoc]
    exact congrArg Over.Hom.left (kernelTranslation_over f x)) (by trivial)

@[simp] theorem translationPair_first (x : KernelPoints f) :
    translationPair f x ≫ kernelPairFirst f = (kernelDeckRepresentation f x).hom := by
  apply MorphismProperty.Over.Hom.ext
  exact translationPairMap_fst f x

@[simp] theorem translationPair_second (x : KernelPoints f) :
    translationPair f x ≫ kernelPairSecond f = 𝟙 (cover f) := by
  apply MorphismProperty.Over.Hom.ext
  exact translationPairMap_snd f x

/-- The literal translation graphs form a covering sieve of the kernel pair. -/
theorem translationPair_cover [IsAlgClosed k] [IsFinite f.hom.hom.left] :
    Sieve.ofArrows (fun _ : KernelPoints f => cover f) (translationPair f) ∈
      Scheme.smallEtaleTopology D.X.left (kernelPairCover f) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  ext z
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact translationPairMap_cover f z

/-- For an actual etale sheaf, invariance under every rational kernel
translation is the matching condition on the entire scheme kernel pair. -/
theorem deckInvariant_equalizer [IsAlgClosed k] [IsFinite f.hom.hom.left]
    (F : SetSheaf D.X.left) (s : F.obj.obj (op (cover f)))
    (hs : ∀ x : KernelPoints f, F.obj.map (kernelDeckRepresentation f x).hom.op s = s) :
    F.obj.map (kernelPairFirst f).op s = F.obj.map (kernelPairSecond f).op s := by
  have hloc (x : KernelPoints f) :
      F.obj.map (translationPair f x).op (F.obj.map (kernelPairFirst f).op s) =
        F.obj.map (translationPair f x).op (F.obj.map (kernelPairSecond f).op s) := by
    change (F.obj.map (kernelPairFirst f).op ≫ F.obj.map (translationPair f x).op) s =
      (F.obj.map (kernelPairSecond f).op ≫ F.obj.map (translationPair f x).op) s
    rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp,
      translationPair_first, translationPair_second, op_id, F.obj.map_id]
    exact hs x
  apply (F.property.isSheafFor _ (translationPair_cover f)).isSeparatedFor.ext
  intro V a ha
  obtain ⟨x, b, rfl⟩ := Sieve.ofArrows.exists ha
  simp only [op_comp, F.obj.map_comp]
  exact congrArg (F.obj.map b.op) (hloc x)

/-- The original isogeny as a cover of the terminal object of the etale site. -/
def coverToTerminal : cover f ⟶ etaleTerminal D.X.left :=
  MorphismProperty.Over.homMk f.hom.hom.left (Category.comp_id _) (by trivial)

/-- Deck-invariant sections descend along the original finite etale
surjection. The proof uses the actual kernel pair and the sheaf axiom. -/
theorem deckInvariant_descends [IsAlgClosed k] [IsFinite f.hom.hom.left]
    [Surjective f.hom.hom.left] (F : SetSheaf D.X.left)
    (s : F.obj.obj (op (cover f)))
    (hs : ∀ x : KernelPoints f, F.obj.map (kernelDeckRepresentation f x).hom.op s = s) :
    ∃! t : F.obj.obj (op (etaleTerminal D.X.left)), F.obj.map (coverToTerminal f).op t = s := by
  have hcover : Sieve.ofArrows (fun _ : PUnit.{1} => cover f) (fun _ => coverToTerminal f) ∈
      Scheme.smallEtaleTopology D.X.left (etaleTerminal D.X.left) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := f.hom.hom.left.surjective z
    exact ⟨PUnit.unit, x, hx⟩
  have hf : Presieve.IsSheafFor F.obj (Presieve.singleton (coverToTerminal f)) := by
    apply (Presieve.isSheafFor_iff_generate _).mpr
    apply F.property.isSheafFor
    simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hcover
  apply (Presieve.isSheafFor_singleton.mp hf) s
  intro V a b hab
  have hw : a.left ≫ f.hom.hom.left = b.left ≫ f.hom.hom.left :=
    congrArg (fun q : V ⟶ etaleTerminal D.X.left => q.left) hab
  let l : V ⟶ kernelPairCover f := MorphismProperty.Over.homMk
    (pullback.lift a.left b.left hw) (by
      change pullback.lift a.left b.left hw ≫
        (pullback.fst f.hom.hom.left f.hom.hom.left ≫ f.hom.hom.left) = V.hom
      rw [pullback.lift_fst_assoc]
      exact MorphismProperty.Over.w a) (by trivial)
  have hfst : l ≫ kernelPairFirst f = a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  have hsnd : l ≫ kernelPairSecond f = b := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  have h := congrArg (F.obj.map l.op) (deckInvariant_equalizer f F s hs)
  change (F.obj.map (kernelPairFirst f).op ≫ F.obj.map l.op) s =
    (F.obj.map (kernelPairSecond f).op ≫ F.obj.map l.op) s at h
  rwa [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp, hfst, hsnd] at h

open Scheme.Modules.Invertible.EtaleDescent Scheme.Modules.Invertible.FrameTorsor
open Scheme.Modules.Invertible.AssociatedBundle

/-- A trivial evaluation character forces the original line-bundle class
to be zero: its chosen frame is deck-invariant and therefore descends. -/
theorem class_eq_zero_of_kernelCharacter_eq_one [IsAlgClosed k]
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left]
    (hE : Curve.Properties E.X) (L : LineBundle D.X.left)
    (hL : pullbackClass f.hom.hom.left (classOf D.X.left L) = 0)
    (hχ : lineBundleKernelCharacter f hE L hL = 1) : classOf D.X.left L = 0 := by
  let P := frameTorsor etaleLineBundleDescent D.X.left L
  let s := frameOfPullbackClassZero f L hL
  have hs (x : KernelPoints f) : P.carrier.obj.map (kernelDeckRepresentation f x).hom.op s = s := by
    let c := Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen E.X hE
    have hc := congrArg (fun χ => χ x) hχ
    have ht : transportUnit P (op (cover f)) s
        (P.carrier.obj.map (kernelDeckRepresentation f x).hom.op s) = 1 := by
      change Units.map c.symm.toMonoidHom
        (transportUnit P (op (cover f)) s
          (P.carrier.obj.map (kernelDeckRepresentation f x).hom.op s)) = 1 at hc
      apply Units.map_injective (f := c.symm.toMonoidHom) c.symm.injective
      simpa only [map_one] using hc
    have hzero : transport P (op (cover f)) s
        (P.carrier.obj.map (kernelDeckRepresentation f x).hom.op s) = 0 := by
      apply (unitsSections D.X.left (op (cover f))).injective
      exact (congrArg Additive.ofMul ht).trans (map_zero _).symm
    have ha := action_transport P (op (cover f)) s
      (P.carrier.obj.map (kernelDeckRepresentation f x).hom.op s)
    rw [hzero, P.zero_action] at ha
    exact ha.symm
  obtain ⟨t, _, _⟩ := deckInvariant_descends f P.carrier s hs
  let e := ((Scheme.Modules.pullbackId D.X.left).app L.val).symm ≪≫
    frameSectionsEquiv etaleLineBundleDescent D.X.left L (op (etaleTerminal D.X.left)) t ≪≫
    (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
      SheafOfModules.unit D.X.left.ringCatSheaf)).symm
  exact Quotient.sound ⟨e⟩

end AlgebraicGeometry.Scheme.Group.IsogenyPairing

namespace AlgebraicGeometry.Scheme.Group.IsogenyPairing

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The point of the original source represented by an actual kernel point. -/
def kernelPoint {E D : Grp (FScheme k)} (f : E ⟶ D) (x : KernelPoints f) :
    𝟙_ (FScheme k) ⟶ E.X := x ≫ (Kernel.inclusion f).hom.hom

theorem kernelPoint_over {E D : Grp (FScheme k)} (f : E ⟶ D) (x : KernelPoints f) :
    kernelPoint f x ≫ f.hom.hom = 1 := by
  rw [kernelPoint, Category.assoc, (Kernel.square f).w]
  simp only [← Category.assoc, comp_toUnit, Hom.one_def]

theorem unitorCurvePullback {E D : Grp (FScheme k)} (f : E ⟶ D)
    (a : PicardGroup (D.X ⊗ 𝟙_ (FScheme k)).left) :
    pullbackClass (ρ_ E.X).inv.left (pullbackClass (f.hom.hom ▷ (𝟙_ (FScheme k))).left a) =
      pullbackClass f.hom.hom.left (pullbackClass (ρ_ D.X).inv.left a) := by
  have hu : (ρ_ E.X).inv ≫ (f.hom.hom ▷ (𝟙_ (FScheme k))) =
      f.hom.hom ≫ (ρ_ D.X).inv := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd,
        rightUnitor_inv_fst_assoc, rightUnitor_inv_fst, rightUnitor_inv_snd,
        Category.comp_id, comp_toUnit]
  calc
    _ = pullbackClass ((ρ_ E.X).inv ≫ (f.hom.hom ▷ (𝟙_ (FScheme k)))).left a := by
      rw [Over.comp_left, pullbackClass_comp]
    _ = pullbackClass (f.hom.hom ≫ (ρ_ D.X).inv).left a :=
      congrArg (fun q : E.X ⟶ D.X ⊗ 𝟙_ (FScheme k) => pullbackClass q.left a) hu
    _ = _ := by rw [Over.comp_left, pullbackClass_comp]

variable (G : Grp (FScheme k))
variable [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom]

/-- The original positive point-minus-origin Picard class, realized by
the normalized diagonal class on the original curve. -/
def pointDivisorClass (x : 𝟙_ (FScheme k) ⟶ G.X) : PicardGroup G.X.left :=
  DualIsogeny.poincareClass G G.X (𝟙 G.X) (toUnit G.X ≫ x)

theorem pointDivisorClass_one : pointDivisorClass G 1 = 0 := by
  rw [pointDivisorClass, MonObj.comp_one, DualIsogeny.poincareClass_one_right]

theorem pointDivisorClass_mul [IsAlgClosed k] (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (x y : 𝟙_ (FScheme k) ⟶ G.X) :
    pointDivisorClass G (x * y) = pointDivisorClass G x + pointDivisorClass G y := by
  dsimp only [pointDivisorClass]
  rw [MonObj.comp_mul, DualIsogeny.poincareClass_mul_right G hG hg]

/-- The actual ideal line bundle of a rational section of the original curve. -/
def pointIdealLineBundle (x : 𝟙_ (FScheme k) ⟶ G.X) : LineBundle G.X.left :=
  ⟨idealModule x.left,
    sectionIdeal_isLocallyRankOne smoothRelativeDivisorIdeal G.X.hom x.left (Over.w x)⟩

/-- The original graph ideal becomes the actual point ideal under the
canonical unitor, through the canonical ideal-pullback morphism. -/
theorem pointGraph_unitor (x : 𝟙_ (FScheme k) ⟶ G.X) :
    pullbackClass (ρ_ G.X).inv.left
      (classOf _ (graphIdealLineBundle smoothRelativeDivisorIdeal G.X.hom
        (𝟙 (Base k)) x.left (Over.w x))) =
      classOf G.X.left (pointIdealLineBundle G x) := by
  have h : (𝟙 (Base k)) ≫ graph G.X.hom (𝟙 (Base k)) x.left (Over.w x) =
      x.left ≫ (ρ_ G.X).inv.left := by
    apply pullback.hom_ext
    · simp only [Category.id_comp, graph_fst, Category.assoc,
        Over.rightUnitor_inv_left_fst, Category.comp_id]
    · simp only [Category.id_comp, graph_snd, Category.assoc,
        Over.rightUnitor_inv_left_snd, Over.w, Over.tensorUnit_hom]
  let : IsIso (ρ_ G.X).inv.left := (Over.forget (Base k)).map_isIso (ρ_ G.X).inv
  let : IsIso (𝟙 (Base k)) := (Iso.refl (Base k)).isIso_hom
  let := idealPullbackMap_isIso_of_iso_square
    (graph G.X.hom (𝟙 (Base k)) x.left (Over.w x)) x.left
    (ρ_ G.X).inv.left (𝟙 (Base k)) h
  exact Quotient.sound ⟨asIso (idealPullbackMap
    (graph G.X.hom (𝟙 (Base k)) x.left (Over.w x)) x.left
    (ρ_ G.X).inv.left (𝟙 (Base k)) h)⟩

/-- The normalized positive point class is literally O(x) tensor O(-0).
The normalization over the ground field vanishes by its trivial Picard group. -/
theorem pointDivisorClass_eq_ideal (hG : Curve.Properties G.X)
    (x : 𝟙_ (FScheme k) ⟶ G.X) :
    pointDivisorClass G x = -classOf G.X.left (pointIdealLineBundle G x) +
      classOf G.X.left (pointIdealLineBundle G η[G.X]) := by
  have hc : (PointDivisor.degreeZeroPointClass G hG (𝟙_ (FScheme k)) x).val.val =
      abelClass smoothRelativeDivisorIdeal G.X.hom η[G.X].left (Over.w _)
        (𝟙 (Base k)) x.left (Over.w x) := by
    change (Scheme.RelativePicard.Classes.normalizeHom moduleTensorPullback G.X.hom
      η[G.X].left (Over.w _) (𝟙_ (FScheme k)) _).val = _
    rw [Scheme.RelativePicard.Classes.normalizeHom_val]
    have hz : pullbackClass
        (Scheme.RelativePicard.Classes.originSection G.X.hom η[G.X].left
          (Over.w _) (𝟙_ (FScheme k)))
        (abelClass smoothRelativeDivisorIdeal G.X.hom η[G.X].left (Over.w _)
          (𝟙 (Base k)) x.left (Over.w x)) = 0 := fieldPicard_eq_zero k _
    erw [hz, pullbackClass_zero, sub_zero]
    rfl
  rw [pointDivisorClass, ← DualIsogeny.pointClass_unitor G hG x, hc, abelClass_eq,
    pullbackClass_add moduleTensorPullback, pullbackClass_neg moduleTensorPullback]
  erw [pointGraph_unitor G x]
  have ho : originIdealLineBundle smoothRelativeDivisorIdeal G.X.hom η[G.X].left
      (Over.w _) (𝟙 (Base k)) =
      graphIdealLineBundle smoothRelativeDivisorIdeal G.X.hom (𝟙 (Base k))
        η[G.X].left (Over.w _) := by
    simp only [originIdealLineBundle, Category.id_comp]
  erw [ho, pointGraph_unitor G η[G.X]]

/-- Semilinear scheme isomorphisms pull back the actual point-minus-origin
class according to the literal two point squares. -/
theorem pointDivisorClass_semilinear (hG : Curve.Properties G.X)
    (a : G.X.left ≅ G.X.left) (c : Base k ≅ Base k)
    (ho : c.hom ≫ η[G.X].left = η[G.X].left ≫ a.hom)
    (x y : 𝟙_ (FScheme k) ⟶ G.X)
    (hxy : c.hom ≫ x.left = y.left ≫ a.hom) :
    pullbackClass a.hom (pointDivisorClass G x) = pointDivisorClass G y := by
  have hp (x y : 𝟙_ (FScheme k) ⟶ G.X)
      (hxy : c.hom ≫ x.left = y.left ≫ a.hom) :
      pullbackClass a.hom (classOf G.X.left (pointIdealLineBundle G x)) =
        classOf G.X.left (pointIdealLineBundle G y) := by
    let := idealPullbackMap_isIso_of_iso_square x.left y.left a.hom c.hom hxy
    exact Quotient.sound ⟨asIso (idealPullbackMap x.left y.left a.hom c.hom hxy)⟩
  rw [pointDivisorClass_eq_ideal G hG, pointDivisorClass_eq_ideal G hG,
    pullbackClass_add moduleTensorPullback, pullbackClass_neg moduleTensorPullback,
    hp x y hxy, hp η[G.X] η[G.X] ho]

/-- The actual positive point-minus-origin class detects rational points.
This is the native reduced-test Abel injectivity transported by the unitor. -/
theorem pointDivisorClass_injective (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) : Function.Injective (pointDivisorClass G) := by
  let : IsReduced (𝟙_ (FScheme k)).left := by
    change IsReduced (Spec (.of k))
    infer_instance
  have hi : Function.Injective (pullbackClass (ρ_ G.X).inv.left) := by
    intro a b h
    have h' := congrArg (pullbackClass (ρ_ G.X).hom.left) h
    simpa only [← pullbackClass_comp, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, pullbackClass_id] using h'
  intro x y h
  apply PointDivisor.pointClass_injective_of_isReduced smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback
    Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree relativeCartierIdealBaseChange
    smoothRelativeDivisorIdeal Curve.Picard.NormDegree.finiteMorphismNormOrder
    Cohomology.properStructureCohomologyBaseChange Curve.lineBundleRiemannRoch
    Curve.lineBundleHighDegreeVanishing Cohomology.noetherianSheafCohomologyVanishing
    G.X hG η[G.X] hg (𝟙_ (FScheme k))
  apply Subtype.ext
  apply Subtype.ext
  apply hi
  simpa only [DualIsogeny.pointClass_unitor, pointDivisorClass] using h

end AlgebraicGeometry.Scheme.Group.IsogenyPairing

namespace AlgebraicGeometry.Scheme.Group.IsogenyPairing

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] [IsAlgClosed k] {E D : Grp (FScheme k)}
variable [SmoothOfRelativeDimension 1 E.X.hom] [IsSeparated E.X.hom]
variable [SmoothOfRelativeDimension 1 D.X.hom] [IsSeparated D.X.hom]
variable (f : E ⟶ D) (hE : Curve.Properties E.X) (hD : Curve.Properties D.X)
variable [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left]
variable (n : ℕ) (hn : HasGeometricDegree f.hom.hom n)
variable (hgE : Curve.coherentGenus k E.X = 1)
variable (d : D ⟶ E) (hfd : f.hom.hom ≫ d.hom.hom = (𝟙 E.X) ^ n)

include hE hD hn hgE hfd in
/-- The actual Picard class of a point in the given reverse kernel becomes
trivial under the original isogeny pullback. The Picard-dual comparison,
not the multiplication triangle by itself, supplies this conclusion. -/
theorem pullback_kernelPointClass_zero (y : KernelPoints d) :
    pullbackClass f.hom.hom.left (pointDivisorClass D (kernelPoint d y)) = 0 := by
  have h := DualIsogeny.reverse_pointClass f hE hD n hn hgE d hfd
    (𝟙_ (FScheme k)) (kernelPoint d y)
  have hv := congrArg (fun a => pullbackClass (ρ_ E.X).inv.left a.val.val) h
  change pullbackClass (ρ_ E.X).inv.left
      (PointDivisor.degreeZeroPointClass E hE (𝟙_ (FScheme k))
        (kernelPoint d y ≫ d.hom.hom)).val.val =
    pullbackClass (ρ_ E.X).inv.left
      (pullbackClass (f.hom.hom ▷ (𝟙_ (FScheme k))).left
        (PointDivisor.degreeZeroPointClass D hD (𝟙_ (FScheme k)) (kernelPoint d y)).val.val) at hv
  rw [DualIsogeny.pointClass_unitor, kernelPoint_over, MonObj.comp_one,
    DualIsogeny.poincareClass_one_right, unitorCurvePullback,
    DualIsogeny.pointClass_unitor] at hv
  exact hv.symm

/-- An actual line-bundle representative of the original reverse-kernel
point class. Its eventual evaluation is independent of this choice. -/
def kernelPointLineBundle (y : KernelPoints d) : LineBundle D.X.left :=
  Quotient.out (pointDivisorClass D (kernelPoint d y))

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 E.X.hom] [IsSeparated E.X.hom] in
@[simp] theorem kernelPointLineBundle_class (y : KernelPoints d) :
    classOf D.X.left (kernelPointLineBundle d y) = pointDivisorClass D (kernelPoint d y) :=
  Quotient.out_eq _

include hE hD hn hgE hfd in
theorem kernelPointLineBundle_pullback_zero (y : KernelPoints d) :
    pullbackClass f.hom.hom.left (classOf D.X.left (kernelPointLineBundle d y)) = 0 := by
  rw [kernelPointLineBundle_class]
  exact pullback_kernelPointClass_zero f hE hD n hn hgE d hfd y

/-- The actual roots-of-unity evaluation character of a given reverse-kernel
point, constructed from its point/divisor class and kernel translations. -/
def evaluationCharacter (y : KernelPoints d) : KernelPoints f →* rootsOfUnity n k :=
  lineBundleKernelRootCharacter f hE (kernelPointLineBundle d y)
    (kernelPointLineBundle_pullback_zero f hE hD n hn hgE d hfd y) n d hfd

/-- The chosen representatives of reverse-kernel classes multiply by
tensor product at the level of actual evaluation characters. -/
theorem evaluationCharacter_mul (hgD : Curve.coherentGenus k D.X = 1)
    (y z : KernelPoints d) :
    evaluationCharacter f hE hD n hn hgE d hfd (y * z) =
      evaluationCharacter f hE hD n hn hgE d hfd y *
        evaluationCharacter f hE hD n hn hgE d hfd z := by
  let L := kernelPointLineBundle d y
  let M := kernelPointLineBundle d z
  let Q := kernelPointLineBundle d (y * z)
  have hL := kernelPointLineBundle_pullback_zero f hE hD n hn hgE d hfd y
  have hM := kernelPointLineBundle_pullback_zero f hE hD n hn hgE d hfd z
  have hQ := kernelPointLineBundle_pullback_zero f hE hD n hn hgE d hfd (y * z)
  have hLM : pullbackClass f.hom.hom.left
      (classOf D.X.left (tensorLineBundle D.X.left L M)) = 0 := by
    rw [classOf_tensor, pullbackClass_add moduleTensorPullback, hL, hM, add_zero]
  have hc : classOf D.X.left Q = classOf D.X.left (tensorLineBundle D.X.left L M) := by
    dsimp only [Q, L, M]
    simp only [classOf_tensor, kernelPointLineBundle_class, kernelPoint,
      MonObj.mul_comp, pointDivisorClass_mul D hD hgD]
  obtain ⟨e⟩ := Quotient.exact hc
  have he := (lineBundleKernelCharacter_iso f hE Q (tensorLineBundle D.X.left L M) e hQ hLM).trans
    (lineBundleKernelCharacter_tensor f hE L M hL hM hLM)
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change lineBundleKernelCharacter f hE Q hQ x =
    lineBundleKernelCharacter f hE L hL x * lineBundleKernelCharacter f hE M hM x
  exact congrArg (fun c => c x) he

/-- The actual evaluation is a homomorphism in the reverse-kernel point. -/
def evaluationHom (hgD : Curve.coherentGenus k D.X = 1) :
    KernelPoints d →* (KernelPoints f →* rootsOfUnity n k) where
  toFun := evaluationCharacter f hE hD n hn hgE d hfd
  map_one' := by
    have h := evaluationCharacter_mul f hE hD n hn hgE d hfd hgD 1 1
    rw [_root_.one_mul] at h
    apply mul_left_cancel (a := evaluationCharacter f hE hD n hn hgE d hfd 1)
    simpa only [_root_.mul_one] using h.symm
  map_mul' := evaluationCharacter_mul f hE hD n hn hgE d hfd hgD

/-- The constructed biadditive evaluation on the actual two kernel point
groups, with values in the literal roots of unity. Perfectness and Galois
equivariance are separate statements. -/
def kernelPairing (hgD : Curve.coherentGenus k D.X = 1) :
    Additive (KernelPoints d) →+
      (Additive (KernelPoints f) →+ Additive (rootsOfUnity n k)) where
  toFun y := (evaluationHom f hE hD n hn hgE d hfd hgD y.toMul).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (congrArg (fun c => c x.toMul)
      (evaluationHom f hE hD n hn hgE d hfd hgD).map_one)
  map_add' y z := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (congrArg (fun c => c x.toMul)
      ((evaluationHom f hE hD n hn hgE d hfd hgD).map_mul y.toMul z.toMul))

/-- Trivial evaluation detects the identity of the actual reverse kernel.
No invertibility assumption on the degree is needed for this direction. -/
theorem evaluationCharacter_eq_one (hgD : Curve.coherentGenus k D.X = 1)
    (y : KernelPoints d) (hy : evaluationCharacter f hE hD n hn hgE d hfd y = 1) : y = 1 := by
  have hχ : lineBundleKernelCharacter f hE (kernelPointLineBundle d y)
      (kernelPointLineBundle_pullback_zero f hE hD n hn hgE d hfd y) = 1 := by
    apply MonoidHom.ext
    intro x
    exact congrArg (fun χ => (χ x).val) hy
  have hc := class_eq_zero_of_kernelCharacter_eq_one f hE (kernelPointLineBundle d y)
    (kernelPointLineBundle_pullback_zero f hE hD n hn hgE d hfd y) hχ
  rw [kernelPointLineBundle_class] at hc
  have hp : kernelPoint d y = 1 := pointDivisorClass_injective D hD hgD
    (hc.trans (pointDivisorClass_one D).symm)
  apply Kernel.DeckTranslation.inclusion_points_injective d (𝟙_ (FScheme k))
  simpa only [kernelPoint, MonObj.one_comp] using hp

/-- The constructed reverse-kernel character map is injective by actual
frame descent and Abel injectivity. -/
theorem evaluationHom_injective (hgD : Curve.coherentGenus k D.X = 1) :
    Function.Injective (evaluationHom f hE hD n hn hgE d hfd hgD) := by
  apply (injective_iff_map_eq_one _).mpr
  exact evaluationCharacter_eq_one f hE hD n hn hgE d hfd hgD

/-- The actual biadditive kernel pairing is nondegenerate in its
reverse-kernel variable, without a prime-to-characteristic restriction. -/
theorem kernelPairing_injective (hgD : Curve.coherentGenus k D.X = 1) :
    Function.Injective (kernelPairing f hE hD n hn hgE d hfd hgD) := by
  intro y z h
  change y.toMul = z.toMul
  apply evaluationHom_injective f hE hD n hn hgE d hfd hgD
  apply MonoidHom.ext
  intro x
  exact congrArg Additive.toMul (congrArg (fun χ => χ (Additive.ofMul x)) h)

include hn in
omit [SmoothOfRelativeDimension 1 E.X.hom] [IsSeparated E.X.hom]
  [SmoothOfRelativeDimension 1 D.X.hom] [IsSeparated D.X.hom]
  [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left] in
/-- The original kernel-point cardinality is its given geometric degree. -/
theorem kernelPoints_card : Nat.card (KernelPoints f) = n :=
  (Nat.card_congr (Kernel.pointsEquiv f (𝟙_ (FScheme k)))).trans (hn k (𝟙 (Base k)) 1)

include hE hn hgE hfd in
omit [SmoothOfRelativeDimension 1 E.X.hom] [IsSeparated E.X.hom]
  [SmoothOfRelativeDimension 1 D.X.hom] [IsSeparated D.X.hom]
  [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left] in
/-- The reverse kernel has the expected cardinality at invertible levels.
This is proved by decomposing the actual multiplication fibre into the
actual fibres of the original isogeny. -/
theorem reverseKernelPoints_card (hu : IsUnit (n : k)) : Nat.card (KernelPoints d) = n := by
  have hn0 : n ≠ 0 := by
    intro h
    apply hu.ne_zero
    simp only [h, Nat.cast_zero]
  let A := {x : 𝟙_ (FScheme k) ⟶ E.X // x ≫ (𝟙 E.X) ^ n = 1}
  let B := {y : 𝟙_ (FScheme k) ⟶ D.X // y ≫ d.hom.hom = 1}
  let C (y : B) := {x : 𝟙_ (FScheme k) ⟶ E.X // x ≫ f.hom.hom = y.val}
  let e : A ≃ Sigma C := {
    toFun x := ⟨⟨x.val ≫ f.hom.hom, by
      rw [Category.assoc, hfd]
      exact x.property⟩, ⟨x.val, rfl⟩⟩
    invFun z := ⟨z.2.val, by
      rw [← hfd, ← Category.assoc, z.2.property]
      exact z.1.property⟩
    left_inv x := by rfl
    right_inv z := by
      rcases z with ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
      dsimp only [C] at hx
      cases hx
      rfl }
  have hA : Nat.card A = n * n :=
    Multiplication.multiplication_hasGeometricDegree_of_isAlgClosed E hE hgE n hu k (𝟙 (Base k)) 1
  have hC (y : B) : Nat.card (C y) = n := hn k (𝟙 (Base k)) y.val
  let : Finite A := Nat.finite_of_card_ne_zero (hA.trans_ne (mul_ne_zero hn0 hn0))
  let : Finite (Sigma C) := Finite.of_equiv A e
  let (y : B) : Finite (C y) := Nat.finite_of_card_ne_zero ((hC y).trans_ne hn0)
  have hs : Function.Surjective (Sigma.fst : Sigma C → B) := by
    intro y
    obtain ⟨x⟩ := (Nat.card_ne_zero.mp ((hC y).trans_ne hn0)).1
    exact ⟨⟨y, x⟩, rfl⟩
  let : Finite B := Finite.of_surjective Sigma.fst hs
  let : Fintype B := Fintype.ofFinite B
  have hc : n * n = Nat.card B * n := by
    rw [← hA, Nat.card_congr e, Nat.card_sigma]
    simp [hC, Nat.card_eq_fintype_card]
  have hB : Nat.card B = n := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn0) hc.symm
  exact (Nat.card_congr (Kernel.pointsEquiv d (𝟙_ (FScheme k)))).trans hB

include hE hn hgE hfd in
omit [SmoothOfRelativeDimension 1 D.X.hom] [IsSeparated D.X.hom]
  [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left] in
/-- The full group of literal roots-of-unity characters has the geometric
kernel cardinality. Finite abelian duality is applied only after the
actual exponent bound and enough roots have been supplied. -/
theorem kernelRootCharacters_card (hu : IsUnit (n : k)) :
    Nat.card (KernelPoints f →* rootsOfUnity n k) = n := by
  have hn0 : n ≠ 0 := by
    intro h
    apply hu.ne_zero
    simp only [h, Nat.cast_zero]
  let : Finite (KernelPoints f) := Nat.finite_of_card_ne_zero
    ((kernelPoints_card f n hn).trans_ne hn0)
  let : CommGroup (KernelPoints f) := {
    toGroup := inferInstance
    mul_comm a b := by
      apply Kernel.DeckTranslation.inclusion_points_injective f (𝟙_ (FScheme k))
      change (a * b) ≫ (Kernel.inclusion f).hom.hom =
        (b * a) ≫ (Kernel.inclusion f).hom.hom
      rw [MonObj.mul_comp, MonObj.mul_comp]
      apply pointDivisorClass_injective E hE hgE
      rw [pointDivisorClass_mul E hE hgE, pointDivisorClass_mul E hE hgE, add_comm] }
  let : NeZero n := ⟨hn0⟩
  let : NeZero (n : k) := ⟨hu.ne_zero⟩
  let : HasEnoughRootsOfUnity k (Monoid.exponent (KernelPoints f)) :=
    HasEnoughRootsOfUnity.of_dvd k
      (Monoid.exponent_dvd_of_forall_pow_eq_one (kernelPoints_pow_eq_one f n d hfd))
  let e : (KernelPoints f →* rootsOfUnity n k) ≃ (KernelPoints f →* kˣ) := {
    toFun χ := (rootsOfUnity n k).subtype.comp χ
    invFun χ := χ.codRestrict (rootsOfUnity n k) (fun x => by
      rw [mem_rootsOfUnity, ← map_pow, kernelPoints_pow_eq_one f n d hfd x, map_one])
    left_inv χ := by ext x; rfl
    right_inv χ := by ext x; rfl }
  exact (Nat.card_congr e).trans
    ((CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (KernelPoints f) k).trans
      (kernelPoints_card f n hn))

/-- At levels invertible in the field, the actual evaluation character map
is bijective. Injectivity is the descended-frame theorem; surjectivity
then follows from the two proved cardinality formulas. -/
theorem evaluationHom_bijective (hgD : Curve.coherentGenus k D.X = 1)
    (hu : IsUnit (n : k)) :
    Function.Bijective (evaluationHom f hE hD n hn hgE d hfd hgD) := by
  have hn0 : n ≠ 0 := by
    intro h
    apply hu.ne_zero
    simp only [h, Nat.cast_zero]
  let : Finite (KernelPoints f →* rootsOfUnity n k) := Nat.finite_of_card_ne_zero
    ((kernelRootCharacters_card f hE n hn hgE d hfd hu).trans_ne hn0)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨evaluationHom_injective f hE hD n hn hgE d hfd hgD, ?_⟩
  exact (reverseKernelPoints_card f hE n hn hgE d hfd hu).trans
    (kernelRootCharacters_card f hE n hn hgE d hfd hu).symm

/-- Perfectness of the constructed biadditive pairing at levels invertible
in the field, on the actual categorical-kernel rational point groups. -/
theorem kernelPairing_bijective (hgD : Curve.coherentGenus k D.X = 1)
    (hu : IsUnit (n : k)) :
    Function.Bijective (kernelPairing f hE hD n hn hgE d hfd hgD) :=
  MonoidHom.toAdditive.bijective.comp
    ((evaluationHom_bijective f hE hD n hn hgE d hfd hgD hu).comp Additive.toMul.bijective)

/-- The constructed kernel evaluation follows a literal semilinear
isomorphism square. The point and translation hypotheses are actual
scheme equalities, ready for the canonical Galois base-change maps. -/
theorem evaluationCharacter_semilinear (a : D.X.left ≅ D.X.left)
    (b : E.X.left ≅ E.X.left) (c : Base k ≅ Base k) (σ : k →+* k)
    (w : b.hom ≫ f.hom.hom.left = f.hom.hom.left ≫ a.hom)
    (hb : b.hom ≫ E.X.hom = E.X.hom ≫ Spec.map (CommRingCat.ofHom σ))
    (ho : c.hom ≫ η[D.X].left = η[D.X].left ≫ a.hom)
    (y y' : KernelPoints d)
    (hy : c.hom ≫ (kernelPoint d y).left = (kernelPoint d y').left ≫ a.hom)
    (x x' : KernelPoints f)
    (hx : (kernelTranslationHom f x').left ≫ b.hom =
      b.hom ≫ (kernelTranslationHom f x).left) :
    (evaluationCharacter f hE hD n hn hgE d hfd y' x' : kˣ) =
      Units.map σ.toMonoidHom (evaluationCharacter f hE hD n hn hgE d hfd y x : kˣ) := by
  let L := kernelPointLineBundle d y
  let L' := kernelPointLineBundle d y'
  have hL := kernelPointLineBundle_pullback_zero f hE hD n hn hgE d hfd y
  have hL' := kernelPointLineBundle_pullback_zero f hE hD n hn hgE d hfd y'
  have hM := pullbackKernelClass_zero f L hL a.hom b.hom w
  have he : classOf D.X.left L' = classOf D.X.left (pullbackLineBundle a.hom L) := by
    change classOf D.X.left L' = pullbackClass a.hom (classOf D.X.left L)
    dsimp only [L, L']
    rw [kernelPointLineBundle_class, kernelPointLineBundle_class]
    exact (pointDivisorClass_semilinear D hD a c ho (kernelPoint d y) (kernelPoint d y') hy).symm
  obtain ⟨e⟩ := Quotient.exact he
  have hi := congrArg (fun χ => χ x')
    (lineBundleKernelCharacter_iso f hE L' (pullbackLineBundle a.hom L) e hL' hM)
  exact hi.trans (lineBundleKernelCharacter_semilinear f hE L hL a.hom b.hom w σ hb x x' hx)

end AlgebraicGeometry.Scheme.Group.IsogenyPairing
