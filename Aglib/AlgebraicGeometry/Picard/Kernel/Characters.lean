/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Pullback
public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Translation
public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange

/-!
# Normalization on the original Picard pullback kernel

The universal source-pullback comparison trivializes the actual universal
rigidified pair at a point of the original pullback kernel. This construction
uses the same supplied representatives and their one universal pair. It is
defined on every test scheme by pulling back the universal comparison; no
extension of locally Noetherian Picard representability is asserted.
The original kernel marking then turns the transported cocycle of a
trivialized family into its actual relative multiplicative-group character.
The construction commutes with parameter pullback and tensor products.
A trivial character descends the same given frame by full faithfulness.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : Over S}
  [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
  [IsProper Y.hom] [Flat Y.hom] [GeometricallyIntegral Y.hom]
  (PX : LocallyNoetherianOver S) [LocallyOfFiniteType PX.obj.hom]
  (RX : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PX)
  (PY : LocallyNoetherianOver S)
  (RY : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf Y.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PY)
  (oX : 𝟙_ (Over S) ⟶ X) (oY : 𝟙_ (Over S) ⟶ Y)
  (f : X ⟶ Y) (hf : oX ≫ f = oY)

/-- The original source pullback of the original universal pair has its
unique origin-normalized trivialization on the actual Picard kernel.
The kernel equation is a whole morphism equation on the original test. -/
def picardKernelTrivialization {T : Over S} (t : T ⟶ PY.obj)
    (ht : letI := picardCommGrpObj X.hom PX RX
      t ≫ picardPullback PX RX PY RY f = 1) :
    RigidifiedPair.Iso
      (RigidifiedPair.sourcePullback oX oY f hf (RigidifiedPair.map t
        (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY)))
      (trivialRigidifiedPair X.hom oX.left (Over.w oX) T) := by
  letI := picardCommGrpObj X.hom PX RX
  exact (picardPullbackUniversalPullbackIso PX RX PY RY oX oY f hf t).symm.trans
    ((RigidifiedPair.mapCongrIso ht
      (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX)).trans
        (fppfUniversalRigidifiedUnitIso X.hom oX.left (Over.w oX) RX T))

/-- Uniqueness is valid on every test scheme, including nonreduced and
non-Noetherian ones, by the original source's universal O-connectedness. -/
theorem picardKernelTrivialization_unique {T : Over S} (t : T ⟶ PY.obj)
    (ht : letI := picardCommGrpObj X.hom PX RX
      t ≫ picardPullback PX RX PY RY f = 1)
    (e : RigidifiedPair.Iso
      (RigidifiedPair.sourcePullback oX oY f hf (RigidifiedPair.map t
        (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY)))
      (trivialRigidifiedPair X.hom oX.left (Over.w oX) T)) :
    e = picardKernelTrivialization PX RX PY RY oX oY f hf t ht :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    X.hom oX.left (Over.w oX) _ _

/-- Parameter pullback of the same normalized trivialization is the
normalized trivialization at the pulled-back point. The comparison uses
only the original source/parameter and trivial-pair isomorphisms. -/
theorem picardKernelTrivialization_naturality {T T' : Over S}
    (a : T' ⟶ T) (t : T ⟶ PY.obj)
    (ht : letI := picardCommGrpObj X.hom PX RX
      t ≫ picardPullback PX RX PY RY f = 1) :
    picardKernelTrivialization PX RX PY RY oX oY f hf (a ≫ t)
        (by
          let := picardCommGrpObj X.hom PX RX
          rw [Category.assoc, ht, MonObj.comp_one]) =
      (RigidifiedPair.Iso.sourcePullback oX oY f hf
        (RigidifiedPair.mapCompIso a t
          (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY))).trans
        ((RigidifiedPair.sourcePullbackParameterIso oX oY f hf a
          (RigidifiedPair.map t
            (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY))).symm.trans
          ((RigidifiedPair.Iso.map a
            (picardKernelTrivialization PX RX PY RY oX oY f hf t ht)).trans
              (trivialRigidifiedPairMapIso X.hom oX.left (Over.w oX) a))) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    X.hom oX.left (Over.w oX) _ _

variable [LocallyOfFiniteType PY.obj.hom]

/-- A trivialization of the actual universal pullback detects the original
Picard unit on a locally Noetherian test. This is precisely the represented
test boundary needed after descending a kernel trivialization. -/
theorem eq_one_of_universalRigidifiedPullbackIso
    {T : LocallyNoetherianOver S} (t : T.obj ⟶ PY.obj)
    (e : RigidifiedPair.Iso
      (RigidifiedPair.map t
        (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY))
      (trivialRigidifiedPair Y.hom oY.left (Over.w oY) T.obj)) :
    letI := picardCommGrpObj Y.hom PY RY
    t = 1 := by
  let := picardCommGrpObj Y.hom PY RY
  let Rr := rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral
    Y.hom oY.left (Over.w oY) RY
  have hq : (Quotient.mk _ (RigidifiedPair.map t
      (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY)) :
        (rigidifiedPicardFunctor Y.hom oY.left (Over.w oY)).obj (op T.obj)) =
      Quotient.mk _ (trivialRigidifiedPair Y.hom oY.left (Over.w oY) T.obj) :=
    Quotient.sound ⟨e⟩
  have h : Rr.homEquiv (ObjectProperty.homMk t : T ⟶ PY) =
      Rr.homEquiv (ObjectProperty.homMk (1 : T.obj ⟶ PY.obj) : T ⟶ PY) :=
    (universalRigidifiedPullback_class Y.hom oY.left (Over.w oY) Rr
      (ObjectProperty.homMk t : T ⟶ PY)).symm.trans
        (hq.trans (rigidifiedRepresentableBy_homEquiv_one
          Y.hom oY.left (Over.w oY) RY T).symm)
  exact congrArg (fun q : T ⟶ PY => q.hom) (Rr.homEquiv.injective h)

end AlgebraicGeometry.Scheme.RelativePicard

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Modules Modules.Invertible Modules.TrivializedDescent Scheme.OverField Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

section Units

variable {S : Scheme.{u}} {X : Over S} (o : 𝟙_ (Over S) ⟶ X) (T : Over S)

/-- Universal O-connectedness makes every actual unit on the original
family constant in the source direction. Its coefficient is its original
origin restriction. -/
theorem globalUnit_eq_pullback_origin [IsIso (pullback.snd X.hom T.hom).c]
    (v : Γ(pullback X.hom T.hom, ⊤)ˣ) :
    Units.map (pullback.snd X.hom T.hom).appTop.hom.toMonoidHom
        (Units.map (originSection X.hom o.left (Over.w o) T).appTop.hom.toMonoidHom v) =
      v := by
  apply Units.ext
  have hb : Function.Bijective (pullback.snd X.hom T.hom).appTop :=
    ConcreteCategory.bijective_of_isIso ((pullback.snd X.hom T.hom).c.app (op ⊤))
  obtain ⟨a, ha⟩ := hb.2 v.val
  change (pullback.snd X.hom T.hom).appTop
    ((originSection X.hom o.left (Over.w o) T).appTop v.val) = v.val
  rw [← ha, RigidifiedPair.originSection_appTop_snd_appTop]

private theorem mapUnit_comp {V W Z : Scheme.{u}} (r : V ⟶ W) (s : W ⟶ Z)
    (v : Γ(Z, ⊤)ˣ) :
    Units.map r.appTop.hom.toMonoidHom (Units.map s.appTop.hom.toMonoidHom v) =
      Units.map (r ≫ s).appTop.hom.toMonoidHom v := by
  apply Units.ext
  simp only [Units.coe_map, Scheme.Hom.comp_appTop]
  rfl

private theorem mapUnit_factor {U V W : Scheme.{u}} (r : U ⟶ V) (p : V ⟶ W) (s : U ⟶ W)
    (hrs : r ≫ p = s) (c : Γ(V, ⊤)ˣ) (d : Γ(W, ⊤)ˣ)
    (h : Units.map p.appTop.hom.toMonoidHom d = c) :
    Units.map r.appTop.hom.toMonoidHom c = Units.map s.appTop.hom.toMonoidHom d :=
  (congrArg (Units.map r.appTop.hom.toMonoidHom) h.symm).trans
    ((mapUnit_comp r p d).trans
      (congrArg (fun f : U ⟶ W => Units.map f.appTop.hom.toMonoidHom d) hrs))

end Units

section Family

variable {k : Type u} [Field k] {A B K : Grp (FScheme k)} (q : A ⟶ B)
  (m : KernelMarking K A B q)
  (T : FScheme k) (M : LineBundle (pullback B.X.hom T.hom))
  (a : (Modules.pullback (familyMapOfHom q.hom.hom T)).obj M.val ≅
    (SheafOfModules.unit (pullback A.X.hom T.hom).ringCatSheaf :
      (pullback A.X.hom T.hom).Modules))

/-- The original source-pullback family map retains both actual
coordinates of a test point. -/
theorem lift_comp_familyMap {U : FScheme k} (x : U ⟶ A.X) (t : U ⟶ T) :
    (lift x t).left ≫ familyMapOfHom q.hom.hom T =
      (lift (x ≫ q.hom.hom) t).left := by
  apply pullback.hom_ext <;>
    simp [Category.assoc, Over.lift_left, familyMapOfHom_fst, familyMapOfHom_snd]

/-- The original transition evaluated on two family points with the same
image under the original homomorphism. -/
def familyTransitionUnit {U : FScheme k} (x y : U ⟶ A.X) (t : U ⟶ T)
    (h : x ≫ q.hom.hom = y ≫ q.hom.hom) : Γ(U.left, ⊤)ˣ :=
  unit (familyMapOfHom q.hom.hom T) M a
    (lift (x ≫ q.hom.hom) t).left (lift x t).left (lift y t).left
    (lift_comp_familyMap q T x t)
    ((lift_comp_familyMap q T y t).trans
      (congrArg (fun z => (lift z t).left) h.symm))

/-- Naturality of the original transition functions on arbitrary tests. -/
theorem familyTransitionUnit_pullback {U U' : FScheme k} (r : U' ⟶ U)
    (x y : U ⟶ A.X) (t : U ⟶ T)
    (h : x ≫ q.hom.hom = y ≫ q.hom.hom) :
    Units.map r.left.appTop.hom.toMonoidHom (familyTransitionUnit q T M a x y t h) =
      familyTransitionUnit q T M a (r ≫ x) (r ≫ y) (r ≫ t)
        (by simpa only [Category.assoc] using congrArg (fun z => r ≫ z) h) := by
  unfold familyTransitionUnit
  simpa only [← Over.comp_left, comp_lift, Category.assoc] using
    unit_pullback (familyMapOfHom q.hom.hom T) M a r.left
      (lift (x ≫ q.hom.hom) t).left (lift x t).left (lift y t).left
      (lift_comp_familyMap q T x t)
      ((lift_comp_familyMap q T y t).trans
        (congrArg (fun z => (lift z t).left) h.symm))

/-- The original family transition functions obey the original cocycle law. -/
theorem familyTransitionUnit_comp {U : FScheme k} (x y z : U ⟶ A.X) (t : U ⟶ T)
    (hxy : x ≫ q.hom.hom = y ≫ q.hom.hom)
    (hyz : y ≫ q.hom.hom = z ≫ q.hom.hom) :
    familyTransitionUnit q T M a x y t hxy * familyTransitionUnit q T M a y z t hyz =
      familyTransitionUnit q T M a x z t (hxy.trans hyz) := by
  unfold familyTransitionUnit
  simpa only [← hxy] using
    unit_comp (familyMapOfHom q.hom.hom T) M a
      (lift (x ≫ q.hom.hom) t).left (lift x t).left (lift y t).left (lift z t).left
      (lift_comp_familyMap q T x t)
      ((lift_comp_familyMap q T y t).trans
        (congrArg (fun z => (lift z t).left) hxy.symm))
      ((lift_comp_familyMap q T z t).trans
        (congrArg (fun z => (lift z t).left) (hxy.trans hyz).symm))

/-- Repeated family points have the actual unit transition. -/
@[simp]
theorem familyTransitionUnit_self {U : FScheme k} (x : U ⟶ A.X) (t : U ⟶ T) :
    familyTransitionUnit q T M a x x t rfl = 1 := by
  unfold familyTransitionUnit
  exact unit_self _ _ _ _ _ _

/-- The unit multiplier on the original kernel family, evaluated at the
source unit using the actual action of the supplied kernel marking. -/
def kernelMultiplier : Γ((K.X ⊗ T).left, ⊤)ˣ :=
  let τ := m.toTorsorAction
  familyTransitionUnit q T M a 1
    (τ.act (fst K.X T) 1) (snd K.X T) ((τ.over (fst K.X T) 1).symm)

/-- The original kernel multiplier as a morphism to the original
relative multiplicative-group scheme. -/
def kernelTrivializationCharacterMap :
    (MultiplicativeBaseChange.baseChangedGroup T.hom K).X ⟶
      (MultiplicativeGroup.groupScheme T.left).X :=
  (MultiplicativeGroup.sectionsUnitsEquiv T.left
    (MultiplicativeBaseChange.baseChangedGroup T.hom K).X).symm
      (kernelMultiplier q m T M a)

/-- Its unit coordinate on every test is the original pulled-back
multiplier, with no affine or reducedness restriction on that test. -/
theorem kernelTrivializationCharacterMap_units (U : Over T.left)
    (g : U ⟶ (MultiplicativeBaseChange.baseChangedGroup T.hom K).X) :
    MultiplicativeBaseChange.unitsSectionsEquiv T.left U
        (g ≫ kernelTrivializationCharacterMap q m T M a) =
      Units.map g.left.appTop.hom.toMonoidHom (kernelMultiplier q m T M a) := by
  change (MultiplicativeGroup.unitsRepresentable T.left).homEquiv
    (g ≫ kernelTrivializationCharacterMap q m T M a) = _
  rw [(MultiplicativeGroup.unitsRepresentable T.left).homEquiv_comp]
  exact congrArg (Units.map g.left.appTop.hom.toMonoidHom)
    ((MultiplicativeGroup.sectionsUnitsEquiv T.left _).apply_symm_apply _)

private theorem pullbackSection_lift (U : Over T.left)
    (g : U ⟶ (MultiplicativeBaseChange.baseChangedGroup T.hom K).X) :
    (lift (MultiplicativeBaseChange.pullbackSectionsEquiv T.hom K U g)
      (Over.homMk U.hom : (Over.map T.hom).obj U ⟶ T)).left = g.left := by
  apply pullback.hom_ext
  · simp only [Over.lift_left, pullback.lift_fst]
    rfl
  · simp only [Over.lift_left, pullback.lift_snd]
    exact g.w.symm

/-- The actual transported cocycle evaluated on the universal pair of
source and kernel points over the original parameter scheme. -/
def kernelActionTransitionUnit : Γ((A.X ⊗ (K.X ⊗ T)).left, ⊤)ˣ :=
  let H := K.X ⊗ T
  let x := fst A.X H
  let g := snd A.X H ≫ fst K.X T
  let t := snd A.X H ≫ snd K.X T
  familyTransitionUnit q T M a x (m.toTorsorAction.act g x) t
    (m.toTorsorAction.over g x).symm

private theorem familyTransitionUnit_congr {U : FScheme k}
    {x y x' y' : U ⟶ A.X} {t t' : U ⟶ T}
    (h : x ≫ q.hom.hom = y ≫ q.hom.hom) (h' : x' ≫ q.hom.hom = y' ≫ q.hom.hom)
    (hx : x = x') (hy : y = y') (ht : t = t') :
    familyTransitionUnit q T M a x y t h = familyTransitionUnit q T M a x' y' t' h' := by
  cases hx
  cases hy
  cases ht
  rfl

private theorem kernelActionTransitionUnit_restriction {U : FScheme k}
    (r : U ⟶ A.X ⊗ (K.X ⊗ T)) (x : U ⟶ A.X) (g : U ⟶ K.X) (t : U ⟶ T)
    (hx : r ≫ fst A.X (K.X ⊗ T) = x)
    (hg : r ≫ snd A.X (K.X ⊗ T) ≫ fst K.X T = g)
    (ht : r ≫ snd A.X (K.X ⊗ T) ≫ snd K.X T = t) :
    Units.map r.left.appTop.hom.toMonoidHom (kernelActionTransitionUnit q m T M a) =
      familyTransitionUnit q T M a x (m.toTorsorAction.act g x) t
        (m.toTorsorAction.over g x).symm := by
  let H := K.X ⊗ T
  let x₀ := fst A.X H
  let g₀ := snd A.X H ≫ fst K.X T
  let t₀ := snd A.X H ≫ snd K.X T
  have h := familyTransitionUnit_pullback q T M a r x₀
    (m.toTorsorAction.act g₀ x₀) t₀ (m.toTorsorAction.over g₀ x₀).symm
  have hy : r ≫ m.toTorsorAction.act g₀ x₀ = m.toTorsorAction.act g x :=
    (m.toTorsorAction.naturality r g₀ x₀).trans
      (congrArg₂ (fun g' x' => m.toTorsorAction.act g' x') hg hx)
  exact h.trans (familyTransitionUnit_congr q T M a _ _ hx hy ht)

variable [IsProper A.X.hom] [GeometricallyIntegral A.X.hom]

/-- Universal structure-sheaf connectedness makes the actual transported
cocycle the pullback of the kernel multiplier along the original projection. -/
theorem kernelActionTransitionUnit_eq_pullback :
    Units.map (snd A.X (K.X ⊗ T)).left.appTop.hom.toMonoidHom
        (kernelMultiplier q m T M a) = kernelActionTransitionUnit q m T M a := by
  let H := K.X ⊗ T
  let o : H ⟶ A.X ⊗ H := lift (1 : H ⟶ A.X) (𝟙 H)
  let c := kernelActionTransitionUnit q m T M a
  have hx : o ≫ fst A.X H = 1 := lift_fst _ _
  have hg : o ≫ snd A.X H ≫ fst K.X T = fst K.X T := by
    simp only [o, lift_snd_assoc, Category.id_comp]
  have ht : o ≫ snd A.X H ≫ snd K.X T = snd K.X T := by
    simp only [o, lift_snd_assoc, Category.id_comp]
  have hco : Units.map o.left.appTop.hom.toMonoidHom c = kernelMultiplier q m T M a :=
    kernelActionTransitionUnit_restriction q m T M a o 1 (fst K.X T) (snd K.X T) hx hg ht
  have : IsIso (pullback.snd A.X.hom H.hom).c :=
    isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral A.X.hom H.hom
  have hu := globalUnit_eq_pullback_origin η[A.X] H c
  rw [originSection_eq_unit_axis A.X H] at hu
  have hu' : Units.map (snd A.X H).left.appTop.hom.toMonoidHom
      (Units.map o.left.appTop.hom.toMonoidHom c) = c := hu
  exact (congrArg (Units.map (snd A.X H).left.appTop.hom.toMonoidHom) hco.symm).trans hu'

/-- The original transported multiplier is constant along the original
proper source, on every test scheme. Its coefficient is exactly the
original kernel multiplier, with convention `a(gx)=chi(g)a(x)`. -/
theorem familyTransitionUnit_kernel_translate {U : FScheme k}
    (x : U ⟶ A.X) (g : U ⟶ K.X) (t : U ⟶ T) :
    familyTransitionUnit q T M a x (m.toTorsorAction.act g x) t
        (m.toTorsorAction.over g x).symm =
      Units.map (lift g t).left.appTop.hom.toMonoidHom (kernelMultiplier q m T M a) := by
  let H := K.X ⊗ T
  let V := A.X ⊗ H
  let r : U ⟶ V := lift x (lift g t)
  let p : V.left ⟶ H.left := (snd A.X H).left
  let s : U.left ⟶ H.left := (lift g t).left
  let c : Γ(V.left, ⊤)ˣ := kernelActionTransitionUnit q m T M a
  let χ : Γ(H.left, ⊤)ˣ := kernelMultiplier q m T M a
  have hx : r ≫ fst A.X H = x := lift_fst _ _
  have hg : r ≫ snd A.X H ≫ fst K.X T = g := by
    simp only [r, lift_snd_assoc, lift_fst]
  have ht : r ≫ snd A.X H ≫ snd K.X T = t := by
    simp only [r, lift_snd_assoc, lift_snd]
  have h : Units.map r.left.appTop.hom.toMonoidHom c =
      familyTransitionUnit q T M a x (m.toTorsorAction.act g x) t
        (m.toTorsorAction.over g x).symm :=
    kernelActionTransitionUnit_restriction q m T M a r x g t hx hg ht
  have hc : Units.map p.appTop.hom.toMonoidHom χ = c :=
    kernelActionTransitionUnit_eq_pullback q m T M a
  have hr : r ≫ snd A.X H = lift g t := lift_snd _ _
  have hs : r.left ≫ p = s := congrArg Over.Hom.left hr
  exact h.symm.trans (mapUnit_factor r.left p s hs c χ hc)

/-- The original multiplier preserves multiplication on every actual
kernel-valued test, including nonreduced parameter schemes. -/
theorem kernelMultiplier_mul {U : FScheme k}
    (g h : U ⟶ K.X) (t : U ⟶ T) :
    Units.map (lift (g * h) t).left.appTop.hom.toMonoidHom (kernelMultiplier q m T M a) =
      Units.map (lift g t).left.appTop.hom.toMonoidHom (kernelMultiplier q m T M a) *
        Units.map (lift h t).left.appTop.hom.toMonoidHom (kernelMultiplier q m T M a) := by
  let τ := m.toTorsorAction
  let x : U ⟶ A.X := 1
  let y : U ⟶ A.X := τ.act h x
  let z : U ⟶ A.X := τ.act g y
  have hy : x ≫ q.hom.hom = y ≫ q.hom.hom := (τ.over h x).symm
  have hz : y ≫ q.hom.hom = z ≫ q.hom.hom := (τ.over g y).symm
  have hxy := familyTransitionUnit_kernel_translate q m T M a x h t
  have hyz := familyTransitionUnit_kernel_translate q m T M a y g t
  have hxz := familyTransitionUnit_kernel_translate q m T M a x (g * h) t
  have hz' : τ.act (g * h) x = z := τ.mul_act g h x
  have hc := familyTransitionUnit_comp q T M a x y z t hy hz
  calc
    _ = familyTransitionUnit q T M a x z t (hy.trans hz) := by
      simpa only [← hz'] using hxz.symm
    _ = familyTransitionUnit q T M a x y t hy * familyTransitionUnit q T M a y z t hz :=
      hc.symm
    _ = Units.map (lift h t).left.appTop.hom.toMonoidHom (kernelMultiplier q m T M a) *
        Units.map (lift g t).left.appTop.hom.toMonoidHom (kernelMultiplier q m T M a) :=
      congrArg₂ (· * ·) hxy hyz
    _ = _ := mul_comm _ _

/-- The original multiplier has the actual unit value at the actual
kernel unit on every test. -/
theorem kernelMultiplier_one {U : FScheme k} (t : U ⟶ T) :
    Units.map (lift (1 : U ⟶ K.X) t).left.appTop.hom.toMonoidHom
      (kernelMultiplier q m T M a) = 1 := by
  simpa only [m.toTorsorAction.one_act, familyTransitionUnit_self] using
    (familyTransitionUnit_kernel_translate q m T M a (1 : U ⟶ A.X) 1 t).symm

/-- The actual character morphism preserves multiplication on all
test schemes over the actual parameter scheme. -/
theorem kernelTrivializationCharacterMap_mul (U : Over T.left)
    (g h : U ⟶ (MultiplicativeBaseChange.baseChangedGroup T.hom K).X) :
    (g * h) ≫ kernelTrivializationCharacterMap q m T M a =
      (g ≫ kernelTrivializationCharacterMap q m T M a) *
        (h ≫ kernelTrivializationCharacterMap q m T M a) := by
  apply (MultiplicativeBaseChange.unitsSectionsEquiv T.left U).injective
  rw [map_mul, kernelTrivializationCharacterMap_units,
    kernelTrivializationCharacterMap_units, kernelTrivializationCharacterMap_units]
  let e := MultiplicativeBaseChange.pullbackSectionsEquiv T.hom K U
  have hm := kernelMultiplier_mul q m T M a (e g) (e h)
    (Over.homMk U.hom : (Over.map T.hom).obj U ⟶ T)
  rw [← map_mul e] at hm
  simp only [e, pullbackSection_lift] at hm
  exact hm

/-- The actual character morphism preserves the actual unit on every test. -/
theorem kernelTrivializationCharacterMap_one (U : Over T.left) :
    (1 : U ⟶ (MultiplicativeBaseChange.baseChangedGroup T.hom K).X) ≫
      kernelTrivializationCharacterMap q m T M a = 1 := by
  apply (MultiplicativeBaseChange.unitsSectionsEquiv T.left U).injective
  rw [map_one, kernelTrivializationCharacterMap_units]
  let e := MultiplicativeBaseChange.pullbackSectionsEquiv T.hom K U
  have hm := kernelMultiplier_one q m T M a
    (Over.homMk U.hom : (Over.map T.hom).obj U ⟶ T)
  rw [← map_one e] at hm
  simp only [e, pullbackSection_lift] at hm
  exact hm

/-- The original torsor cocycle yields a genuine morphism of the
original group schemes, before applying Cartier representability. -/
theorem isMonHom_kernelTrivializationCharacterMap :
    IsMonHom (kernelTrivializationCharacterMap q m T M a) where
  one_hom := by
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using
      kernelTrivializationCharacterMap_one q m T M a (𝟙_ (Over T.left))
  mul_hom := by
    let H := (MultiplicativeBaseChange.baseChangedGroup T.hom K).X
    have hm := kernelTrivializationCharacterMap_mul q m T M a (H ⊗ H) (fst H H) (snd H H)
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
    exact hm.trans (congrArg (fun f => f ≫ μ[(MultiplicativeGroup.groupScheme T.left).X])
      (lift_fst_comp_snd_comp (kernelTrivializationCharacterMap q m T M a)
        (kernelTrivializationCharacterMap q m T M a)))

/-- The actual kernel-family character of the supplied original
trivialization, as a morphism in the existing group category. -/
def kernelTrivializationCharacter :
    MultiplicativeBaseChange.baseChangedGroup T.hom K ⟶
      MultiplicativeGroup.groupScheme T.left :=
  letI := isMonHom_kernelTrivializationCharacterMap q m T M a
  Grp.homMk (kernelTrivializationCharacterMap q m T M a)

/-- The actual character has exactly the original global multiplier as
its represented unit, with no restriction on the parameter scheme. -/
theorem sectionsUnitsEquiv_kernelTrivializationCharacter :
    MultiplicativeGroup.sectionsUnitsEquiv T.left
      (MultiplicativeBaseChange.baseChangedGroup T.hom K).X
      (kernelTrivializationCharacter q m T M a).hom.hom = kernelMultiplier q m T M a :=
  (MultiplicativeGroup.sectionsUnitsEquiv T.left _).apply_symm_apply _

/-- Triviality of the whole character morphism makes its actual
multiplier the unit function. -/
theorem kernelMultiplier_eq_one_of_characterMap_eq_one
    (h : kernelTrivializationCharacterMap q m T M a = 1) :
    kernelMultiplier q m T M a = 1 := by
  have hv := sectionsUnitsEquiv_kernelTrivializationCharacter q m T M a
  change MultiplicativeBaseChange.unitsSectionsEquiv T.left
      (MultiplicativeBaseChange.baseChangedGroup T.hom K).X
      (kernelTrivializationCharacterMap q m T M a) = _ at hv
  rw [h, map_one] at hv
  exact hv.symm

/-- Every original overlap transition is trivial when the character is
trivial. The actual kernel marking transports the two given points. -/
theorem familyTransitionUnit_eq_one_of_kernelMultiplier_eq_one {U : FScheme k}
    (x y : U ⟶ A.X) (t : U ⟶ T) (h : x ≫ q.hom.hom = y ≫ q.hom.hom)
    (hc : kernelMultiplier q m T M a = 1) : familyTransitionUnit q T M a x y t h = 1 := by
  obtain ⟨g, hg, _⟩ := m.toTorsorAction.transport x y h
  subst y
  rw [familyTransitionUnit_kernel_translate q m T M a x g t, hc, map_one]

/-- This triviality holds for all overlap maps of the literal original
family cover, with no local Noetherian hypothesis on the overlap test. -/
theorem transitionUnit_eq_one_of_kernelMultiplier_eq_one {V : Scheme.{u}}
    (s : V ⟶ pullback B.X.hom T.hom) (v w : V ⟶ pullback A.X.hom T.hom)
    (hv : v ≫ familyMapOfHom q.hom.hom T = s)
    (hw : w ≫ familyMapOfHom q.hom.hom T = s)
    (hc : kernelMultiplier q m T M a = 1) :
    unit (familyMapOfHom q.hom.hom T) M a s v w hv hw = 1 := by
  have hq := hv.trans hw.symm
  have hp := congrArg (fun r => r ≫ pullback.snd B.X.hom T.hom) hq
  have h₁ := congrArg (fun r => r ≫ pullback.fst B.X.hom T.hom) hq
  simp only [Category.assoc, familyMapOfHom_snd] at hp
  simp only [Category.assoc, familyMapOfHom_fst] at h₁
  let U : FScheme k := Over.mk ((v ≫ pullback.snd A.X.hom T.hom) ≫ T.hom)
  let t : U ⟶ T := Over.homMk (v ≫ pullback.snd A.X.hom T.hom)
  let x : U ⟶ A.X := Over.homMk (v ≫ pullback.fst A.X.hom T.hom) (by
    change (v ≫ pullback.fst A.X.hom T.hom) ≫ A.X.hom =
      (v ≫ pullback.snd A.X.hom T.hom) ≫ T.hom
    simp only [Category.assoc, pullback.condition])
  let y : U ⟶ A.X := Over.homMk (w ≫ pullback.fst A.X.hom T.hom) (by
    change (w ≫ pullback.fst A.X.hom T.hom) ≫ A.X.hom =
      (v ≫ pullback.snd A.X.hom T.hom) ≫ T.hom
    rw [hp, Category.assoc, Category.assoc, pullback.condition])
  have hxy : x ≫ q.hom.hom = y ≫ q.hom.hom := by
    apply Over.OverMorphism.ext
    change (v ≫ pullback.fst A.X.hom T.hom) ≫ q.hom.hom.left =
      (w ≫ pullback.fst A.X.hom T.hom) ≫ q.hom.hom.left
    simpa only [Category.assoc] using h₁
  have hvl : (lift x t).left = v := by
    apply pullback.hom_ext <;> simp only [Over.lift_left, pullback.lift_fst,
      pullback.lift_snd, x, t, Over.homMk_left]
  have hwl : (lift y t).left = w := by
    apply pullback.hom_ext
    · simp only [Over.lift_left, pullback.lift_fst, y, Over.homMk_left]
    · simpa only [Over.lift_left, pullback.lift_snd, t, Over.homMk_left] using hp
  have hsl : (lift (x ≫ q.hom.hom) t).left = s :=
    (lift_comp_familyMap q T x t).symm.trans (by rw [hvl, hv])
  have htr : familyTransitionUnit q T M a x y t hxy =
      unit (familyMapOfHom q.hom.hom T) M a s v w hv hw := by
    unfold familyTransitionUnit
    exact unit_congr _ _ _ _ _ hv hw hsl hvl hwl
  exact htr.symm.trans (familyTransitionUnit_eq_one_of_kernelMultiplier_eq_one
    q m T M a x y t hxy hc)

/-- The original frame with trivial character descends as an isomorphism
of the given original bundle with the structure module. -/
def descendKernelTrivialization
    (hf : Sieve.ofArrows (fun _ : PUnit.{1} => pullback A.X.hom T.hom)
        (fun _ : PUnit.{1} => familyMapOfHom q.hom.hom T) ∈
      Scheme.fppfTopology (pullback B.X.hom T.hom))
    (h : kernelTrivializationCharacterMap q m T M a = 1) :
    (M.val : (pullback B.X.hom T.hom).Modules) ≅
      SheafOfModules.unit (pullback B.X.hom T.hom).ringCatSheaf :=
  descendFrameIso (familyMapOfHom q.hom.hom T) M a hf
    (fun s v w hv hw => transitionUnit_eq_one_of_kernelMultiplier_eq_one q m T M a s v w hv hw
      (kernelMultiplier_eq_one_of_characterMap_eq_one q m T M a h))

open Modules.Invertible.TrivializedPower (unitOfIso)
open Modules.Invertible.ScalarAutomorphisms (scalarIso unitAutoEquiv)

/-- For the actual proper source, changing the given bundle by an
isomorphism and the frame by any trivialization preserves every
transition of family points with the same parameter. -/
theorem familyTransitionUnit_congr_iso {U : FScheme k}
    (N : LineBundle (pullback B.X.hom T.hom)) (e : M.val ≅ N.val)
    (b : (Modules.pullback (familyMapOfHom q.hom.hom T)).obj N.val ≅
      (SheafOfModules.unit (pullback A.X.hom T.hom).ringCatSheaf :
        (pullback A.X.hom T.hom).Modules))
    (x y : U ⟶ A.X) (t : U ⟶ T) (h : x ≫ q.hom.hom = y ≫ q.hom.hom) :
    familyTransitionUnit q T M a x y t h = familyTransitionUnit q T N b x y t h := by
  let X := pullback A.X.hom T.hom
  let a₀ := (Modules.pullback (familyMapOfHom q.hom.hom T)).mapIso e ≪≫ b
  let d : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅
      SheafOfModules.unit X.ringCatSheaf := a₀.symm ≪≫ a
  let c := unitOfIso X d
  have hd := (unitAutoEquiv X).left_inv d
  change scalarIso X _ c = d at hd
  have ha : a = a₀ ≪≫ scalarIso X _ c := by
    rw [hd]
    apply Iso.ext
    simp only [d, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  have : IsIso (pullback.snd A.X.hom T.hom).c :=
    isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral A.X.hom T.hom
  have hc := globalUnit_eq_pullback_origin η[A.X] T c
  have huv : Units.map (lift x t).left.appTop.hom.toMonoidHom c =
      Units.map (lift y t).left.appTop.hom.toMonoidHom c := by
    let p := pullback.snd A.X.hom T.hom
    let c₀ := Units.map (originSection A.X.hom η[A.X].left (Over.w η[A.X])
      T).appTop.hom.toMonoidHom c
    have hc₀ : Units.map p.appTop.hom.toMonoidHom c₀ = c := hc
    have hx : (lift x t).left ≫ p = t.left := by
      change (lift x t ≫ snd A.X T).left = t.left
      rw [lift_snd]
    have hy : (lift y t).left ≫ p = t.left := by
      change (lift y t ≫ snd A.X T).left = t.left
      rw [lift_snd]
    let rx := (lift x t).left
    let ry := (lift y t).left
    have hxy := congrArg (fun f : U.left ⟶ T.left =>
      Units.map f.appTop.hom.toMonoidHom c₀) (hx.trans hy.symm)
    exact (congrArg (Units.map rx.appTop.hom.toMonoidHom) hc₀.symm).trans
      ((mapUnit_comp rx p c₀).trans (hxy.trans
        ((mapUnit_comp ry p c₀).symm.trans
          (congrArg (Units.map ry.appTop.hom.toMonoidHom) hc₀))))
  unfold familyTransitionUnit
  rw [ha]
  exact (unit_postcompose_scalar _ _ a₀ c _ _ _ _ _ huv).trans
    (unit_precompIso _ M N e b _ _ _ _ _)

/-- The original kernel multiplier is invariant under an isomorphism of
bundles, regardless of the compatible choice of frame. -/
theorem kernelMultiplier_eq_of_iso (N : LineBundle (pullback B.X.hom T.hom))
    (e : M.val ≅ N.val)
    (b : (Modules.pullback (familyMapOfHom q.hom.hom T)).obj N.val ≅
      (SheafOfModules.unit (pullback A.X.hom T.hom).ringCatSheaf :
        (pullback A.X.hom T.hom).Modules)) :
    kernelMultiplier q m T M a = kernelMultiplier q m T N b := by
  unfold kernelMultiplier
  exact familyTransitionUnit_congr_iso q T M a N e b _ _ _ _

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
/-- Tensoring actual bundles and actual frames multiplies the original
transition units at each pair of family points. -/
theorem familyTransitionUnit_tensor {U : FScheme k}
    (N : LineBundle (pullback B.X.hom T.hom))
    (b : (Modules.pullback (familyMapOfHom q.hom.hom T)).obj N.val ≅
      (SheafOfModules.unit (pullback A.X.hom T.hom).ringCatSheaf :
        (pullback A.X.hom T.hom).Modules))
    (x y : U ⟶ A.X) (t : U ⟶ T) (h : x ≫ q.hom.hom = y ≫ q.hom.hom) :
    familyTransitionUnit q T (tensorLineBundle _ M N)
        (FrameTensor.tensorFrame (familyMapOfHom q.hom.hom T) M N a b) x y t h =
      familyTransitionUnit q T M a x y t h * familyTransitionUnit q T N b x y t h := by
  unfold familyTransitionUnit
  exact unit_tensor _ M a N b _ _ _ _ _

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
/-- Tensoring actual bundles and actual frames multiplies their original
kernel multipliers. -/
theorem kernelMultiplier_tensor (N : LineBundle (pullback B.X.hom T.hom))
    (b : (Modules.pullback (familyMapOfHom q.hom.hom T)).obj N.val ≅
      (SheafOfModules.unit (pullback A.X.hom T.hom).ringCatSheaf :
        (pullback A.X.hom T.hom).Modules)) :
    kernelMultiplier q m T (tensorLineBundle _ M N)
        (FrameTensor.tensorFrame (familyMapOfHom q.hom.hom T) M N a b) =
      kernelMultiplier q m T M a * kernelMultiplier q m T N b := by
  let τ := m.toTorsorAction
  let x : K.X ⊗ T ⟶ A.X := 1
  let g := fst K.X T
  let t := snd K.X T
  exact familyTransitionUnit_tensor q T M a N b x (τ.act g x) t (τ.over g x).symm

/-- Pulling the original frame back along an actual parameter map uses
the existing frame comparison of the original commuting source square. -/
def familyFramePullback {T' : FScheme k} (r : T' ⟶ T) :
    (Modules.pullback (familyMapOfHom q.hom.hom T')).obj
      (pullbackLineBundle ((familyScheme B.X.hom).map r) M).val ≅
        (SheafOfModules.unit (pullback A.X.hom T'.hom).ringCatSheaf :
          (pullback A.X.hom T'.hom).Modules) :=
  Modules.Invertible.PowerBaseChange.pullbackFrame ((familyScheme B.X.hom).map r) M
    (familyMapOfHom q.hom.hom T) (familyMapOfHom q.hom.hom T')
    ((familyScheme A.X.hom).map r) (familyMapOfHom_naturality q.hom.hom r) a

private theorem lift_comp_familyScheme_map {S : Scheme.{u}} {X U V W : Over S}
    (x : U ⟶ X) (t : U ⟶ V) (r : V ⟶ W) :
    (lift x t).left ≫ (familyScheme X.hom).map r = (lift x (t ≫ r)).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, familyScheme_map_fst, Over.lift_left, pullback.lift_fst]
  · simp only [Category.assoc, familyScheme_map_snd, Over.lift_left, pullback.lift_snd,
      pullback.lift_snd_assoc,
      Over.comp_left]

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
/-- Pulling back the actual framed family gives the same original
transition at the composite parameter point. -/
theorem familyTransitionUnit_parameter {T' U : FScheme k} (r : T' ⟶ T)
    (x y : U ⟶ A.X) (t : U ⟶ T') (h : x ≫ q.hom.hom = y ≫ q.hom.hom) :
    familyTransitionUnit q T' (pullbackLineBundle ((familyScheme B.X.hom).map r) M)
        (familyFramePullback q T M a r) x y t h =
      familyTransitionUnit q T M a x y (t ≫ r) h := by
  let p := familyMapOfHom q.hom.hom T
  let p' := familyMapOfHom q.hom.hom T'
  let f := (familyScheme B.X.hom).map r
  let g := (familyScheme A.X.hom).map r
  let s := (lift (x ≫ q.hom.hom) t).left
  let v := (lift x t).left
  let w := (lift y t).left
  have hv : v ≫ p' = s := lift_comp_familyMap q T' x t
  have hw : w ≫ p' = s := (lift_comp_familyMap q T' y t).trans
    (congrArg (fun z => (lift z t).left) h.symm)
  have h' := unit_pullbackFrame p M a f p' g (familyMapOfHom_naturality q.hom.hom r)
    s v w hv hw
  unfold familyTransitionUnit
  exact h'.trans (unit_congr p M a _ _ _ _
    (lift_comp_familyScheme_map (x ≫ q.hom.hom) t r)
    (lift_comp_familyScheme_map x t r) (lift_comp_familyScheme_map y t r))

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
/-- The same multiplier commutes with arbitrary parameter pullback on the
original kernel family, before any Cartier representability is used. -/
theorem kernelMultiplier_parameter {T' : FScheme k} (r : T' ⟶ T) :
    kernelMultiplier q m T' (pullbackLineBundle ((familyScheme B.X.hom).map r) M)
        (familyFramePullback q T M a r) =
      Units.map ((familyScheme K.X.hom).map r).appTop.hom.toMonoidHom
        (kernelMultiplier q m T M a) := by
  let u : K.X ⊗ T' ⟶ K.X ⊗ T := lift (fst K.X T') (snd K.X T' ≫ r)
  have hu : u.left = (familyScheme K.X.hom).map r := by
    apply pullback.hom_ext <;> simp [u, Over.lift_left, Over.comp_left]
  let x : K.X ⊗ T ⟶ A.X := 1
  let g := fst K.X T
  let t := snd K.X T
  let x' : K.X ⊗ T' ⟶ A.X := 1
  have hx : u ≫ x = x' := MonObj.comp_one u
  have hg : u ≫ g = fst K.X T' := lift_fst _ _
  have ht : u ≫ t = snd K.X T' ≫ r := lift_snd _ _
  have hn := familyTransitionUnit_pullback q T M a u x (m.toTorsorAction.act g x)
    t (m.toTorsorAction.over g x).symm
  simp only [m.toTorsorAction.naturality, hx, hg, ht] at hn
  rw [hu] at hn
  exact (familyTransitionUnit_parameter q T M a r x'
    (m.toTorsorAction.act (fst K.X T') x') (snd K.X T')
    (m.toTorsorAction.over (fst K.X T') x').symm).trans hn.symm

end Family

end AlgebraicGeometry.Scheme.RelativePicard
