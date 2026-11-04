/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FrameInverse
public import Aglib.AlgebraicGeometry.Picard.Kernel.Characters
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel
public import Aglib.AlgebraicGeometry.Group.Kernel.Commutative
public import Aglib.AlgebraicGeometry.Torsors.Restriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedTorsor
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverClass
public import Aglib.CategoryTheory.Sites.Torsor.Pushout
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-! # The original frame torsor as an extension of structure group

The literal cover trivialization restricts to the original frame sheaf.
Positive frame transport uses the original kernel multiplier. Inversion
gives the coframe comparison with the inverse character.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory.Sheaf

section PushoutComparison

open CategoryTheory.Abelian.ExtensionPushout

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]
  {L M : Sheaf J AddCommGrpCat.{w}} {P : Torsor L} {Q : Torsor M} {χ : L ⟶ M}
  (r : Torsor.Hom χ P Q)

private abbrev pushoutInl {A B : Sheaf J AddCommGrpCat.{w}} (R : Torsor A) (f : A ⟶ B) :=
  pushout.inl (torsorKernelSheafInclusion R) (torsorDifferenceSheafMap R ≫ f)

private def pushoutMiddleMap :
    (torsorCoefficientExtension P χ).X₂ ⟶ (torsorCoefficientExtension Q (𝟙 M)).X₂ :=
  pushout.desc (torsorFreeSheafMap r ≫ pushoutInl Q (𝟙 M))
    (torsorCoefficientExtension Q (𝟙 M)).f (by
      have hi : torsorKernelSheafMap r ≫ torsorKernelSheafInclusion Q =
          torsorKernelSheafInclusion P ≫ torsorFreeSheafMap r :=
        (torsorAugmentationComplexMap r).comm₁₂
      change torsorKernelSheafInclusion P ≫ torsorFreeSheafMap r ≫ pushoutInl Q (𝟙 M) =
        (torsorDifferenceSheafMap P ≫ χ) ≫ (torsorCoefficientExtension Q (𝟙 M)).f
      calc
        _ = torsorKernelSheafMap r ≫ torsorKernelSheafInclusion Q ≫ pushoutInl Q (𝟙 M) := by
          rw [← Category.assoc, ← hi, Category.assoc]
        _ = torsorKernelSheafMap r ≫ (torsorDifferenceSheafMap Q ≫ 𝟙 M) ≫
            (torsorCoefficientExtension Q (𝟙 M)).f := by
          rw [pushout.condition]
          rfl
        _ = torsorKernelSheafMap r ≫ torsorDifferenceSheafMap Q ≫
            (torsorCoefficientExtension Q (𝟙 M)).f :=
          congrArg (fun f : torsorKernelSheaf Q ⟶ M =>
            torsorKernelSheafMap r ≫ f ≫ (torsorCoefficientExtension Q (𝟙 M)).f)
            (Category.comp_id (torsorDifferenceSheafMap Q))
        _ = _ := by rw [← Category.assoc, torsorDifferenceSheafMap_naturality r])

private theorem pushoutMiddleMap_inl :
    pushoutInl P χ ≫ pushoutMiddleMap r =
      torsorFreeSheafMap r ≫ pushoutInl Q (𝟙 M) :=
  pushout.inl_desc _ _ _

private theorem pushoutMiddleMap_inr :
    (torsorCoefficientExtension P χ).f ≫ pushoutMiddleMap r =
      (torsorCoefficientExtension Q (𝟙 M)).f :=
  pushout.inr_desc _ _ _

private theorem pushoutMiddleMap_projection :
    pushoutMiddleMap r ≫ (torsorCoefficientExtension Q (𝟙 M)).g =
      (torsorCoefficientExtension P χ).g := by
  apply pushout.hom_ext
  · change pushoutInl P χ ≫ pushoutMiddleMap r ≫ (torsorCoefficientExtension Q (𝟙 M)).g =
      pushoutInl P χ ≫ (torsorCoefficientExtension P χ).g
    rw [← Category.assoc, pushoutMiddleMap_inl, Category.assoc]
    have hQ : pushoutInl Q (𝟙 M) ≫ (torsorCoefficientExtension Q (𝟙 M)).g =
        torsorAugmentation Q :=
      inl_projection (torsorAugmentationComplex Q) (torsorDifferenceSheafMap Q ≫ 𝟙 M)
    have hP : pushoutInl P χ ≫ (torsorCoefficientExtension P χ).g = torsorAugmentation P :=
      inl_projection (torsorAugmentationComplex P) (torsorDifferenceSheafMap P ≫ χ)
    rw [hQ, hP]
    exact ((torsorAugmentationComplexMap r).comm₂₃).trans (Category.comp_id _)
  · change (torsorCoefficientExtension P χ).f ≫
        pushoutMiddleMap r ≫ (torsorCoefficientExtension Q (𝟙 M)).g =
      (torsorCoefficientExtension P χ).f ≫ (torsorCoefficientExtension P χ).g
    rw [← Category.assoc, pushoutMiddleMap_inr,
      (torsorCoefficientExtension Q (𝟙 M)).zero, (torsorCoefficientExtension P χ).zero]

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

private def pushoutFiberHom :
    Torsor.Hom (𝟙 M) (torsorPushout P χ) (torsorPushout Q (𝟙 M)) where
  map := ⟨{
    app U := TypeCat.ofHom fun t => ⟨(pushoutMiddleMap r).hom.app U t.val, by
      change (torsorCoefficientExtension Q (𝟙 M)).g.hom.app U
        ((pushoutMiddleMap r).hom.app U t.val) = (constantIntegerOne J).hom.app U PUnit.unit
      exact (congrArg
        (fun f : (torsorCoefficientExtension P χ).X₂ ⟶ (torsorCoefficientExtension P χ).X₃ =>
          f.hom.app U (show (torsorCoefficientExtension P χ).X₂.obj.obj U from t.val))
          (pushoutMiddleMap_projection r)).trans t.property⟩
    naturality {U V} f := by
      ext t
      apply Subtype.ext
      exact ConcreteCategory.congr_hom ((pushoutMiddleMap r).hom.naturality f) t.val }⟩
  equivariant U a t := by
    apply Subtype.ext
    change (pushoutMiddleMap r).hom.app U
      ((torsorCoefficientExtension P χ).f.hom.app U a +
        (show (torsorCoefficientExtension P χ).X₂.obj.obj U from t.val)) =
      (torsorCoefficientExtension Q (𝟙 M)).f.hom.app U a +
        (pushoutMiddleMap r).hom.app U t.val
    rw [map_add]
    exact congrArg (· + (pushoutMiddleMap r).hom.app U t.val)
      (congrArg (fun f => f.hom.app U a) (pushoutMiddleMap_inr r))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
private theorem freeSheafMap_generator (U : Cᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorFreeSheafMap r).hom.app U (torsorGenerator P U t) =
      torsorGenerator Q U (r.map.hom.app U t) := by
  have h := congrArg (fun f => f.app U (FreeAbelianGroup.of t))
    (toSheafify_naturality J (torsorFreePresheafMap r))
  change (toSheafify J (torsorFreePresheaf Q)).app U
      (FreeAbelianGroup.map (r.map.hom.app U) (FreeAbelianGroup.of t)) =
    (torsorFreeSheafMap r).hom.app U (torsorGenerator P U t) at h
  rw [FreeAbelianGroup.map_of_apply] at h
  exact h.symm

private theorem pushoutFiberHom_map :
    (torsorPushoutMap P χ).map ≫ (pushoutFiberHom r).map =
      r.map ≫ (torsorPushoutMap Q (𝟙 M)).map := by
  ext U t
  apply Subtype.ext
  change (pushoutMiddleMap r).hom.app U
      ((pushoutInl P χ).hom.app U (torsorGenerator P U t)) =
    (pushoutInl Q (𝟙 M)).hom.app U (torsorGenerator Q U (r.map.hom.app U t))
  exact (congrArg (fun f => f.hom.app U (torsorGenerator P U t)) (pushoutMiddleMap_inl r)).trans
    (congrArg ((pushoutInl Q (𝟙 M)).hom.app U) (freeSheafMap_generator r U t))

private def pushoutComparison : Torsor.Iso (torsorPushout P χ) Q :=
  (pushoutFiberHom r).toIso.trans (torsorPushoutMap Q (𝟙 M)).toIso.symm

private theorem pushoutComparison_map :
    (torsorPushoutMap P χ).map ≫ (pushoutComparison r).carrierIso.hom = r.map := by
  let e := (torsorPushoutMap Q (𝟙 M)).toIso.carrierIso
  apply (cancel_mono e.hom).mp
  change ((torsorPushoutMap P χ).map ≫ (pushoutFiberHom r).map ≫ e.inv) ≫ e.hom =
    r.map ≫ e.hom
  have he : e.hom = (torsorPushoutMap Q (𝟙 M)).map := rfl
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, he]
  exact pushoutFiberHom_map r

end PushoutComparison

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout

open Scheme.EtaleCohomology
open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.Invertible.EtaleDescent
open Scheme.Modules.Invertible.FrameTorsor Scheme.Modules.Invertible.FrameInverse
open Scheme.Modules.Invertible.TrivializedPowerTorsor
open Scheme.Modules.Invertible.PowerBaseChange
open GroupCohomology.Kummer.Coefficients
open CategoryTheory.CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

section FrameMaps

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (L : LineBundle X)
  (a : (Modules.pullback Y.obj.hom).obj L.val ≅ SheafOfModules.unit Y.obj.left.ringCatSheaf)

private def frameAt (U : X.Etale) (v : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    (frameSheaf etaleLineBundleDescent X L).obj.obj (op U) :=
  (frameSectionsEquiv etaleLineBundleDescent X L (op U)).symm
    (nativePullFrame L Y.obj.hom U.hom v.left v.w a)

private theorem frameAt_sections (U : X.Etale) (v : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    frameSectionsEquiv etaleLineBundleDescent X L (op U) (frameAt Y L a U v) =
      nativePullFrame L Y.obj.hom U.hom v.left v.w a :=
  (frameSectionsEquiv etaleLineBundleDescent X L (op U)).apply_symm_apply _

private theorem frameAt_naturality {U V : X.Etale} (f : U ⟶ V)
    (v : (Scheme.Etale.forget X).obj V ⟶ Y.obj) :
    (frameSheaf etaleLineBundleDescent X L).obj.map f.op (frameAt Y L a V v) =
      frameAt Y L a U ((Scheme.Etale.forget X).map f ≫ v) := by
  apply (frameSectionsEquiv etaleLineBundleDescent X L (op U)).injective
  apply Iso.ext
  rw [frameSections_restriction, frameAt_sections, frameAt_sections]
  exact congrArg (fun φ => φ.hom)
    (nativePullFrame_comp L Y.obj.hom V.hom U.hom v.left f.left v.w f.w a)

variable (H : Grp (Over X)) [IsCommMonObj H.X] [Surjective Y.obj.hom]
  (τ : TorsorAction H (toUnit Y.obj)) (χ : H ⟶ Group.MultiplicativeGroup.groupScheme X)

private def frameHomOfUnit
    (hχ : ∀ (U : X.Etale) (g : (Scheme.Etale.forget X).obj U ⟶ H.X)
      (v : (Scheme.Etale.forget X).obj U ⟶ Y.obj),
      TrivializedDescent.unit Y.obj.hom L a U.hom v.left (τ.act g v).left
          v.w (τ.act g v).w =
        Group.MultiplicativeGroup.sectionsUnitsEquiv X ((Scheme.Etale.forget X).obj U)
          (g ≫ χ.hom.hom)) :
    Torsor.Hom (representedSheafMap χ) (torsorOfSchemeAction H Y τ)
      (frameTorsor etaleLineBundleDescent X L) where
  map := ⟨{
    app U := TypeCat.ofHom (fun v => frameAt Y L a U.unop v.down)
    naturality {U V} f := by
      ext v
      exact (frameAt_naturality Y L a f.unop v.down).symm }⟩
  equivariant U g v := by
    change frameAt Y L a U.unop (τ.act g.down.toMul v.down) =
      frameAction etaleLineBundleDescent X L U ((representedSheafMap χ).hom.app U g)
        (frameAt Y L a U.unop v.down)
    apply (frameSectionsEquiv etaleLineBundleDescent X L U).injective
    have hv := frameAt_sections Y L a U.unop v.down
    have hw := frameAt_sections Y L a U.unop (τ.act g.down.toMul v.down)
    change frameSectionsEquiv etaleLineBundleDescent X L U (frameAt Y L a U.unop v.down) = _
      at hv
    change frameSectionsEquiv etaleLineBundleDescent X L U
      (frameAt Y L a U.unop (τ.act g.down.toMul v.down)) = _ at hw
    rw [frameAction_sections, hv, hw, representedSheafMap_app]
    change nativePullFrame L Y.obj.hom U.unop.hom (τ.act g.down.toMul v.down).left
        (τ.act g.down.toMul v.down).w a =
      nativePullFrame L Y.obj.hom U.unop.hom v.down.left v.down.w a ≪≫
        ScalarAutomorphisms.scalarIso U.unop.left _
          (Group.MultiplicativeGroup.sectionsUnitsEquiv X
            ((Scheme.Etale.forget X).obj U.unop) (g.down.toMul ≫ χ.hom.hom))
    rw [← hχ U.unop g.down.toMul v.down]
    exact TrivializedDescent.nativePullFrame_eq_scalar Y.obj.hom L a U.unop.hom v.down.left
      (τ.act g.down.toMul v.down).left v.down.w (τ.act g.down.toMul v.down).w

private def coframeHomOfFrame {A : AbelianSheaf.{u, u + 1} X} {P : Torsor A}
    {ψ : A ⟶ gm X} (r : Torsor.Hom ψ P (frameTorsor etaleLineBundleDescent X L)) :
    Torsor.Hom (ψ ≫ (-𝟙 (gm X))) P (coframeTorsor etaleLineBundleDescent X L) where
  map := r.map ≫ (frameInverseHom etaleLineBundleDescent X L).map
  equivariant U g v := by
    change (frameInverseHom etaleLineBundleDescent X L).map.hom.app U
        (r.map.hom.app U (P.action U g v)) =
      (coframeTorsor etaleLineBundleDescent X L).action U
        ((-𝟙 (gm X)).hom.app U (ψ.hom.app U g))
        ((frameInverseHom etaleLineBundleDescent X L).map.hom.app U (r.map.hom.app U v))
    rw [r.equivariant]
    exact (frameInverseHom etaleLineBundleDescent X L).equivariant U
      (ψ.hom.app U g) (r.map.hom.app U v)

end FrameMaps

section Family

open Scheme.OverField CategoryTheory.MonObj
open Scheme.Group
open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k] {A B : Grp (FScheme k)} (q : A ⟶ B)
  (T : FScheme k)

set_option hygiene false in
local notation "Aₜ" => Functor.obj (Functor.mapGrp (Over.pullback T.hom)) A
set_option hygiene false in
local notation "Bₜ" => Functor.obj (Functor.mapGrp (Over.pullback T.hom)) B
set_option hygiene false in
local notation "Kₜ" => Functor.obj (Functor.mapGrp (Over.pullback T.hom)) (Kernel.group q)
set_option hygiene false in
local notation "qₜ" => CategoryTheory.Functor.map (Functor.mapGrp (Over.pullback T.hom)) q
set_option hygiene false in
local notation "mₜ" => BaseChange.kernelMarking T.hom (Kernel.marking q)

/-- The original family cover as a finite étale object of its actual target. -/
abbrev familyCover [IsFinite q.hom.hom.left] [Etale q.hom.hom.left] :
    Scheme.FiniteEtale (Bₜ).X.left := by
  letI : IsFinite (qₜ).hom.hom.left := BaseChange.map_finite T.hom q inferInstance
  letI : Etale (qₜ).hom.hom.left := BaseChange.map_etale T.hom q inferInstance
  exact Scheme.FiniteEtale.mk (qₜ).hom.hom.left

/-- The original kernel coefficient, pulled back to the actual target of the family cover. -/
abbrev familyCoefficient : Grp (Over (Bₜ).X.left) :=
  (Over.pullback (Bₜ).X.hom).mapGrp.obj Kₜ

private theorem familyAction_transpose (U : Over T.left) (g : U ⟶ (Kₜ).X) (x : U ⟶ (Aₜ).X) :
    MultiplicativeBaseChange.pullbackSectionsEquiv T.hom A U ((mₜ).toTorsorAction.act g x) =
      (Kernel.marking q).toTorsorAction.act
        (MultiplicativeBaseChange.pullbackSectionsEquiv T.hom (Kernel.group q) U g)
        (MultiplicativeBaseChange.pullbackSectionsEquiv T.hom A U x) := by
  let i : (Kₜ).X ⟶ (Aₜ).X := (Over.pullback T.hom).map (Kernel.inclusion q).hom.hom
  change MultiplicativeBaseChange.pullbackSectionsEquiv T.hom A U ((g ≫ i) * x) =
    _ * MultiplicativeBaseChange.pullbackSectionsEquiv T.hom A U x
  rw [map_mul]
  exact congrArg (· * MultiplicativeBaseChange.pullbackSectionsEquiv T.hom A U x)
    ((Over.mapPullbackAdj T.hom).homEquiv_naturality_right_symm g (Kernel.inclusion q).hom.hom)

variable [IsCommMonObj A.X]

/-- The actual pulled-back kernel inherits commutativity from the original source. -/
theorem familyCoefficient_isCommMonObj : IsCommMonObj (familyCoefficient q T).X := by
  let K := Kernel.group q
  have : IsCommMonObj K.X := Kernel.isCommMonObj_group q
  let : GrpObj ((Over.pullback T.hom).obj K.X) := (Kₜ).grp
  have : IsCommMonObj (Kₜ).X := inferInstanceAs (IsCommMonObj ((Over.pullback T.hom).obj K.X))
  let : GrpObj ((Over.pullback (Bₜ).X.hom).obj (Kₜ).X) := (familyCoefficient q T).grp
  exact inferInstanceAs (IsCommMonObj ((Over.pullback (Bₜ).X.hom).obj (Kₜ).X))

attribute [local instance] familyCoefficient_isCommMonObj

variable [IsFinite q.hom.hom.left] [Etale q.hom.hom.left]

/-- The original translation action restricted to the actual family cover over its target. -/
@[no_expose]
def familyCoverAction :
    TorsorAction (familyCoefficient q T) (toUnit (familyCover q T).obj) :=
  Torsors.Restriction.relativeTorsorRestrictionOfMap (Bₜ).X Kₜ (qₜ).hom.hom (mₜ).toTorsorAction

variable [Surjective q.hom.hom.left]

/-- The original quotient remains surjective on the family cover. -/
local instance familyCoverSurjective : Surjective (familyCover q T).obj.hom :=
  BaseChange.map_surjective T.hom q inferInstance

/-- The original finite étale family cover with its original kernel action, as a sheaf torsor. -/
@[no_expose]
def familyCoverTorsor : Torsor (representedSheaf (familyCoefficient q T)) := by
  let q' := (BaseChange.groupSchemeBaseChange T.hom).functor.map q
  let : IsFinite q'.hom.hom.left := BaseChange.map_finite T.hom q inferInstance
  let : Etale q'.hom.hom.left := BaseChange.map_etale T.hom q inferInstance
  let : Surjective q'.hom.hom.left := BaseChange.map_surjective T.hom q inferInstance
  let : IsCommMonObj (BaseChange.baseChangedGroup T.hom (Kernel.group q)).X :=
    have : IsCommMonObj (Kernel.group q).X := Kernel.isCommMonObj_group q
    BaseChange.groupSchemeBaseChange_isCommMonObj T.hom _
  exact RepresentedKernel.relativeCoverTorsor (BaseChange.kernelMarking T.hom (Kernel.marking q))

open Scheme.EtaleCohomology.RepresentedKernel in
attribute [local instance] BaseChange.groupSchemeBaseChange_isCommMonObj
  Kernel.isCommMonObj_group in
/-- The original family cover uses the relative cover of the original marked map. -/
theorem familyCoverTorsor_eq :
    let q' := (BaseChange.groupSchemeBaseChange T.hom).functor.map q
    letI : IsFinite q'.hom.hom.left := BaseChange.map_finite T.hom q inferInstance
    letI : Etale q'.hom.hom.left := BaseChange.map_etale T.hom q inferInstance
    letI : Surjective q'.hom.hom.left := BaseChange.map_surjective T.hom q inferInstance
    familyCoverTorsor q T =
      relativeCoverTorsor (BaseChange.kernelMarking T.hom (Kernel.marking q)) := by
  unfold familyCoverTorsor
  rfl

open Scheme.EtaleCohomology.RepresentedKernel in
attribute [local instance] BaseChange.groupSchemeBaseChange_isCommMonObj
  Kernel.isCommMonObj_group in
/-- The original family cover class is the original extension boundary at
the target diagonal section. -/
abbrev familyCoverExtClassEq [IsCommMonObj B.X]
    [hExt : HasExt.{w} (AbelianSheaf.{u, u + 1} (Bₜ).X.left)] :=
  letI : HasExt.{w} (AbelianSheaf.{u, u + 1} (BaseChange.baseChangedGroup T.hom B).X.left) := hExt
  let q' := (BaseChange.groupSchemeBaseChange T.hom).functor.map q
  letI : IsFinite q'.hom.hom.left := BaseChange.map_finite T.hom q inferInstance
  letI : Etale q'.hom.hom.left := BaseChange.map_etale T.hom q inferInstance
  letI : Surjective q'.hom.hom.left := BaseChange.map_surjective T.hom q inferInstance
  relativeCoverExtClass_of_eq (BaseChange.kernelMarking T.hom (Kernel.marking q))
    (familyCoverTorsor q T) (familyCoverTorsor_eq q T)

variable [IsProper A.X.hom] [GeometricallyIntegral A.X.hom]
  (M : LineBundle (Bₜ).X.left)
  (a : (Modules.pullback (familyMapOfHom q.hom.hom T)).obj M.val ≅
    SheafOfModules.unit (Aₜ).X.left.ringCatSheaf)

/-- The original positive kernel character on the actual family cover's target. -/
@[no_expose]
def familyCharacter : familyCoefficient q T ⟶ MultiplicativeGroup.groupScheme (Bₜ).X.left :=
  (Over.pullback (Bₜ).X.hom).mapGrp.map
      (kernelTrivializationCharacter q (Kernel.marking q) T M a) ≫
    (MultiplicativeBaseChange.unitsBaseChangeIso (Bₜ).X.hom).hom

omit [IsCommMonObj A.X] [IsFinite q.hom.hom.left] [Etale q.hom.hom.left]
  [Surjective q.hom.hom.left] in
/-- The family character is the original kernel character pulled to the target
and followed by the canonical units comparison. -/
theorem familyCharacter_eq :
    familyCharacter q T M a =
      (Over.pullback (Bₜ).X.hom).mapGrp.map
          (kernelTrivializationCharacter q (Kernel.marking q) T M a) ≫
        (MultiplicativeBaseChange.unitsBaseChangeIso (Bₜ).X.hom).hom := (rfl)

private theorem lift_pullbackSection_left (X : FScheme k) (U : Over T.left)
    (v : U ⟶ (Over.pullback T.hom).obj X) :
    (lift (((Over.mapPullbackAdj T.hom).homEquiv U X).symm v)
      (Over.homMk U.hom : (Over.map T.hom).obj U ⟶ T)).left = v.left := by
  apply pullback.hom_ext
  · simp only [Over.lift_left, pullback.lift_fst]
    rfl
  · simp only [Over.lift_left, pullback.lift_snd]
    exact v.w.symm

omit [IsCommMonObj A.X] [IsFinite q.hom.hom.left] [Etale q.hom.hom.left]
  [Surjective q.hom.hom.left] in
private theorem familyCharacter_units (U : Over (Bₜ).X.left) (g : U ⟶ (familyCoefficient q T).X) :
    MultiplicativeGroup.sectionsUnitsEquiv (Bₜ).X.left U (g ≫ (familyCharacter q T M a).hom.hom) =
      Units.map (Torsors.Restriction.globalCoefficient (Bₜ).X Kₜ g).left.appTop.hom.toMonoidHom
        (kernelMultiplier q (Kernel.marking q) T M a) := by
  let χ := kernelTrivializationCharacter q (Kernel.marking q) T M a
  let g' := Torsors.Restriction.globalCoefficient (Bₜ).X Kₜ g
  change MultiplicativeGroup.sectionsUnitsEquiv (Bₜ).X.left U
      (g ≫ (Over.pullback (Bₜ).X.hom).map χ.hom.hom ≫
        (MultiplicativeBaseChange.unitsBaseChangeIso (Bₜ).X.hom).hom.hom.hom) = _
  rw [← Category.assoc, MultiplicativeBaseChange.unitsBaseChangeIso_sections]
  exact (congrArg (MultiplicativeGroup.sectionsUnitsEquiv T.left ((Over.map (Bₜ).X.hom).obj U))
    ((Over.mapPullbackAdj (Bₜ).X.hom).homEquiv_naturality_right_symm g χ.hom.hom)).trans
      (kernelTrivializationCharacterMap_units q (Kernel.marking q) T M a _ g')

omit [IsCommMonObj A.X] [Surjective q.hom.hom.left] in
/-- On every original étale test, the literal frame ratio on the original
family cover is the original positive kernel character evaluated there. -/
theorem familyFrameTransition (U : (Bₜ).X.left.Etale)
    (g : (Scheme.Etale.forget (Bₜ).X.left).obj U ⟶ (familyCoefficient q T).X)
    (v : (Scheme.Etale.forget (Bₜ).X.left).obj U ⟶ (familyCover q T).obj) :
    TrivializedDescent.unit (familyMapOfHom q.hom.hom T) M a U.hom v.left
        ((familyCoverAction q T).act g v).left v.w ((familyCoverAction q T).act g v).w =
      MultiplicativeGroup.sectionsUnitsEquiv (Bₜ).X.left ((Scheme.Etale.forget (Bₜ).X.left).obj U)
        (g ≫ (familyCharacter q T M a).hom.hom) := by
  let V := (Scheme.Etale.forget (Bₜ).X.left).obj U
  let W := (Over.map (Bₜ).X.hom).obj V
  let t : (Over.map T.hom).obj W ⟶ T := Over.homMk W.hom
  let w := (familyCoverAction q T).act g v
  let v' : W ⟶ (Aₜ).X := (Over.map (Bₜ).X.hom).map v ≫
    (Torsors.Restriction.canonicalTotalIso (Bₜ).X (qₜ).hom.hom).hom
  let w' : W ⟶ (Aₜ).X := (Over.map (Bₜ).X.hom).map w ≫
    (Torsors.Restriction.canonicalTotalIso (Bₜ).X (qₜ).hom.hom).hom
  let g' := Torsors.Restriction.globalCoefficient (Bₜ).X Kₜ g
  let x := MultiplicativeBaseChange.pullbackSectionsEquiv T.hom A W v'
  let z := MultiplicativeBaseChange.pullbackSectionsEquiv T.hom (Kernel.group q) W g'
  let σ := (Kernel.marking q).toTorsorAction
  have hv' : v'.left = v.left := Category.comp_id _
  have hw' : w'.left = w.left := Category.comp_id _
  have hw_act : w' = (mₜ).toTorsorAction.act g' v' := by
    apply Over.OverMorphism.ext
    exact hw'.trans (Torsors.Restriction.relativeTorsorRestrictionOfMap_point
      (Bₜ).X Kₜ (qₜ).hom.hom (mₜ).toTorsorAction g v)
  have hw_x : MultiplicativeBaseChange.pullbackSectionsEquiv T.hom A W w' = σ.act z x :=
    (congrArg (MultiplicativeBaseChange.pullbackSectionsEquiv T.hom A W) hw_act).trans
      (familyAction_transpose q T W g' v')
  have hv : (lift x t).left = v.left :=
    (lift_pullbackSection_left T A.X W v').trans hv'
  have hw : (lift (σ.act z x) t).left = w.left :=
    (congrArg (fun r => (lift r t).left) hw_x.symm).trans
      ((lift_pullbackSection_left T A.X W w').trans hw')
  have ht : (lift (x ≫ q.hom.hom) t).left = U.hom :=
    (lift_comp_familyMap q T x t).symm.trans (by rw [hv]; exact v.w)
  have hg : (lift z t).left = g'.left := lift_pullbackSection_left T (Kernel.group q).X W g'
  have htr : familyTransitionUnit q T M a x (σ.act z x) t (σ.over z x).symm =
      TrivializedDescent.unit (familyMapOfHom q.hom.hom T) M a U.hom v.left w.left v.w w.w := by
    unfold familyTransitionUnit
    exact TrivializedDescent.unit_congr _ _ _ _ _ v.w w.w ht hv hw
  rw [← htr, familyTransitionUnit_kernel_translate, hg]
  exact (familyCharacter_units q T M a V g).symm

/-- The native frame map from the original family cover is equivariant for the
original positive kernel character. -/
@[no_expose]
def familyFrameHom :
    Torsor.Hom (representedSheafMap (familyCharacter q T M a)) (familyCoverTorsor q T)
      (frameTorsor etaleLineBundleDescent (Bₜ).X.left M) :=
  frameHomOfUnit (familyCover q T) M a (familyCoefficient q T) (familyCoverAction q T)
    (familyCharacter q T M a) (familyFrameTransition q T M a)

/-- A section of the actual represented cover is the original lifted test arrow. -/
@[no_expose]
def familyCoverSection (U : (Bₜ).X.left.Etale)
    (v : (Scheme.Etale.forget (Bₜ).X.left).obj U ⟶ (familyCover q T).obj) :
    (familyCoverTorsor q T).carrier.obj.obj (op U) :=
  ULift.up v

/-- On the original cover the sheaf map is the literal restriction of the
original trivialization. -/
theorem familyFrameHom_sections (U : (Bₜ).X.left.Etale)
    (v : (Scheme.Etale.forget (Bₜ).X.left).obj U ⟶ (familyCover q T).obj) :
    frameSectionsEquiv etaleLineBundleDescent (Bₜ).X.left M (op U)
        ((familyFrameHom q T M a).map.hom.app (op U) (familyCoverSection q T U v)) =
      nativePullFrame M (familyMapOfHom q.hom.hom T) U.hom v.left v.w a :=
  frameAt_sections (familyCover q T) M a U v

/-- The actual frame torsor is the actual pushout along the original positive
character on the original family cover. -/
@[no_expose]
def familyFramePushoutIso :
    Torsor.Iso (Sheaf.torsorPushout (familyCoverTorsor q T)
      (representedSheafMap (familyCharacter q T M a)))
      (frameTorsor etaleLineBundleDescent (Bₜ).X.left M) :=
  Sheaf.pushoutComparison (familyFrameHom q T M a)

/-- The comparison sends the original pushout generator to the literal frame map. -/
theorem familyFramePushoutIso_map :
    (Sheaf.torsorPushoutMap (familyCoverTorsor q T)
      (representedSheafMap (familyCharacter q T M a))).map ≫
        (familyFramePushoutIso q T M a).carrierIso.hom = (familyFrameHom q T M a).map :=
  Sheaf.pushoutComparison_map (familyFrameHom q T M a)

/-- Inverting the literal frame map uses the inverse coefficient action. -/
@[no_expose]
def familyCoframeHom :
    Torsor.Hom (representedSheafMap (familyCharacter q T M a) ≫ (-𝟙 (gm (Bₜ).X.left)))
      (familyCoverTorsor q T) (coframeTorsor etaleLineBundleDescent (Bₜ).X.left M) :=
  coframeHomOfFrame M (familyFrameHom q T M a)

/-- On the original cover the coframe is the inverse of the same literal restricted frame. -/
theorem familyCoframeHom_sections (U : (Bₜ).X.left.Etale)
    (v : (Scheme.Etale.forget (Bₜ).X.left).obj U ⟶ (familyCover q T).obj) :
    coframeSectionsEquiv etaleLineBundleDescent (Bₜ).X.left M (op U)
        ((familyCoframeHom q T M a).map.hom.app (op U) (familyCoverSection q T U v)) =
      (nativePullFrame M (familyMapOfHom q.hom.hom T) U.hom v.left v.w a).symm := by
  change coframeSectionsEquiv etaleLineBundleDescent (Bₜ).X.left M (op U)
    ((frameInverseIso etaleLineBundleDescent (Bₜ).X.left M).hom.hom.app (op U)
      ((familyFrameHom q T M a).map.hom.app (op U) (familyCoverSection q T U v))) = _
  rw [coframeSectionsEquiv_inverse, familyFrameHom_sections]

/-- Positive coframes give the actual pushout along the inverse character. -/
@[no_expose]
def familyCoframePushoutIso :
    Torsor.Iso (Sheaf.torsorPushout (familyCoverTorsor q T)
      (representedSheafMap (familyCharacter q T M a) ≫ (-𝟙 (gm (Bₜ).X.left))))
      (coframeTorsor etaleLineBundleDescent (Bₜ).X.left M) :=
  Sheaf.pushoutComparison (familyCoframeHom q T M a)

/-- The coframe comparison preserves the literal inverse-frame map on the original cover. -/
theorem familyCoframePushoutIso_map :
    (Sheaf.torsorPushoutMap (familyCoverTorsor q T)
      (representedSheafMap (familyCharacter q T M a) ≫ (-𝟙 (gm (Bₜ).X.left)))).map ≫
        (familyCoframePushoutIso q T M a).carrierIso.hom = (familyCoframeHom q T M a).map :=
  Sheaf.pushoutComparison_map (familyCoframeHom q T M a)

end Family

end AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout
