/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionsRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.EtaleSections

/-!
# The additive small étale coefficient of a quasi-coherent module

Values are lifted global sections of the actual pullback module. Restrictions
are the original geometric unit followed by native pullback coherence. Descent
comes from the existing fpqc prestack, not from affine acyclicity. No structure
ring sheaf or scalar comparison is introduced here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- The transported restriction agrees with the actual geometric section restriction. -/
theorem sectionsPresheaf_map_eq {T U : Over X} (f : U ⟶ T)
    (s : Γ((pullback T.hom).obj F, ⊤)) :
    (sectionsPresheaf X F).map f.op s =
      Scheme.Modules.Hom.app
        ((pullbackComp f.left T.hom).hom.app F ≫
          (pullbackCongr (Over.w f)).hom.app F) ⊤
        ((((pullbackPushforwardAdjunction f.left).unit.app
          ((pullback T.hom).obj F)).app ⊤) s) := by
  change sectionsEquiv X F U ((homPresheaf X F).map f.op
    ((sectionsEquiv X F T).symm s)) = _
  rw [sectionsEquiv_map, Equiv.apply_symm_apply, nativeSectionPullback_eq_unit]

/-- Original section restrictions preserve addition. -/
theorem sectionsPresheaf_map_add {T U : Over X} (f : U ⟶ T)
    (s t : Γ((pullback T.hom).obj F, ⊤)) :
    (sectionsPresheaf X F).map f.op (s + t) =
      Add.add (α := Γ((pullback U.hom).obj F, ⊤))
        ((sectionsPresheaf X F).map f.op s) ((sectionsPresheaf X F).map f.op t) := by
  simp only [sectionsPresheaf_map_eq, map_add]
  rfl

/-- Original section restrictions preserve zero. -/
theorem sectionsPresheaf_map_zero {T U : Over X} (f : U ⟶ T) :
    (sectionsPresheaf X F).map f.op (0 : Γ((pullback T.hom).obj F, ⊤)) =
      (0 : Γ((pullback U.hom).obj F, ⊤)) := by
  simp only [sectionsPresheaf_map_eq, map_zero]

/-- Lift the supplied additive restrictions through the faithful forgetful functor. -/
abbrev liftAdditiveTransport := @CategoryTheory.PresheafTransport.liftAdditiveTransport

/-- Forgetting the additive transport retains the original lifted Type presheaf. -/
abbrev liftAdditiveTransportForgetIso :=
  @CategoryTheory.PresheafTransport.liftAdditiveTransportForgetIso

/-- Additive transport preserves descent of the original Type presheaf. -/
theorem liftAdditiveTransport_isSheaf {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type u)
    (A : C → AddCommGrpCat.{u}) (e : ∀ T, P.obj (op T) ≃ A T)
    (r : ∀ {T U}, (U ⟶ T) → (A T →+ A U))
    (hr : ∀ {T U} (f : U ⟶ T) (s : A T), r f s = e U (P.map f.op ((e T).symm s)))
    (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (liftAdditiveTransport P A e r hr) :=
  CategoryTheory.PresheafTransport.liftAdditiveTransport_isSheaf J P A e r hr hP

/-- The Type restriction retains the original Hom-transport formula. -/
theorem sectionsPresheaf_map_transport {T U : Over X} (f : U ⟶ T)
    (s : Γ((pullback T.hom).obj F, ⊤)) :
    (sectionsPresheaf X F).map f.op s = sectionsEquiv X F U
      ((homPresheaf X F).map f.op ((sectionsEquiv X F T).symm s)) := rfl

/-- The original restrictions bundled on explicit section carriers. -/
def sectionsAddHom {T U : Over X} (f : U ⟶ T) :
    Γ((pullback T.hom).obj F, ⊤) →+ Γ((pullback U.hom).obj F, ⊤) where
  toFun s := (sectionsPresheaf X F).map f.op s
  map_zero' := sectionsPresheaf_map_zero X F f
  map_add' s t := sectionsPresheaf_map_add X F f s t

/-- The bundled additive map retains its explicit original Hom-transport formula. -/
theorem sectionsAddHom_apply {T U : Over X} (f : U ⟶ T)
    (s : Γ((pullback T.hom).obj F, ⊤)) :
    sectionsAddHom X F f s = sectionsEquiv X F U
      ((homPresheaf X F).map f.op ((sectionsEquiv X F T).symm s)) :=
  sectionsPresheaf_map_transport X F f s

/-- Lifted additive sections on the over-category. -/
def additiveSectionsPresheaf : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  liftAdditiveTransport (homPresheaf X F)
    (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj F, ⊤))
    (sectionsEquiv X F) (fun f => sectionsAddHom X F f)
    (fun f s => sectionsAddHom_apply X F f s)

/-- The actual additive presheaf on the native small étale site. -/
def etaleAdditivePresheaf : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Scheme.Etale.forget X).op ⋙ additiveSectionsPresheaf X F

/-- The additive coefficient is a sheaf by native Hom descent and value lift. -/
theorem etaleAdditivePresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (etaleAdditivePresheaf X F) := by
  apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
  exact CategoryTheory.PresheafTransport.liftAdditiveTransport_isSheaf
    (Scheme.etaleTopology.over X) (homPresheaf X F)
    (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj F, ⊤))
    (sectionsEquiv X F) (fun f => sectionsAddHom X F f)
    (fun f s => sectionsAddHom_apply X F f s)
    (homPresheaf_isSheaf_etale X F)

/-- The genuine additive étale coefficient of a native quasi-coherent module. -/
def additiveCoefficient : AbelianSheaf.{u, u + 1} X :=
  ⟨etaleAdditivePresheaf X F, etaleAdditivePresheaf_isSheaf X F⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
