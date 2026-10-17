/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Open restriction of the actual relative differential sheaf

The original universal derivations and the native open restriction adjunction
identify the actual relative differential sheaves in a commuting square of
source and base open immersions. The forward and inverse formulas retain the
original d values and the original open section isomorphisms. The native
pullback comparison is obtained through the original restriction-to-pullback
isomorphism, with its actual forward arrow identified.

The base and coefficient module sheaves are arbitrary. No field, Noetherian,
smoothness, affineness, or quasicoherence premise is used; empty sources are
included. Native standard-smooth affine charts consume this comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
variable {W X Y : Scheme.{u}} (f : X ⟶ Y) (i : W ⟶ X) [IsOpenImmersion i]

/-- Original relative derivations restricted along an open immersion. -/
def restrictRelativeDerivation (M : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c) :
    PresheafOfModulesOfCommRing.Derivation (M.restrict i).val (i ≫ f).c where
  d {U} := d.d.comp (i.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul {U} a b := by
    change d.d ((i.appIso U.unop).inv (a * b)) = _
    rw [map_mul, d.d_mul]
    rfl
  d_map {U V} k a := by
    have h : (i.appIso V.unop).inv (W.presheaf.map k a) =
        X.presheaf.map (i.opensFunctor.op.map k) ((i.appIso U.unop).inv a) :=
      ConcreteCategory.congr_hom (i.appIso_inv_naturality k) a
    exact (congrArg d.d h).trans (d.d_map (i.opensFunctor.op.map k) _)
  d_app {U} a := by
    change d.d ((i.appIso (i ⁻¹ᵁ f ⁻¹ᵁ U.unop)).inv ((i ≫ f).app U.unop a)) = 0
    rw [Scheme.Hom.comp_app]
    change d.d (((i.app (f ⁻¹ᵁ U.unop) ≫
      (i.appIso (i ⁻¹ᵁ f ⁻¹ᵁ U.unop)).inv)) (f.app U.unop a)) = 0
    rw [i.app_appIso_inv]
    exact (d.d_map (homOfLE (i.image_preimage_le (f ⁻¹ᵁ U.unop))).op
      (f.app U.unop a)).trans
      ((congrArg (M.val.map (homOfLE (i.image_preimage_le (f ⁻¹ᵁ U.unop))).op)
        (d.d_app a)).trans (map_zero _))

/-- Pull a derivation back to source sections, retaining the direct-image coefficient. -/
def pushforwardRelativeDerivation (M : W.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val (i ≫ f).c) :
    PresheafOfModulesOfCommRing.Derivation ((Scheme.Modules.pushforward i).obj M).val f.c where
  d {U} := d.d.comp (i.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b :=
    (congrArg d.d ((i.app U.unop).hom.map_mul a b)).trans (d.d_mul _ _)
  d_map {U V} k a := by
    have h := ConcreteCategory.congr_hom (i.naturality k) a
    exact (congrArg d.d h).trans (d.d_map _ _)
  d_app {U} a := by
    change d.d ((f.app U.unop ≫ i.app (f ⁻¹ᵁ U.unop)) a) = 0
    rw [← Scheme.Hom.comp_app]
    exact d.d_app a


/-- The canonical inverse restriction comparison, induced by the original restricted d. -/
def relativeDifferentialRestrictInv :
    relativeDifferentialSheaf (i ≫ f) ⟶ (relativeDifferentialSheaf f).restrict i :=
  relativeDifferentialDesc (i ≫ f) _
    (restrictRelativeDerivation f i _ (relativeDifferentialDerivation f))

@[simp]
theorem relativeDifferentialRestrictInv_d (U : W.Opens) (a : Γ(W, U)) :
    (relativeDifferentialRestrictInv f i).val.app (op U)
      ((relativeDifferentialDerivation (i ≫ f)).d a) =
        (relativeDifferentialDerivation f).d ((i.appIso U).inv a) :=
  relativeDifferentialDesc_d (i ≫ f) _ _ _ a

/-- The adjoint canonical restriction comparison on the actual differential sheaf. -/
def relativeDifferentialRestrictHom :
    (relativeDifferentialSheaf f).restrict i ⟶ relativeDifferentialSheaf (i ≫ f) :=
  ((Scheme.Modules.restrictAdjunction i).homEquiv _ _).symm
    (relativeDifferentialDesc f _
      (pushforwardRelativeDerivation f i _ (relativeDifferentialDerivation (i ≫ f))))

theorem relativeDifferentialRestrictHom_d (U : W.Opens) (a : Γ(X, i ''ᵁ U)) :
    (relativeDifferentialRestrictHom f i).val.app (op U)
      ((relativeDifferentialDerivation f).d a) =
        (relativeDifferentialDerivation (i ≫ f)).d ((i.appIso U).hom a) := by
  unfold relativeDifferentialRestrictHom
  rw [Adjunction.homEquiv_counit]
  change (relativeDifferentialSheaf (i ≫ f)).val.map
    (eqToHom (i.preimage_image_eq U).symm).op
    ((relativeDifferentialDesc f _
      (pushforwardRelativeDerivation f i _ (relativeDifferentialDerivation (i ≫ f)))).val.app
        (op (i ''ᵁ U)) ((relativeDifferentialDerivation f).d a)) = _
  rw [relativeDifferentialDesc_d]
  change (relativeDifferentialSheaf (i ≫ f)).val.map
    (eqToHom (i.preimage_image_eq U).symm).op
    ((relativeDifferentialDerivation (i ≫ f)).d (i.app (i ''ᵁ U) a)) = _
  exact ((relativeDifferentialDerivation (i ≫ f)).d_map
    (eqToHom (i.preimage_image_eq U).symm).op (i.app (i ''ᵁ U) a)).symm.trans
      (congrArg (relativeDifferentialDerivation (i ≫ f)).d
        (ConcreteCategory.congr_hom (i.appIso_hom U) a).symm)

/-- Canonical coercion form of `relativeDifferentialRestrictHom_d`
for simplification. -/
@[simp]
private theorem relativeDifferentialRestrictHom_d' (U : W.Opens) (a : Γ(X, i ''ᵁ U)) :
    DFunLike.coe (F := _ →ₗ[Γ(W, U)] _)
      ((relativeDifferentialRestrictHom f i).val.app' (op U)).hom
      ((relativeDifferentialDerivation f).d a) =
        (relativeDifferentialDerivation (i ≫ f)).d ((i.appIso U).hom a) := by
  exact relativeDifferentialRestrictHom_d f i U a


/-- The actual relative differential sheaf commutes with source-open restriction. -/
def relativeDifferentialRestrictIso :
    (relativeDifferentialSheaf f).restrict i ≅ relativeDifferentialSheaf (i ≫ f) where
  hom := relativeDifferentialRestrictHom f i
  inv := relativeDifferentialRestrictInv f i
  hom_inv_id := by
    apply ((Scheme.Modules.restrictAdjunction i).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    have hAdj : (Scheme.Modules.restrictAdjunction i).homEquiv _ _
        (relativeDifferentialRestrictHom f i) = relativeDifferentialDesc f _
          (pushforwardRelativeDerivation f i _ (relativeDifferentialDerivation (i ≫ f))) :=
      Equiv.apply_symm_apply _ _
    rw [hAdj, Adjunction.homEquiv_unit]
    apply relativeDifferentialSheaf_hom_ext f _
    intro U a
    change (relativeDifferentialRestrictInv f i).val.app (op (i ⁻¹ᵁ U.unop))
      ((relativeDifferentialDesc f _
        (pushforwardRelativeDerivation f i _ (relativeDifferentialDerivation (i ≫ f)))).val.app
          U ((relativeDifferentialDerivation f).d a)) =
        (relativeDifferentialSheaf f).val.map
          (homOfLE (i.image_preimage_le U.unop)).op
          ((relativeDifferentialDerivation f).d a)
    rw [relativeDifferentialDesc_d]
    change (relativeDifferentialRestrictInv f i).val.app (op (i ⁻¹ᵁ U.unop))
      ((relativeDifferentialDerivation (i ≫ f)).d (i.app U.unop a)) = _
    rw [relativeDifferentialRestrictInv_d]
    have h : (i.appIso (i ⁻¹ᵁ U.unop)).inv (i.app U.unop a) =
        X.presheaf.map (homOfLE (i.image_preimage_le U.unop)).op a :=
      ConcreteCategory.congr_hom (i.app_appIso_inv U.unop) a
    exact (congrArg (relativeDifferentialDerivation f).d h).trans
      ((relativeDifferentialDerivation f).d_map _ a)
  inv_hom_id := by
    apply relativeDifferentialSheaf_hom_ext (i ≫ f) _
    intro U a
    change (relativeDifferentialRestrictHom f i).val.app U
      ((relativeDifferentialRestrictInv f i).val.app U
        ((relativeDifferentialDerivation (i ≫ f)).d a)) = _
    rw [relativeDifferentialRestrictInv_d]
    exact (relativeDifferentialRestrictHom_d f i U.unop _).trans
      (congrArg (relativeDifferentialDerivation (i ≫ f)).d
        (Iso.inv_hom_id_apply (i.appIso U.unop) a))


section BaseOpen

variable {Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]

/-- A relative derivation also kills sections from any further base. -/
def composeBaseRelativeDerivation (M : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c) :
    PresheafOfModulesOfCommRing.Derivation M.val (f ≫ j).c where
  d := d.d
  d_mul := d.d_mul
  d_map := d.d_map
  d_app {U} a := by
    change d.d ((f ≫ j).app U.unop a) = 0
    rw [Scheme.Hom.comp_app]
    exact d.d_app (j.app U.unop a)

/-- An open immersion of bases adds no relative vanishing condition. -/
def removeBaseOpenRelativeDerivation (M : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val (f ≫ j).c) :
    PresheafOfModulesOfCommRing.Derivation M.val f.c where
  d := d.d
  d_mul := d.d_mul
  d_map := d.d_map
  d_app {U} a := by
    let k : U.unop ⟶ j ⁻¹ᵁ (j ''ᵁ U.unop) :=
      eqToHom (j.preimage_image_eq U.unop).symm
    have h : f.app U.unop a =
        X.presheaf.map ((Opens.map f.base).map k).op
          ((f ≫ j).app (j ''ᵁ U.unop) ((j.appIso U.unop).inv a)) := by
      calc
        f.app U.unop a =
            f.app U.unop ((j.appIso U.unop).hom ((j.appIso U.unop).inv a)) := by
          rw [Iso.inv_hom_id_apply]
        _ = f.app U.unop (Y.presheaf.map k.op
            (j.app (j ''ᵁ U.unop) ((j.appIso U.unop).inv a))) := by
          rw [Scheme.Hom.appIso_hom]
          rfl
        _ = X.presheaf.map ((Opens.map f.base).map k).op
            (f.app (j ⁻¹ᵁ (j ''ᵁ U.unop))
              (j.app (j ''ᵁ U.unop) ((j.appIso U.unop).inv a))) :=
          ConcreteCategory.congr_hom (f.naturality k.op) _
        _ = _ := by rw [Scheme.Hom.comp_app]; rfl
    exact (congrArg d.d h).trans
      ((d.d_map ((Opens.map f.base).map k).op _).trans
        ((congrArg (M.val.map ((Opens.map f.base).map k).op)
          (d.d_app ((j.appIso U.unop).inv a))).trans (map_zero _)))

/-- The actual differential sheaf is unchanged by an open immersion of the base. -/
def relativeDifferentialBaseOpenIso :
    relativeDifferentialSheaf (f ≫ j) ≅ relativeDifferentialSheaf f where
  hom := relativeDifferentialDesc (f ≫ j) _
    (composeBaseRelativeDerivation f j _ (relativeDifferentialDerivation f))
  inv := relativeDifferentialDesc f _
    (removeBaseOpenRelativeDerivation f j _ (relativeDifferentialDerivation (f ≫ j)))
  hom_inv_id := by
    apply relativeDifferentialSheaf_hom_ext (f ≫ j) _
    intro U a
    change (relativeDifferentialDesc f _ _).val.app U
      ((relativeDifferentialDesc (f ≫ j) _ _).val.app U
        ((relativeDifferentialDerivation (f ≫ j)).d a)) = _
    rw [relativeDifferentialDesc_d]
    exact relativeDifferentialDesc_d f _ _ U a
  inv_hom_id := by
    apply relativeDifferentialSheaf_hom_ext f _
    intro U a
    change (relativeDifferentialDesc (f ≫ j) _ _).val.app U
      ((relativeDifferentialDesc f _ _).val.app U
        ((relativeDifferentialDerivation f).d a)) = _
    rw [relativeDifferentialDesc_d]
    exact relativeDifferentialDesc_d (f ≫ j) _ _ U a

end BaseOpen


/-- The restriction comparison sends original differentials through the open section map. -/
theorem relativeDifferentialRestrictIso_hom_d (U : W.Opens) (a : Γ(X, i ''ᵁ U)) :
    (relativeDifferentialRestrictIso f i).hom.val.app (op U)
      ((relativeDifferentialDerivation f).d a) =
        (relativeDifferentialDerivation (i ≫ f)).d ((i.appIso U).hom a) :=
  relativeDifferentialRestrictHom_d f i U a

/-- Its inverse uses precisely the inverse original open section map. -/
theorem relativeDifferentialRestrictIso_inv_d (U : W.Opens) (a : Γ(W, U)) :
    (relativeDifferentialRestrictIso f i).inv.val.app (op U)
      ((relativeDifferentialDerivation (i ≫ f)).d a) =
        (relativeDifferentialDerivation f).d ((i.appIso U).inv a) :=
  relativeDifferentialRestrictInv_d f i U a

section BaseOpenFormulas
variable {Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]

/-- The open-base comparison keeps every original differential unchanged. -/
theorem relativeDifferentialBaseOpenIso_hom_d (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialBaseOpenIso f j).hom.val.app U
      ((relativeDifferentialDerivation (f ≫ j)).d a) =
        (relativeDifferentialDerivation f).d a :=
  relativeDifferentialDesc_d (f ≫ j) _ _ U a

/-- The inverse open-base comparison keeps the same differential unchanged. -/
theorem relativeDifferentialBaseOpenIso_inv_d (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialBaseOpenIso f j).inv.val.app U
      ((relativeDifferentialDerivation f).d a) =
        (relativeDifferentialDerivation (f ≫ j)).d a :=
  relativeDifferentialDesc_d f _ _ U a

end BaseOpenFormulas

/-- Change an equal structural map only in the vanishing proof, retaining the d values. -/
def congrRelativeDerivation {g : X ⟶ Y} (h : f = g) (M : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c) :
    PresheafOfModulesOfCommRing.Derivation M.val g.c where
  d := d.d
  d_mul := d.d_mul
  d_map := d.d_map
  d_app {U} a := by
    cases h
    exact d.d_app a

/-- Equality of structural maps identifies their actual universal differential sheaves. -/
def relativeDifferentialCongrIso {g : X ⟶ Y} (h : f = g) :
    relativeDifferentialSheaf f ≅ relativeDifferentialSheaf g where
  hom := relativeDifferentialDesc f _
    (congrRelativeDerivation g h.symm _ (relativeDifferentialDerivation g))
  inv := relativeDifferentialDesc g _
    (congrRelativeDerivation f h _ (relativeDifferentialDerivation f))
  hom_inv_id := by
    apply relativeDifferentialSheaf_hom_ext f _
    intro U a
    change (relativeDifferentialDesc g _ _).val.app U
      ((relativeDifferentialDesc f _ _).val.app U
        ((relativeDifferentialDerivation f).d a)) = _
    rw [relativeDifferentialDesc_d]
    exact relativeDifferentialDesc_d g _ _ U a
  inv_hom_id := by
    apply relativeDifferentialSheaf_hom_ext g _
    intro U a
    change (relativeDifferentialDesc f _ _).val.app U
      ((relativeDifferentialDesc g _ _).val.app U
        ((relativeDifferentialDerivation g).d a)) = _
    rw [relativeDifferentialDesc_d]
    exact relativeDifferentialDesc_d f _ _ U a

/-- Structural-map congruence preserves the original universal differential. -/
theorem relativeDifferentialCongrIso_hom_d {g : X ⟶ Y} (h : f = g)
    (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialCongrIso f h).hom.val.app U
      ((relativeDifferentialDerivation f).d a) =
        (relativeDifferentialDerivation g).d a :=
  relativeDifferentialDesc_d f _ _ U a

/-- The inverse congruence preserves that same original differential. -/
theorem relativeDifferentialCongrIso_inv_d {g : X ⟶ Y} (h : f = g)
    (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialCongrIso f h).inv.val.app U
      ((relativeDifferentialDerivation g).d a) =
        (relativeDifferentialDerivation f).d a :=
  relativeDifferentialDesc_d g _ _ U a

section OpenSquare
variable {Z : Scheme.{u}} (g : W ⟶ Z) (j : Z ⟶ Y) [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j)

/-- The actual relative differential sheaf on a commuting square of source and base opens. -/
def relativeDifferentialOpenSquareIso :
    (relativeDifferentialSheaf f).restrict i ≅ relativeDifferentialSheaf g :=
  relativeDifferentialRestrictIso f i ≪≫ relativeDifferentialCongrIso (i ≫ f) h ≪≫
    relativeDifferentialBaseOpenIso g j

/-- The forward open-square comparison has exactly the original differential formula. -/
theorem relativeDifferentialOpenSquareIso_hom_d (U : W.Opens) (a : Γ(X, i ''ᵁ U)) :
    (relativeDifferentialOpenSquareIso f i g j h).hom.val.app (op U)
      ((relativeDifferentialDerivation f).d a) =
        (relativeDifferentialDerivation g).d ((i.appIso U).hom a) :=
  (congrArg (fun z => (relativeDifferentialBaseOpenIso g j).hom.val.app (op U)
    ((relativeDifferentialCongrIso (i ≫ f) h).hom.val.app (op U) z))
    (relativeDifferentialRestrictIso_hom_d f i U a)).trans
    ((congrArg ((relativeDifferentialBaseOpenIso g j).hom.val.app (op U))
      (relativeDifferentialCongrIso_hom_d (i ≫ f) h (op U) ((i.appIso U).hom a))).trans
        (relativeDifferentialBaseOpenIso_hom_d g j (op U) ((i.appIso U).hom a)))

/-- The inverse open-square comparison has the inverse original differential formula. -/
theorem relativeDifferentialOpenSquareIso_inv_d (U : W.Opens) (a : Γ(W, U)) :
    (relativeDifferentialOpenSquareIso f i g j h).inv.val.app (op U)
      ((relativeDifferentialDerivation g).d a) =
        (relativeDifferentialDerivation f).d ((i.appIso U).inv a) :=
  (congrArg (fun z => (relativeDifferentialRestrictIso f i).inv.val.app (op U)
    ((relativeDifferentialCongrIso (i ≫ f) h).inv.val.app (op U) z))
    (relativeDifferentialBaseOpenIso_inv_d g j (op U) a)).trans
    ((congrArg ((relativeDifferentialRestrictIso f i).inv.val.app (op U))
      (relativeDifferentialCongrIso_inv_d (i ≫ f) h (op U) a)).trans
        (relativeDifferentialRestrictIso_inv_d f i U a))

/-- The same comparison for the actual native pullback of structure-module sheaves. -/
def relativeDifferentialPullbackOpenSquareIso :
    (Scheme.Modules.pullback i).obj (relativeDifferentialSheaf f) ≅
      relativeDifferentialSheaf g :=
  ((Scheme.Modules.restrictFunctorIsoPullback i).app (relativeDifferentialSheaf f)).symm ≪≫
    relativeDifferentialOpenSquareIso f i g j h

/-- Native restriction-to-pullback transport recovers the same original comparison map. -/
@[reassoc]
theorem relativeDifferentialPullbackOpenSquareIso_hom_restrict :
    (Scheme.Modules.restrictFunctorIsoPullback i).hom.app (relativeDifferentialSheaf f) ≫
      (relativeDifferentialPullbackOpenSquareIso f i g j h).hom =
        (relativeDifferentialOpenSquareIso f i g j h).hom := by
  simp [relativeDifferentialPullbackOpenSquareIso]

end OpenSquare

end AlgebraicGeometry.Scheme.Modules.Differentials
