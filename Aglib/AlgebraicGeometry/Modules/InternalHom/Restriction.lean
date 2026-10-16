/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.InternalHom

/-!
# Original Hom-sheaf sections under actual open restriction

Morphisms between actual restrictions along an open immersion identify with sections of the
original structure-linear Hom sheaf on its original range. The construction uses the native
image/preimage section isomorphisms and retains the original component maps and scalar actions.
Further actual open restriction is exactly the original Hom-sheaf restriction, with the native
composition comparison isomorphisms retained. Both module sheaves are arbitrary.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.InternalHom
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Image after inverse image is the original open when it lies in the original range. -/
theorem restrictionImagePreimage (V : X.Opens) (hV : V ≤ j.opensRange) :
    j ''ᵁ (j ⁻¹ᵁ V) = V :=
  (j.image_preimage_eq_opensRange_inf V).trans (inf_eq_right.mpr hV)

/-- Original restriction sections over the inverse image identify with the original sections
on an open contained in the range. -/
def rangeRestrictionSectionIso (M : X.Modules) (V : X.Opens) (hV : V ≤ j.opensRange) :
    Γ(M.restrict j, j ⁻¹ᵁ V) ≅ Γ(M, V) :=
  M.restrictAppIso j (j ⁻¹ᵁ V) ≪≫
    M.presheaf.mapIso (eqToIso (restrictionImagePreimage j V hV).symm).op

/-- An actual restricted arrow respects the original scalar action on its image open. -/
theorem restrictionHom_original_smul {M N : X.Modules}
    (f : M.restrict j ⟶ N.restrict j) (V : U.Opens)
    (r : Γ(X, j ''ᵁ V)) (m : Γ(M, j ''ᵁ V)) :
    f.val.app (op V) (r • m) = r • (show Γ(N, j ''ᵁ V) from f.val.app (op V) m) := by
  let m' : Γ(M.restrict j, V) := m
  have h := (f.val.app (op V)).hom.map_smul ((j.appIso V).hom r) m'
  change f.val.app (op V) (((j.appIso V).inv ((j.appIso V).hom r)) • m) =
    ((j.appIso V).inv ((j.appIso V).hom r)) •
      (show Γ(N, j ''ᵁ V) from f.val.app (op V) m) at h
  exact (congrArg (fun a : Γ(X, j ''ᵁ V) => f.val.app (op V) (a • m))
    (Iso.hom_inv_id_apply (j.appIso V) r)).symm.trans
      (h.trans (congrArg (fun a : Γ(X, j ''ᵁ V) =>
        a • (show Γ(N, j ''ᵁ V) from f.val.app (op V) m))
          (Iso.hom_inv_id_apply (j.appIso V) r)))

/-- A genuine morphism over the original range induces the actual open-restriction morphism. -/
def rangeHomToRestriction {M N : X.Modules}
    (a : M.over j.opensRange ⟶ N.over j.opensRange) : M.restrict j ⟶ N.restrict j := by
  let A := (_root_.PresheafOfModules.toPresheaf (X.ringCatSheaf.over j.opensRange).obj).map a.val
  refine ⟨_root_.PresheafOfModules.homMk {
    app V := A.app (op (Over.mk (homOfLE (j.image_le_opensRange V.unop))))
    naturality {V W} k := by
      let q : Over.mk (homOfLE (j.image_le_opensRange W.unop)) ⟶
          Over.mk (homOfLE (j.image_le_opensRange V.unop)) :=
        Over.homMk (homOfLE (j.image_mono k.unop.le))
      exact A.naturality q.op } ?_⟩
  intro V r m
  change a.val.app (op (Over.mk (homOfLE (j.image_le_opensRange V.unop))))
    (((j.appIso V.unop).inv r) • (show Γ(M, j ''ᵁ V.unop) from m)) =
      ((j.appIso V.unop).inv r) •
        (show Γ(N, j ''ᵁ V.unop) from
          a.val.app (op (Over.mk (homOfLE (j.image_le_opensRange V.unop)))) m)
  exact (a.val.app _).hom.map_smul _ _

/-- The original image-open component is unchanged under range-to-restriction transport. -/
theorem rangeHomToRestriction_app {M N : X.Modules}
    (a : M.over j.opensRange ⟶ N.over j.opensRange) (V : U.Opens) (m : Γ(M, j ''ᵁ V)) :
    (rangeHomToRestriction j a).val.app (op V) m =
      a.val.app (op (Over.mk (homOfLE (j.image_le_opensRange V)))) m := rfl

/-- Original inverse image on the opens contained in the original range. -/
def rangePreimageFunctor : Over j.opensRange ⥤ U.Opens :=
  Over.forget j.opensRange ⋙ TopologicalSpace.Opens.map j.base

/-- The original range-section identifications retain the original restriction maps. -/
theorem rangeRestrictionSectionIso_hom_naturality (M : X.Modules)
    {V W : X.Opens} (h : V ≤ W) (hW : W ≤ j.opensRange) :
    (M.restrict j).presheaf.map ((TopologicalSpace.Opens.map j.base).map (homOfLE h)).op ≫
        (rangeRestrictionSectionIso j M V (h.trans hW)).hom =
      (rangeRestrictionSectionIso j M W hW).hom ≫ M.presheaf.map (homOfLE h).op := by
  change M.presheaf.map _ ≫ M.presheaf.map _ = M.presheaf.map _ ≫ M.presheaf.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Original range sections form the original comparison of abelian presheaves. -/
def rangeRestrictionSectionsNatIso (M : X.Modules) :
    (rangePreimageFunctor j).op ⋙ (M.restrict j).presheaf ≅
      (M.over j.opensRange).val.presheaf :=
  NatIso.ofComponents
    (fun W => rangeRestrictionSectionIso j M W.unop.left W.unop.hom.le)
    (fun k => rangeRestrictionSectionIso_hom_naturality j M k.unop.left.le _)

/-- An actual restricted arrow gives a genuine morphism over its original open range. -/
def restrictionHomToRange {M N : X.Modules} (f : M.restrict j ⟶ N.restrict j) :
    M.over j.opensRange ⟶ N.over j.opensRange := by
  let A := (rangeRestrictionSectionsNatIso j M).inv ≫
    Functor.whiskerLeft (rangePreimageFunctor j).op f.mapPresheaf ≫
      (rangeRestrictionSectionsNatIso j N).hom
  refine ⟨_root_.PresheafOfModules.homMk A ?_⟩
  intro W r m
  let V := W.unop.left
  let hV := W.unop.hom.le
  let r₀ : Γ(X, V) := r
  let m₀ : Γ(M, V) := m
  let h := restrictionImagePreimage j V hV
  let r' : Γ(X, j ''ᵁ (j ⁻¹ᵁ V)) := X.presheaf.map (eqToHom h).op r₀
  let m' : Γ(M, j ''ᵁ (j ⁻¹ᵁ V)) := M.presheaf.map (eqToHom h).op m₀
  let n' : Γ(N, j ''ᵁ (j ⁻¹ᵁ V)) := f.val.app (op (j ⁻¹ᵁ V)) m'
  have hm := M.val.map_smul (eqToHom h).op r₀ m₀
  have hf := restrictionHom_original_smul j f (j ⁻¹ᵁ V) r' m'
  have hn := N.val.map_smul (eqToHom h.symm).op r' n'
  have hr : X.presheaf.map (eqToHom h.symm).op r' = r₀ :=
    Iso.inv_hom_id_apply (X.presheaf.mapIso (eqToIso h.symm).op) r₀
  change N.presheaf.map (eqToHom h.symm).op
    (f.val.app (op (j ⁻¹ᵁ V)) (M.val.map (eqToHom h).op (r₀ • m₀))) =
      r₀ • N.presheaf.map (eqToHom h.symm).op n'
  exact (congrArg (fun z => N.presheaf.map (eqToHom h.symm).op
    (f.val.app (op (j ⁻¹ᵁ V)) z)) hm).trans
      ((congrArg (N.presheaf.map (eqToHom h.symm).op) hf).trans
        (hn.trans (congrArg (fun a : Γ(X, V) =>
          a • (show Γ(N, V) from N.presheaf.map (eqToHom h.symm).op n')) hr)))

/-- The actual restricted morphism is recovered after original range transport. -/
theorem rangeHomToRestriction_toRange {M N : X.Modules}
    (f : M.restrict j ⟶ N.restrict j) :
    rangeHomToRestriction j (restrictionHomToRange j f) = f := by
  ext V m
  let T := j ⁻¹ᵁ (j ''ᵁ V)
  let aM := rangeRestrictionSectionIso j M (j ''ᵁ V) (j.image_le_opensRange V)
  let aN := rangeRestrictionSectionIso j N (j ''ᵁ V) (j.image_le_opensRange V)
  change aN.hom (f.val.app (op T) (aM.inv m)) = f.val.app (op V) m
  have hn := _root_.PresheafOfModules.naturality_apply f.val
    (eqToHom (j.preimage_image_eq V).symm).op (aM.inv m)
  change f.val.app (op V) (aM.hom (aM.inv m)) =
    aN.hom (f.val.app (op T) (aM.inv m)) at hn
  exact hn.symm.trans (congrArg (f.val.app (op V)) (Iso.inv_hom_id_apply aM m))

/-- The actual range morphism is recovered after original open restriction. -/
theorem restrictionHomToRange_fromRange {M N : X.Modules}
    (a : M.over j.opensRange ⟶ N.over j.opensRange) :
    restrictionHomToRange j (rangeHomToRestriction j a) = a := by
  ext W m
  let V := W.unop.left
  let hV := W.unop.hom.le
  let h := restrictionImagePreimage j V hV
  let aM := rangeRestrictionSectionIso j M V hV
  let aN := rangeRestrictionSectionIso j N V hV
  let T := Over.mk (homOfLE (j.image_le_opensRange (j ⁻¹ᵁ V)))
  let k : T ⟶ W.unop := Over.homMk (eqToHom h)
  change aN.hom (a.val.app (op T) (aM.inv m)) = a.val.app W m
  have hn := _root_.PresheafOfModules.naturality_apply a.val k.op m
  change a.val.app (op T) (aM.inv m) = aN.inv (a.val.app W m) at hn
  exact (congrArg aN.hom hn).trans (Iso.inv_hom_id_apply aN (a.val.app W m))

/-- Actual restricted morphisms identify with actual morphisms on the original range. -/
def rangeRestrictionHomEquiv (M N : X.Modules) :
    (M.restrict j ⟶ N.restrict j) ≃ (M.over j.opensRange ⟶ N.over j.opensRange) where
  toFun := restrictionHomToRange j
  invFun := rangeHomToRestriction j
  left_inv := rangeHomToRestriction_toRange j
  right_inv := restrictionHomToRange_fromRange j

/-- Actual open-restriction morphisms are sections of the original structure-linear Hom sheaf
on the original open range. -/
def restrictionHomEquiv (M N : X.Modules) :
    (M.restrict j ⟶ N.restrict j) ≃ Γ(sheaf X M N, j.opensRange) :=
  rangeRestrictionHomEquiv j M N |>.trans (sectionHomEquiv X M N j.opensRange).symm

/-- The inverse Hom-section comparison retains the original component on every image open. -/
theorem restrictionHomEquiv_symm_app (M N : X.Modules)
    (s : Γ(sheaf X M N, j.opensRange)) (V : U.Opens) (m : Γ(M, j ''ᵁ V)) :
    ((restrictionHomEquiv j M N).symm s).val.app (op V) m =
      (sectionHomEquiv X M N j.opensRange s).val.app
        (op (Over.mk (homOfLE (j.image_le_opensRange V)))) m := rfl

/-- The Hom-sheaf section has exactly the original restricted morphism component. -/
theorem restrictionHomEquiv_app (M N : X.Modules)
    (f : M.restrict j ⟶ N.restrict j) (V : U.Opens) (m : Γ(M, j ''ᵁ V)) :
    (sectionHomEquiv X M N j.opensRange (restrictionHomEquiv j M N f)).val.app
      (op (Over.mk (homOfLE (j.image_le_opensRange V)))) m = f.val.app (op V) m := by
  exact congrArg (fun k => k.val.app (op V) m)
    ((restrictionHomEquiv j M N).symm_apply_apply f)

/-- Actual further open restriction, with the native composition comparisons retained. -/
def restrictionHomMap {V : Scheme.{u}} (k : V ⟶ U) [IsOpenImmersion k]
    {M N : X.Modules} (f : M.restrict j ⟶ N.restrict j) :
    M.restrict (k ≫ j) ⟶ N.restrict (k ≫ j) :=
  (Scheme.Modules.restrictFunctorComp k j).hom.app M ≫
    (Scheme.Modules.restrictFunctor k).map f ≫
      (Scheme.Modules.restrictFunctorComp k j).inv.app N

/-- The original range of a further open restriction lies in the original range. -/
theorem restrictionRange_le {V : Scheme.{u}} (k : V ⟶ U) [IsOpenImmersion k] :
    (k ≫ j).opensRange ≤ j.opensRange :=
  (Scheme.Hom.opensRange_comp k j).le.trans (j.image_le_opensRange k.opensRange)

/-- Restricting the original Hom-sheaf section is exactly further actual open restriction. -/
theorem restrictionHomEquiv_restrict {V : Scheme.{u}} (k : V ⟶ U) [IsOpenImmersion k]
    (M N : X.Modules) (f : M.restrict j ⟶ N.restrict j) :
    (sheaf X M N).val.map (homOfLE (restrictionRange_le j k)).op
        (restrictionHomEquiv j M N f) =
      restrictionHomEquiv (k ≫ j) M N (restrictionHomMap j k f) := by
  apply (restrictionHomEquiv (k ≫ j) M N).symm.injective
  simp only [Equiv.symm_apply_apply]
  ext W m
  let h := Scheme.Hom.comp_image k j W
  let a := restrictionHomToRange j f
  let A := Over.mk (homOfLE (((k ≫ j).image_le_opensRange W).trans (restrictionRange_le j k)))
  let B := Over.mk (homOfLE (j.image_le_opensRange (k ''ᵁ W)))
  let q : A ⟶ B := Over.homMk (eqToHom h)
  let x : Γ(M, j ''ᵁ (k ''ᵁ W)) := M.presheaf.map (eqToHom h.symm).op m
  change a.val.app (op A) m =
    N.presheaf.map (eqToHom h).op (f.val.app (op (k ''ᵁ W)) x)
  have hn := _root_.PresheafOfModules.naturality_apply a.val q.op x
  have hm : M.presheaf.map (eqToHom h).op x = m :=
    Iso.inv_hom_id_apply (M.presheaf.mapIso (eqToIso h).op) m
  have ha : a.val.app (op B) x = f.val.app (op (k ''ᵁ W)) x :=
    restrictionHomEquiv_app j M N f (k ''ᵁ W) x
  exact ((congrArg (a.val.app (op A)) hm).symm.trans hn).trans
    (congrArg (N.presheaf.map (eqToHom h).op) ha)

end AlgebraicGeometry.Scheme.Modules.InternalHom
