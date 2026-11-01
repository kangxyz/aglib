/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.HomCongr

/-!
# The original rings of affine etale tests as base algebras

The algebra structure is the preimage of the original structural spectrum
arrow. Both objects and morphisms retain the native affine test rings; no
replacement global-section ring or parallel category of tests is introduced.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

variable (A : CommRingCat.{u})

/-- The original affine-test ring, with the scalar action of its structural arrow. -/
def affineAlgebra (U : (Spec A).AffineEtale) : CommAlgCat.{u} A :=
  letI : Algebra A U.left.unop := (Spec.preimage U.hom).hom.toAlgebra
  CommAlgCat.of A U.left.unop

/-- Its spectrum structural map is the original arrow, not merely an isomorphic map. -/
theorem affineAlgebra_specMap (U : (Spec A).AffineEtale) :
    Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A U))) = U.hom :=
  Spec.map_preimage U.hom

/-- An original affine-test morphism is the same ring homomorphism, contravariantly. -/
def affineAlgebraMap {U V : (Spec A).AffineEtale} (f : U ⟶ V) :
    affineAlgebra A V ⟶ affineAlgebra A U := by
  letI : Algebra A U.left.unop := inferInstanceAs (Algebra A (affineAlgebra A U))
  letI : Algebra A V.left.unop := inferInstanceAs (Algebra A (affineAlgebra A V))
  exact CommAlgCat.ofHom ({
    toFun := fun x => f.left.unop.hom x
    map_zero' := f.left.unop.hom.map_zero
    map_one' := f.left.unop.hom.map_one
    map_add' := f.left.unop.hom.map_add
    map_mul' := f.left.unop.hom.map_mul
    commutes' a := by
      have hw := MorphismProperty.Over.w ((Scheme.AffineEtale.Spec (Spec A)).map f)
      change Spec.map f.left.unop ≫ V.hom = U.hom at hw
      have hs := congrArg Spec.preimage hw
      rw [Spec.preimage_comp, Spec.preimage_map] at hs
      exact congrArg (fun g => g.hom a) hs } :
    affineAlgebra A V →ₐ[A] affineAlgebra A U)

/-- The complete native affine-test algebra functor has the original contravariant maps. -/
def affineAlgebraFunctor : (Spec A).AffineEtale ⥤ (CommAlgCat.{u} A)ᵒᵖ where
  obj U := op (affineAlgebra A U)
  map f := (affineAlgebraMap A f).op
  map_id U := by
    apply Quiver.Hom.unop_inj
    ext a
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    ext a
    rfl

/-- The spectrum comparison is the identity on the original affine scheme,
with the structural-arrow equality supplied by full faithfulness of Spec. -/
def affineAlgebraSpecIso :
    affineAlgebraFunctor A ⋙ algSpec A ≅
      Scheme.AffineEtale.Spec (Spec A) ⋙ Scheme.Etale.forget (Spec A) :=
  NatIso.ofComponents
    (fun U => Over.isoMk (Iso.refl (Spec U.left.unop)) (by
      change 𝟙 (Spec U.left.unop) ≫ U.hom =
        Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A U)))
      rw [Category.id_comp]
      exact (affineAlgebra_specMap A U).symm))
    (by
      intro U V f
      apply Over.OverMorphism.ext
      simp only [Functor.comp_map, Over.comp_left]
      rfl)

/-- The comparison changes no underlying scheme point or scheme morphism. -/
@[simp]
theorem affineAlgebraSpecIso_hom_left (U : (Spec A).AffineEtale) :
    ((affineAlgebraSpecIso A).hom.app U).left = 𝟙 (Spec U.left.unop) := rfl

/-- Etaleness is the property of the original affine test structural map. -/
instance affineAlgebra_specMap_etale (U : (Spec A).AffineEtale) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A U)))) := by
  rw [affineAlgebra_specMap]
  exact U.prop

/-- The same structural comparison in the original etale site, lifted through
its native fully faithful forgetful functor. -/
def affineAlgebraEtaleIso (U : (Spec A).AffineEtale) :
    Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A U)))) ≅
      (Scheme.AffineEtale.Spec (Spec A)).obj U :=
  (Scheme.Etale.forget (Spec A)).preimageIso ((affineAlgebraSpecIso A).app U)

/-- The native etale arrow of the original algebra morphism. -/
def affineAlgebraEtaleMap {U V : (Spec A).AffineEtale} (f : U ⟶ V) :
    Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A U)))) ⟶
      Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A V)))) :=
  (Scheme.Etale.forget (Spec A)).preimage
    ((algSpec A).map (affineAlgebraMap A f).op)

/-- Forgetting the lifted comparison recovers the original whole over-map. -/
theorem affineAlgebraEtaleIso_forget_hom (U : (Spec A).AffineEtale) :
    (Scheme.Etale.forget (Spec A)).map (affineAlgebraEtaleIso A U).hom =
      (affineAlgebraSpecIso A).hom.app U :=
  (Scheme.Etale.forget (Spec A)).map_preimage
    (X := Scheme.Etale.mk
      (Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A U)))))
    (Y := (Scheme.AffineEtale.Spec (Spec A)).obj U) ((affineAlgebraSpecIso A).hom.app U)

/-- Forgetting the lifted arrow recovers the same original algebra spectrum map. -/
theorem affineAlgebraEtaleMap_forget {U V : (Spec A).AffineEtale} (f : U ⟶ V) :
    (Scheme.Etale.forget (Spec A)).map (affineAlgebraEtaleMap A f) =
      (algSpec A).map (affineAlgebraMap A f).op :=
  (Scheme.Etale.forget (Spec A)).map_preimage
    (X := Scheme.Etale.mk
      (Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A U)))))
    (Y := Scheme.Etale.mk
      (Spec.map (CommRingCat.ofHom (algebraMap A (affineAlgebra A V)))))
    ((algSpec A).map (affineAlgebraMap A f).op)

/-- The etale comparison preserves the whole original affine restriction square. -/
theorem affineAlgebraEtaleIso_naturality {U V : (Spec A).AffineEtale} (f : U ⟶ V) :
    affineAlgebraEtaleMap A f ≫ (affineAlgebraEtaleIso A V).hom =
      (affineAlgebraEtaleIso A U).hom ≫ (Scheme.AffineEtale.Spec (Spec A)).map f := by
  apply (Scheme.Etale.forget (Spec A)).map_injective
  rw [Functor.map_comp, Functor.map_comp, affineAlgebraEtaleMap_forget,
    affineAlgebraEtaleIso_forget_hom, affineAlgebraEtaleIso_forget_hom]
  exact (affineAlgebraSpecIso A).hom.naturality f

/-- The actual etale comparison still has the identity underlying scheme map. -/
theorem affineAlgebraEtaleIso_hom_left (U : (Spec A).AffineEtale) :
    (affineAlgebraEtaleIso A U).hom.left = 𝟙 (Spec U.left.unop) := by
  exact congrArg Over.Hom.left (affineAlgebraEtaleIso_forget_hom A U)

/-- Maps from the original affine test to an algebra spectrum are exactly
algebra homomorphisms into its original ring. -/
def affineAlgebraHomEquiv (C : CommAlgCat.{u} A) (U : (Spec A).AffineEtale) :
    (((Scheme.Etale.forget (Spec A)).obj ((Scheme.AffineEtale.Spec (Spec A)).obj U)) ⟶
      (algSpec A).obj (op C)) ≃ (C →ₐ[A] affineAlgebra A U) :=
  (Iso.homCongr ((affineAlgebraSpecIso A).app U).symm
      (Iso.refl ((algSpec A).obj (op C)))).trans
    (((algSpec.fullyFaithful (R := A)).homEquiv
      (X := op (affineAlgebra A U)) (Y := op C)).symm.trans
      ((opEquiv (op (affineAlgebra A U)) (op C)).trans
        (ConcreteCategory.homEquiv (C := CommAlgCat.{u} A)
          (X := C) (Y := affineAlgebra A U))))

/-- The represented algebra homomorphism gives the original map after the
identity-on-scheme structural comparison. -/
theorem affineAlgebraHomEquiv_specMap (C : CommAlgCat.{u} A)
    (U : (Spec A).AffineEtale)
    (g : ((Scheme.Etale.forget (Spec A)).obj
      ((Scheme.AffineEtale.Spec (Spec A)).obj U)) ⟶ (algSpec A).obj (op C)) :
    (algSpec A).map
        ((ConcreteCategory.homEquiv (C := CommAlgCat.{u} A)
          (X := C) (Y := affineAlgebra A U)).symm (affineAlgebraHomEquiv A C U g)).op =
      (affineAlgebraSpecIso A).hom.app U ≫ g := by
  change (algSpec A).map (((algSpec.fullyFaithful (R := A)).homEquiv
    (X := op (affineAlgebra A U)) (Y := op C)).symm
      ((affineAlgebraSpecIso A).hom.app U ≫ g ≫ 𝟙 _)) = _
  rw [Category.comp_id]
  exact ((algSpec.fullyFaithful (R := A)).homEquiv).apply_symm_apply _

/-- Contravariant composition is the original algebra map, not a chosen
isomorphic ring or a replacement affine test. -/
theorem affineAlgebraHomEquiv_naturality (C : CommAlgCat.{u} A)
    {U V : (Spec A).AffineEtale} (f : U ⟶ V)
    (g : ((Scheme.Etale.forget (Spec A)).obj
      ((Scheme.AffineEtale.Spec (Spec A)).obj V)) ⟶ (algSpec A).obj (op C)) :
    affineAlgebraHomEquiv A C U
        ((Scheme.Etale.forget (Spec A)).map ((Scheme.AffineEtale.Spec (Spec A)).map f) ≫ g) =
      (affineAlgebraMap A f).hom.comp (affineAlgebraHomEquiv A C V g) := by
  have h : (algSpec A).map
      ((ConcreteCategory.homEquiv (C := CommAlgCat.{u} A)
        (X := C) (Y := affineAlgebra A U)).symm (affineAlgebraHomEquiv A C U
          ((Scheme.Etale.forget (Spec A)).map
            ((Scheme.AffineEtale.Spec (Spec A)).map f) ≫ g))).op =
      (algSpec A).map ((ConcreteCategory.homEquiv (C := CommAlgCat.{u} A)
        (X := C) (Y := affineAlgebra A U)).symm
          ((affineAlgebraMap A f).hom.comp (affineAlgebraHomEquiv A C V g))).op := by
    rw [affineAlgebraHomEquiv_specMap]
    change _ = (algSpec A).map
      ((affineAlgebraMap A f).op ≫
        ((ConcreteCategory.homEquiv (C := CommAlgCat.{u} A)
          (X := C) (Y := affineAlgebra A V)).symm (affineAlgebraHomEquiv A C V g)).op)
    rw [Functor.map_comp, affineAlgebraHomEquiv_specMap]
    simpa only [Functor.comp_map, affineAlgebraFunctor, Category.assoc] using
      congrArg (fun k => k ≫ g) ((affineAlgebraSpecIso A).hom.naturality f).symm
  exact congrArg (fun k => k.unop.hom) ((algSpec A).map_injective h)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
