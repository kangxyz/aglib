/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Native Hopf Spec under scalar extension

The group isomorphism packages the existing group-compatible native
`pullbackSymmetry` and `pullbackSpecIso'`. Its underlying maps and projections
are the original maps. No alternate base-changed group or Hopf/Spec model is
introduced, and the two base rings are arbitrary commutative rings.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry Scheme
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

private theorem scalarExtension_inv_fst (k R S : Type u)
    [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] :
    (pullbackSymmetry (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of k))
        (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≪≫
      pullbackSpecIso' k R S).inv ≫
        pullback.fst (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S).toRingHom) := by
  rw [Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_fst]
  exact pullbackSpecIso_inv_snd k R S

private theorem scalarExtension_inv_snd (k R S : Type u)
    [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] :
    (pullbackSymmetry (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of k))
        (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≪≫
      pullbackSpecIso' k R S).inv ≫
        pullback.snd (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] S))) := by
  rw [Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_snd]
  exact pullbackSpecIso_inv_fst' k R S

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  (A : CommHopfAlgCat.{u} k)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original native Hopf Spec comparison under scalar extension, as a group isomorphism. -/
def hopfSpecScalarExtensionIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp.obj
        ((hopfSpec (CommRingCat.of k)).obj (op A)) ≅
      (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R (R ⊗[k] A))) := by
  let e := pullbackSymmetry
      (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
      (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≪≫ pullbackSpecIso' k R A
  have he : IsMonHom (e.hom.asOver (Spec (CommRingCat.of R))) := by
    dsimp only [e]
    infer_instance
  letI : IsMonHom (e.asOver (Spec (CommRingCat.of R))).hom := he
  exact Grp.mkIso' (e.asOver (Spec (CommRingCat.of R)))

/-- The forward group comparison keeps the original scheme arrow. -/
theorem hopfSpecScalarExtensionIso_hom_left :
    (hopfSpecScalarExtensionIso k R A).hom.hom.hom.left =
      (pullbackSymmetry
        (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
        (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≪≫
          pullbackSpecIso' k R A).hom := rfl

/-- The inverse group comparison keeps the original inverse scheme arrow. -/
theorem hopfSpecScalarExtensionIso_inv_left :
    (hopfSpecScalarExtensionIso k R A).inv.hom.hom.left =
      (pullbackSymmetry
        (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
        (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≪≫
          pullbackSpecIso' k R A).inv := rfl

/-- The original inverse comparison followed by the group-coordinate projection. -/
theorem hopfSpecScalarExtensionIso_inv_fst :
    (hopfSpecScalarExtensionIso k R A).inv.hom.hom.left ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A).toRingHom) :=
  scalarExtension_inv_fst k R A

/-- The original inverse comparison followed by the coefficient-base projection. -/
theorem hopfSpecScalarExtensionIso_inv_snd :
    (hopfSpecScalarExtensionIso k R A).inv.hom.hom.left ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] A))) :=
  scalarExtension_inv_snd k R A

/-- The original group isomorphism preserves the actual identity section. -/
theorem hopfSpecScalarExtensionIso_one :
    η ≫ (hopfSpecScalarExtensionIso k R A).hom.hom.hom = η :=
  IsMonHom.one_hom _

/-- The original group isomorphism preserves the actual multiplication morphism. -/
theorem hopfSpecScalarExtensionIso_mul :
    μ ≫ (hopfSpecScalarExtensionIso k R A).hom.hom.hom =
      ((hopfSpecScalarExtensionIso k R A).hom.hom.hom ⊗ₘ
        (hopfSpecScalarExtensionIso k R A).hom.hom.hom) ≫ μ :=
  IsMonHom.mul_hom _

/-- Scalar extension on native commutative Hopf algebras uses the original tensor maps. -/
def hopfScalarExtension : CommHopfAlgCat.{u} k ⥤ CommHopfAlgCat.{u} R where
  obj B := CommHopfAlgCat.of R (R ⊗[k] B)
  map f := CommHopfAlgCat.ofHom
    (Bialgebra.TensorProduct.map (BialgHom.id R R) f.hom)
  map_id B := by
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.coe_toAlgHom_injective
    ext b
    rfl
  map_comp f g := by
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.coe_toAlgHom_injective
    ext b
    rfl

/-- The native scalar-extension map is the literal tensor map on each pure tensor. -/
@[simp]
theorem hopfScalarExtension_map_tmul {B C : CommHopfAlgCat.{u} k}
    (f : B ⟶ C) (r : R) (b : B) :
    (hopfScalarExtension k R).map f (r ⊗ₜ[k] b) = r ⊗ₜ[k] f.hom b := rfl

/-- Naturality of the inverse comparison on the actual Hopf algebra maps. -/
theorem hopfSpecScalarExtensionIso_inv_naturality {B C : CommHopfAlgCat.{u} k}
    (f : B ⟶ C) :
    (hopfSpecScalarExtensionIso k R C).inv ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp.map
          ((hopfSpec (CommRingCat.of k)).map f.op) =
      (hopfSpec (CommRingCat.of R)).map ((hopfScalarExtension k R).map f).op ≫
        (hopfSpecScalarExtensionIso k R B).inv := by
  dsimp only [CommRingCat.carrier, CommRingCat.commRing, hopfScalarExtension] at *
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change
    (pullbackSymmetry (Spec (CommRingCat.of C) ↘ Spec (CommRingCat.of k))
        (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≪≫
      pullbackSpecIso' k R C).inv ≫
        pullback.lift
          (pullback.fst (Spec (CommRingCat.of C) ↘ Spec (CommRingCat.of k))
              (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≫
            Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))
          (pullback.snd (Spec (CommRingCat.of C) ↘ Spec (CommRingCat.of k))
            (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k))) _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R R) f.hom.toAlgHom).toRingHom) ≫
        (pullbackSymmetry (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of k))
            (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≪≫
          pullbackSpecIso' k R B).inv
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [pullback.lift_fst]
    rw [← Category.assoc, scalarExtension_inv_fst, scalarExtension_inv_fst]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  · simp only [Category.assoc]
    erw [pullback.lift_snd]
    rw [scalarExtension_inv_snd, scalarExtension_inv_snd]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp

private theorem inv_square_to_hom_square {C : Type*} [Category C]
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : eX.inv ≫ f = g ≫ eY.inv) : f ≫ eY.hom = eX.hom ≫ g := by
  apply (Iso.inv_comp_eq eX).mp
  calc
    _ = (eX.inv ≫ f) ≫ eY.hom := (Category.assoc _ _ _).symm
    _ = (g ≫ eY.inv) ≫ eY.hom := congrArg (fun q => q ≫ eY.hom) h
    _ = g := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Naturality of the original forward group comparison. -/
theorem hopfSpecScalarExtensionIso_hom_naturality {B C : CommHopfAlgCat.{u} k}
    (f : B ⟶ C) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp.map
        ((hopfSpec (CommRingCat.of k)).map f.op) ≫
        (hopfSpecScalarExtensionIso k R B).hom =
      (hopfSpecScalarExtensionIso k R C).hom ≫
        (hopfSpec (CommRingCat.of R)).map ((hopfScalarExtension k R).map f).op := by
  have h := hopfSpecScalarExtensionIso_inv_naturality k R f
  have h' := inv_square_to_hom_square _ _ _ _ h
  dsimp only [CommRingCat.carrier, CommRingCat.commRing, hopfScalarExtension] at h' ⊢
  exact h'

/-- The original Hopf Spec comparisons form a natural group isomorphism. -/
def hopfSpecScalarExtensionNatIso :
    hopfSpec (CommRingCat.of k) ⋙
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp ≅
      (hopfScalarExtension k R).op ⋙ hopfSpec (CommRingCat.of R) :=
  NatIso.ofComponents (fun B => hopfSpecScalarExtensionIso k R B.unop)
    (fun f => hopfSpecScalarExtensionIso_hom_naturality k R f.unop)

private theorem scalarExtension_inv_base_naturality (k R A : Type u)
    [CommRing k] [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    {S : Type u} [CommRing S] [Algebra k S] (g : R →ₐ[k] S) :
    (pullbackSymmetry (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
        (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of k)) ≪≫
      pullbackSpecIso' k S A).inv ≫
        pullback.map
          (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k))
          (𝟙 _) (Spec.map (CommRingCat.ofHom g.toRingHom)) (𝟙 _) (by simp)
          (by
            change Spec.map (CommRingCat.ofHom (algebraMap k S)) ≫ 𝟙 _ =
              Spec.map (CommRingCat.ofHom g.toRingHom) ≫
                Spec.map (CommRingCat.ofHom (algebraMap k R))
            rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 1
            ext r
            exact (g.commutes r).symm) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map g (AlgHom.id k A)).toRingHom) ≫
        (pullbackSymmetry (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
        (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) ≪≫
      pullbackSpecIso' k R A).inv := by
  apply pullback.hom_ext
  · simp only [pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id]
    rw [scalarExtension_inv_fst, scalarExtension_inv_fst]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp
  · simp only [pullback.map, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, scalarExtension_inv_snd, scalarExtension_inv_snd]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2

/-- The original comparison is natural for an arbitrary map of coefficient algebras. -/
theorem hopfSpecScalarExtensionIso_base_naturality
    {S : Type u} [CommRing S] [Algebra k S] (g : R →ₐ[k] S) :
    (hopfSpecScalarExtensionIso k S A).inv.hom.hom.left ≫
        pullback.map
          (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k))
          (𝟙 _) (Spec.map (CommRingCat.ofHom g.toRingHom)) (𝟙 _) (by simp)
          (by
            change Spec.map (CommRingCat.ofHom (algebraMap k S)) ≫ 𝟙 _ =
              Spec.map (CommRingCat.ofHom g.toRingHom) ≫
                Spec.map (CommRingCat.ofHom (algebraMap k R))
            rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 1
            ext r
            exact (g.commutes r).symm) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map g (AlgHom.id k A)).toRingHom) ≫
        (hopfSpecScalarExtensionIso k R A).inv.hom.hom.left := by
  have h := scalarExtension_inv_base_naturality k R A g
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h ⊢
  exact h

end AlgebraicGeometry
