/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineGeometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineCoverAlgebra
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.CoproductSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestrictionAdditive
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AmitsurCech
public import Aglib.CategoryTheory.Limits.OverCoproducts
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CoproductCover
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CechNerveIso

/-! # Actual affine Čech acyclicity of quasi-coherent coefficients

The coefficient is the original additive pullback-section sheaf. Finite affine
families are compared with their actual coproduct and its faithfully flat
algebra; the coproduct is not claimed to refine the original covering sieve.
No coefficient flatness or cohomological vanishing hypothesis is imposed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]

/-- Transport the original coefficient along the actual affine base isomorphism. -/
def affineCoefficientBaseIso :
    additiveSectionsPresheaf X F ≅
      (affineSliceEquivalence X).functor.op ⋙
        additiveSectionsPresheaf (Spec Γ(X, ⊤)) ((Modules.pullback X.isoSpec.inv).obj F) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (affineSliceEquivalence X).unitIso).symm
      (additiveSectionsPresheaf X F) ≪≫
    Functor.isoWhiskerRight
      (Functor.opComp (affineSliceEquivalence X).functor (affineSliceEquivalence X).inverse)
      (additiveSectionsPresheaf X F) ≪≫
    Functor.associator (affineSliceEquivalence X).functor.op
      (affineSliceEquivalence X).inverse.op (additiveSectionsPresheaf X F) ≪≫
    Functor.isoWhiskerLeft (affineSliceEquivalence X).functor.op
      (additiveBaseRestrictionIso X.isoSpec.inv F)

/-- The actual affine singleton nerve has the original Amitsur spectrum coordinates. -/
def affineSingletonCechIso (T : Over X) [IsAffine T.left] :
    letI : Algebra Γ(X, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
      ((cechNerveTerminalFrom T).rightOp ⋙ additiveSectionsPresheaf X F) ≅
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
      ((cechNerveTerminalFrom ((algSpec Γ(X, ⊤)).obj
        (op (CommAlgCat.of Γ(X, ⊤) Γ(T.left, ⊤))))).rightOp ⋙
          additiveSectionsPresheaf (Spec Γ(X, ⊤)) ((Modules.pullback X.isoSpec.inv).obj F)) := by
  letI : Algebra Γ(X, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  exact (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso
      (Functor.isoWhiskerLeft (cechNerveTerminalFrom T).rightOp
        (affineCoefficientBaseIso X F)) ≪≫
    Cech.productNerveChangeComplexIso (affineSliceEquivalence X).functor T
      (additiveSectionsPresheaf (Spec Γ(X, ⊤)) ((Modules.pullback X.isoSpec.inv).obj F)) ≪≫
    Cech.productNerveComplexIso (affineOverAlgSpecIso X T)
      (additiveSectionsPresheaf (Spec Γ(X, ⊤)) ((Modules.pullback X.isoSpec.inv).obj F))

/-- Positive exactness for an actual faithfully flat affine covering object. -/
theorem affineSingleton_exactAt_succ (T : Over X) [IsAffine T.left]
    [Flat T.hom] [Surjective T.hom] (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
      ((cechNerveTerminalFrom T).rightOp ⋙ additiveSectionsPresheaf X F)).ExactAt (n + 1) := by
  let : Algebra Γ(X, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  have : Module.FaithfullyFlat Γ(X, ⊤) Γ(T.left, ⊤) :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine T.hom).mp
      ⟨inferInstance, inferInstance⟩
  exact (spectrumCech_exactAt_succ Γ(X, ⊤) Γ(T.left, ⊤)
    ((Modules.pullback X.isoSpec.inv).obj F) n).of_iso (affineSingletonCechIso X F T).symm

/-- Positive exactness on finite affine étale families, using the original
family complex and the original additive section restrictions. -/
theorem finiteAffineFamily_exactAt_succ {ι : Type (u + 1)} [Finite ι]
    (U : ι → Over X) [∀ i, IsAffine (U i).left] [∀ i, Etale (U i).hom]
    (hcover : ∀ x : X, ∃ i y, (U i).hom y = x) (n : ℕ) :
    ((cechComplexFunctor U).obj (additiveSectionsPresheaf X F)).ExactAt (n + 1) := by
  let T : Over X := Over.mk (Sigma.desc (fun i => (U i).hom))
  have : IsAffine T.left := by
    change IsAffine (∐ fun i => (U i).left)
    infer_instance
  have : Flat T.hom := by
    change Flat (Sigma.desc (fun i => (U i).hom))
    infer_instance
  have : Surjective T.hom := ⟨by
    intro x
    obtain ⟨i, y, rfl⟩ := hcover x
    exact ⟨Sigma.ι (fun j => (U j).left) i y, by simp [T, ← Scheme.Hom.comp_apply]⟩⟩
  let : PreservesFiniteProducts (additiveSectionsPresheaf X F) :=
    Scheme.preservesFiniteProducts_of_isSheaf_etale_over X _
      (additiveSectionsPresheaf_isSheaf_etale X F)
  exact ((affineSingleton_exactAt_succ X F T n).of_iso
    (Cech.productNerveComplexIso (Over.coproductIso U)
      (additiveSectionsPresheaf X F)).symm).of_iso
    (Cech.coproductCechComplexIso U (additiveSectionsPresheaf X F))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
