/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.TensorCech
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic

/-!
# Acyclicity of internal Hom into an injective module sheaf

Original tensor-Hom currying identifies the tuple cochains of the existing
internal-Hom sheaf with Hom from the tensor of the original free tuple complex.
The comparison commutes with the original alternating differentials. Tensor
preserves the evaluated extra-degeneracy contraction without a flatness premise;
injectivity of the target gives positive exactness. The existing family-acyclic
criterion then gives vanishing of original positive `Sheaf.H`.

The global acyclicity endpoint retains the standard site-compatible value
universe and the displayed sheafification, enough-injective, Ext and slice
finite-product hypotheses. No assertion that internal Hom preserves injective
objects is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex MonoidalCategory

universe c h r e

namespace SheafOfModules.InternalHom.PresheafSource

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})]
  (R : Sheaf J CommRingCat.{max c h r})
  (M Q : PresheafOfModulesOfCommRing.{max c h r} R.obj)
  (I : SheafOfModulesOfCommRing R)

-- Align the original ringed-sheaf forgetful value with its native presheaf parent.
set_option backward.isDefEq.respectTransparency false in
/-- The existing presheaf-source tensor-Hom equivalence is additive. -/
def tensorHomAddEquivRight :
    (Q ⊗ M ⟶ (I.val : PresheafOfModulesOfCommRing.{max c h r} R.obj)) ≃+
      (Q ⟶ ((sheaf R M I).val : PresheafOfModulesOfCommRing.{max c h r} R.obj)) where
  toEquiv := tensorHomEquivRight.{c, h, r} R M Q I
  map_add' f g := by
    ext U : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (_ : RawHom R M I U.unop) = _
    ext V m
    rfl

end SheafOfModules.InternalHom.PresheafSource

namespace PresheafOfModules.Cech

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})]
  (R : Sheaf J CommRingCat.{max c h r})
  (M : PresheafOfModulesOfCommRing.{max c h r} R.obj)
  (I : SheafOfModulesOfCommRing R)

-- Align the original ringed-sheaf forgetful value with its native presheaf parent.
set_option backward.isDefEq.respectTransparency false in
/-- Currying and the original free-module comparison identify the actual additive cochains. -/
def freeTensorHomAddEquiv (F : Cᵒᵖ ⥤ Type (max c h r)) :
    ((PresheafOfModules.freeWide.{max c h r, max c h r, c, h}
        (R.obj ⋙ forget₂ CommRingCat RingCat)).obj F ⊗ M ⟶
        (I.val : PresheafOfModulesOfCommRing.{max c h r} R.obj)) ≃+
      (F ⋙ AddCommGrpCat.free ⟶
        (SheafOfModules.InternalHom.PresheafSource.sheaf R M I).val.presheaf) :=
  (SheafOfModules.InternalHom.PresheafSource.tensorHomAddEquivRight.{c, h, r}
      R M _ I).trans
    (PresheafOfModules.freeAbelianHomAddEquiv.{max c h r, c, h, max c h r}
      (R.obj ⋙ forget₂ CommRingCat RingCat) F _)

/-- The cochain comparison preserves precomposition by the original maps of tuple generators. -/
theorem freeTensorHomAddEquiv_naturality {F F' : Cᵒᵖ ⥤ Type (max c h r)}
    (a : F' ⟶ F)
    (b : (PresheafOfModules.freeWide.{max c h r, max c h r, c, h}
      (R.obj ⋙ forget₂ CommRingCat RingCat)).obj F ⊗ M ⟶
      (I.val : PresheafOfModulesOfCommRing.{max c h r} R.obj)) :
    freeTensorHomAddEquiv R M I F'
        ((PresheafOfModules.freeWide (R.obj ⋙ forget₂ CommRingCat RingCat)).map a ▷ M ≫ b) =
      Functor.whiskerRight a AddCommGrpCat.free ≫ freeTensorHomAddEquiv R M I F b := by
  change PresheafOfModules.freeAbelianHomEquiv _ F' _
      (SheafOfModules.InternalHom.PresheafSource.tensorHomEquivRight R M _ I
        ((PresheafOfModules.freeWide (R.obj ⋙ forget₂ CommRingCat RingCat)).map a ▷ M ≫ b)) = _
  rw [SheafOfModules.InternalHom.PresheafSource.tensorHomEquivRight_whiskerRight_comp]
  exact PresheafOfModules.freeAbelianHomEquiv_naturality _ F _ a _

-- Keep the actual presheaf Hom additive parent when comparing the native differentials.
set_option backward.isDefEq.respectTransparency false in
/-- The whole tensor-Hom cochain comparison, including its original differentials. -/
def tensorHomComplexIso {F G : Cᵒᵖ ⥤ Type (max c h r)} (f : F ⟶ G) :
    tensorHomComplex R.obj M f I.val ≅
      CategoryTheory.Presheaf.Cech.additiveHomComplex f
        (SheafOfModules.InternalHom.PresheafSource.sheaf R M I).val.presheaf := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n =>
    (freeTensorHomAddEquiv R M I
      (CategoryTheory.Presheaf.Cech.tuplePresheaf f n)).toAddCommGrpIso) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  apply AddCommGrpCat.ext
  intro a
  symm
  change (freeTensorHomAddEquiv R M I _)
      ((tensorFreeComplex R.obj M f).d (i + 1) i ≫ a) =
    (CategoryTheory.Presheaf.Cech.freeComplex f).d (i + 1) i ≫
      freeTensorHomAddEquiv R M I _ a
  simp only [tensorFreeComplex, Functor.mapHomologicalComplex_obj_d, freeComplex,
    CategoryTheory.Presheaf.Cech.freeComplex,
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
    Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp, Preadditive.zsmul_comp,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact freeTensorHomAddEquiv_naturality R M I _ a

-- Align the original ringed-sheaf forgetful value with its native presheaf parent.
set_option backward.isDefEq.respectTransparency false in
/-- Original internal-Hom tuple cochains are positively exact for an injective target. -/
theorem internalHom_additiveHomComplex_exactAt_succ
    [Injective (I.val : PresheafOfModulesOfCommRing.{max c h r} R.obj)]
    {F G : Cᵒᵖ ⥤ Type (max c h r)} (f : F ⟶ G) (n : ℕ) :
    (CategoryTheory.Presheaf.Cech.additiveHomComplex f
      (SheafOfModules.InternalHom.PresheafSource.sheaf R M I).val.presheaf).ExactAt (n + 1) :=
  (tensorHomComplex_exactAt_succ R.obj M f I.val n).of_iso (tensorHomComplexIso R M I f)

end PresheafOfModules.Cech

namespace SheafOfModules.InternalHom

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  (R : Sheaf J CommRingCat.{max c h}) [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  (M I : SheafOfModulesOfCommRing R) [Injective I]

/-- Internal Hom into an injective module sheaf satisfies the genuine tuple-acyclic predicate. -/
theorem familyCechAcyclic : CategoryTheory.Sheaf.ModuleCoefficients.FamilyCechAcyclic
    ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).obj
      (sheaf R M I)) := by
  have : Injective (I.val : PresheafOfModulesOfCommRing.{max c h} R.obj) :=
    inferInstanceAs (Injective ((SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).obj I))
  intro W ι U n
  exact PresheafOfModules.Cech.internalHom_additiveHomComplex_exactAt_succ.{c, h, 0}
    R M.val I (CategoryTheory.Presheaf.Cech.familyMap U) n

variable [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max c h})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max c h})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h})]

/-- The existing underlying internal-Hom sheaf has zero positive original cohomology. -/
theorem cohomology_subsingleton_of_injective {T : C} (hT : IsTerminal T) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{e}
      ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).obj
        (sheaf R M I)) (q + 1)) :=
  subsingleton_of_forall_eq 0 fun x => (familyCechAcyclic R M I).cohomology_eq_zero hT q x

end SheafOfModules.InternalHom
