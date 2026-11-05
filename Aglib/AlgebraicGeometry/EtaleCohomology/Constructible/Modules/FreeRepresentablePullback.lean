/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FreeSet
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineEtale

/-! # Original free module generators under scheme inverse image

The original image adjunction and section equivalence identify pullback of
an original free generator with the generator of the actual base-changed
étale object. Finite étale partitions then imply its constructibility.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open ModuleCat.Sheaf

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type (u + 1)) [Ring R]

/-- Original image adjunction and actual sections identify pullback Homs. -/
def freeModulePullbackHomEquiv {X S : Scheme.{u}} (f : S ⟶ X) (U : X.Etale)
    (F : ModuleSheaf R S) :
    ((moduleInverseImage R f).obj
      (freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U) ⟶ F) ≃
      (freeRepresentable.{u + 1, u + 1, u, 0} S.smallEtaleTopology R
        ((siteBaseChange f).obj U) ⟶ F) :=
  ((moduleImageAdjunction R f).homEquiv _ F).trans
    ((freeRepresentableSectionsEquiv.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U
      ((moduleDirectImage R f).obj F)).trans
        (freeRepresentableSectionsEquiv.{u + 1, u + 1, u, 0} S.smallEtaleTopology R
          ((siteBaseChange f).obj U) F).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original Hom equivalence retains each actual coefficient arrow. -/
theorem freeModulePullbackHomEquiv_naturality {X S : Scheme.{u}} (f : S ⟶ X) (U : X.Etale)
    {F G : ModuleSheaf R S}
    (a : (moduleInverseImage R f).obj
      (freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U) ⟶ F)
    (b : F ⟶ G) :
    freeModulePullbackHomEquiv R f U G (a ≫ b) =
      freeModulePullbackHomEquiv R f U F a ≫ b := by
  apply (freeRepresentableSectionsEquiv.{u + 1, u + 1, u, 0} S.smallEtaleTopology R
    ((siteBaseChange f).obj U) G).injective
  simp only [freeModulePullbackHomEquiv, Equiv.trans_apply,
    freeRepresentableSectionsEquiv_naturality,
    (moduleImageAdjunction R f).homEquiv_naturality_right]
  dsimp [moduleDirectImage, ModuleCat.Sheaf.ConstantRing.moduleValuedDirectImage,
    Functor.sheafPushforwardContinuous]
  simp only [Equiv.apply_symm_apply]

/-- The actual original free module pulls back to the actual base-changed generator. -/
def freeModuleInverseImageIso {X S : Scheme.{u}} (f : S ⟶ X) (U : X.Etale) :
    (moduleInverseImage R f).obj (freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U) ≅
      freeRepresentable.{u + 1, u + 1, u, 0} S.smallEtaleTopology R ((siteBaseChange f).obj U) := by
  let e : coyoneda.obj (op ((moduleInverseImage R f).obj
      (freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U))) ≅
      coyoneda.obj (op (freeRepresentable.{u + 1, u + 1, u, 0} S.smallEtaleTopology R
        ((siteBaseChange f).obj U))) :=
    NatIso.ofComponents (fun F => (freeModulePullbackHomEquiv R f U F).toIso) (by
      intro F G b
      ext a
      exact freeModulePullbackHomEquiv_naturality R f U a b)
  exact (Coyoneda.fullyFaithful.preimageIso e).unop.symm

/-- A finite original étale map supplies finite-type local constancy of its
original free module sheaf without finiteness of its underlying additive group. -/
theorem freeModule_isFiniteTypeLocallyConstant_of_isFinite
    {X : Scheme.{u}} (U : X.Etale) [IsFinite U.hom] :
    IsFiniteTypeLocallyConstant
      (freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U) := by
  let Y : Scheme.FiniteEtale X := Scheme.FiniteEtale.mk U.hom
  let e : U ≅ (Scheme.FiniteEtale.toEtale X).obj Y :=
    MorphismProperty.Over.isoMk (Iso.refl U.left) (by
      change (𝟙 U.left) ≫ U.hom = U.hom
      exact Category.id_comp _)
  exact (isFiniteTypeLocallyConstant_iff_of_iso
    ((freeRepresentableFunctor.{u + 1, u + 1, u, 0} X.smallEtaleTopology R).mapIso e)).mpr
      (finiteEtale_freeModule_isFiniteTypeLocallyConstant R Y)

/-- Actual finite étale partitions of the original test scheme prove original
free module constructibility over the same coefficient ring. -/
theorem freeModule_isConstructible_of_finiteEtalePartitions
    {X : Scheme.{u}} (U : X.Etale)
    (hparts : ∀ V : X.affineOpens, ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
      ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj U).hom) :
    IsConstructible (freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U) := by
  intro V
  obtain ⟨p, hp⟩ := hparts V
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  let := hp i
  let e := ((moduleInverseImageComp R V.1.ι (p.inclusion i)).app
      (freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U)).symm ≪≫
    freeModuleInverseImageIso R (p.inclusion i ≫ V.1.ι) U
  exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr
    (freeModule_isFiniteTypeLocallyConstant_of_isFinite R
      ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj U))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
