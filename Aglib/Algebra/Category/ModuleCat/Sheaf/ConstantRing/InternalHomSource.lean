/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Source
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Commutative
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.OverInjective
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.Algebra.Category.ModuleCat.AB

/-!
# Source exactness of original internal Hom into injective constant-ring sheaves

The existing over-restriction theorem supplies injectivity on each actual
slice. The generic source-Hom construction therefore reverses an original
short exact sequence into an original short exact sequence. No finite or
locally free source assumption is used for an injective target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c h

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] [HasBinaryProducts C]
  (J : GrothendieckTopology C) (Λ : Type (max c h)) [CommRing Λ]
  [HasWeakSheafify J RingCat.{max c h}] [J.WEqualsLocallyBijective RingCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  [∀ U : C, HasWeakSheafify (J.over U) RingCat.{max c h}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective RingCat.{max c h}]
  [∀ U : C, (J.over U).HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max c h}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [∀ U : C, (J.over U).HasSheafCompose
    (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]

attribute [local instance] ModuleCat.Sheaf.hasSheafify

set_option backward.isDefEq.respectTransparency false in
local instance sourceFunctor_additive_native
    (I : ModuleSheaf.{c, h, max c h, max c h} J Λ) :
    (SheafOfModules.InternalHom.sourceFunctor.{c, h, 0}
      (commutativeSheaf J Λ) I).Additive :=
  SheafOfModules.InternalHom.sourceFunctor_additive.{c, h, 0}
    (commutativeSheaf J Λ) I

set_option backward.isDefEq.respectTransparency false in
local instance sourceFunctor_zero_native
    (I : ModuleSheaf.{c, h, max c h, max c h} J Λ) :
    @Functor.PreservesZeroMorphisms
      (ModuleSheaf.{c, h, max c h, max c h} J Λ)ᵒᵖ inferInstance
      (SheafOfModulesOfCommRing (commutativeSheaf J Λ)) inferInstance
      inferInstance inferInstance
      (SheafOfModules.InternalHom.sourceFunctor.{c, h, 0} (commutativeSheaf J Λ) I) := by
  let : (SheafOfModules.InternalHom.sourceFunctor.{c, h, 0} (commutativeSheaf J Λ) I :
      (ModuleSheaf.{c, h, max c h, max c h} J Λ)ᵒᵖ ⥤
        SheafOfModulesOfCommRing (commutativeSheaf J Λ)).Additive :=
    SheafOfModules.InternalHom.sourceFunctor_additive.{c, h, 0} (commutativeSheaf J Λ) I
  infer_instance

set_option backward.isDefEq.respectTransparency false in
local instance sourceComplexFunctor_zero_native {ι : Type*} (d : ComplexShape ι)
    (K : HomologicalComplex (ModuleSheaf.{c, h, max c h, max c h} J Λ) d) :
    @Functor.PreservesZeroMorphisms
      (ModuleSheaf.{c, h, max c h, max c h} J Λ)ᵒᵖ inferInstance
      (HomologicalComplex (SheafOfModulesOfCommRing (commutativeSheaf J Λ)) d) inferInstance
      inferInstance inferInstance
      (SheafOfModules.InternalHom.sourceComplexFunctor.{c, h, 0}
        (commutativeSheaf J Λ) d K) := by
  let : (SheafOfModules.InternalHom.sourceComplexFunctor.{c, h, 0}
      (commutativeSheaf J Λ) d K :
      (ModuleSheaf.{c, h, max c h, max c h} J Λ)ᵒᵖ ⥤
        HomologicalComplex (SheafOfModulesOfCommRing (commutativeSheaf J Λ)) d).Additive :=
    SheafOfModules.InternalHom.sourceComplexFunctor_additive.{c, h, 0}
      (commutativeSheaf J Λ) d K
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Actual over-restriction injectivity supplies exactness of the original source-Hom functor. -/
instance sourceFunctor_preservesHomology_of_injective
    (I : ModuleSheaf.{c, h, max c h, max c h} J Λ) [Injective I] :
    (SheafOfModules.InternalHom.sourceFunctor.{c, h, 0}
      (commutativeSheaf J Λ) I).PreservesHomology := by
  let : ∀ U : C, Injective (I.over U) := by
    intro U
    change Injective ((SheafOfModules.overFunctor.{max c h} (constantRing J Λ) U).obj I)
    infer_instance
  exact SheafOfModules.InternalHom.sourceFunctor_preservesHomology
    (commutativeSheaf J Λ) I

set_option backward.isDefEq.respectTransparency false in
/-- The native source sequence is reversed with its original precomposition arrows. -/
theorem shortExact_source_injective
    (I : ModuleSheaf.{c, h, max c h, max c h} J Λ) [Injective I]
    (S : ShortComplex (ModuleSheaf.{c, h, max c h, max c h} J Λ)) (hS : S.ShortExact) :
    (S.op.map (SheafOfModules.InternalHom.sourceFunctor.{c, h, 0}
      (commutativeSheaf J Λ) I)).ShortExact := by
  let : ∀ U : C, Injective (I.over U) := by
    intro U
    change Injective ((SheafOfModules.overFunctor.{max c h} (constantRing J Λ) U).obj I)
    infer_instance
  exact SheafOfModules.InternalHom.shortExact_source.{c, h, 0}
    (commutativeSheaf J Λ) I S hS

set_option backward.isDefEq.respectTransparency false in
/-- The actual termwise-injective target complex reverses every original source short
exact sequence into a short exact sequence of the existing internal-Hom complexes. -/
theorem shortExact_sourceComplex_injective {ι : Type*} (d : ComplexShape ι)
    (K : HomologicalComplex
      (ModuleSheaf.{c, h, max c h, max c h} J Λ) d)
    [∀ i : ι, Injective (K.X i)]
    (S : ShortComplex (ModuleSheaf.{c, h, max c h, max c h} J Λ)) (hS : S.ShortExact) :
    (S.op.map (SheafOfModules.InternalHom.sourceComplexFunctor.{c, h, 0}
      (commutativeSheaf J Λ) d K)).ShortExact := by
  let : ∀ i : ι, ∀ U : C, Injective ((K.X i).over U) := by
    intro i U
    change Injective ((SheafOfModules.overFunctor.{max c h} (constantRing J Λ) U).obj (K.X i))
    infer_instance
  exact SheafOfModules.InternalHom.shortExact_sourceComplex.{c, h, 0}
    (commutativeSheaf J Λ) d K S hS

end ModuleCat.Sheaf.ConstantRing
