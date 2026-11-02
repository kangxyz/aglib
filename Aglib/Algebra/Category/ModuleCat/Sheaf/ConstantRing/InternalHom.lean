/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Commutative
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Over
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Pullback
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Full
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Sections
public import Mathlib.CategoryTheory.HomCongr

/-!
# Original internal-Hom sections through the constant-ring coefficient equivalence

The original constant-ring-over map and direct-image comparison transport
ringed slice morphisms to module-valued slice morphisms. Full faithfulness of
original scalar restriction and the existing coefficient equivalence give the
whole additive Hom comparison. Its section specialization is the original
internal-Hom section map; every component function is retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r m

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type r) (U : C)

section Ring

variable [Ring Λ]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify (J.over U) RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [(J.over U).WEqualsLocallyBijective RingCat.{r}]
  [(J.over U).HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [HasWeakSheafify J AddCommGrpCat.{m}] [HasWeakSheafify (J.over U) AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m})]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m})]

/-- The actual ringed and module-valued slice Hom groups, through the original comparisons. -/
def overHomValuedAddEquiv (M N : ModuleSheaf.{c, h, r, m} J Λ) :
    (M.over U ⟶ N.over U) ≃+
      ((J.overPullback (ModuleCat.{m} Λ) U).obj ((moduleSheafEquivalence J Λ).inverse.obj M) ⟶
        (J.overPullback (ModuleCat.{m} Λ) U).obj ((moduleSheafEquivalence J Λ).inverse.obj N)) where
  __ :=
    (SheafOfModules.restrictScalarsHomAddEquiv (overRingIso J U Λ).hom
        (M.over U) (N.over U)).toEquiv.trans
      ((Functor.FullyFaithful.ofFullyFaithful
        (moduleSheafEquivalence (J.over U) Λ).inverse).homEquiv.trans
        (Iso.homCongr
          ((moduleDirectImageComparison.{max c h, h, c, h, r, m}
            (Over.forget U) (J.over U) J Λ).app M)
          ((moduleDirectImageComparison.{max c h, h, c, h, r, m}
            (Over.forget U) (J.over U) J Λ).app N)))
  map_add' f g := by
    apply ObjectProperty.hom_ext
    ext V x
    rfl

/-- The whole slice Hom comparison keeps each original component function. -/
theorem overHomValuedAddEquiv_apply_app (M N : ModuleSheaf.{c, h, r, m} J Λ)
    (f : M.over U ⟶ N.over U) (V : (Over U)ᵒᵖ) (x : M.val.obj (op V.unop.left)) :
    (overHomValuedAddEquiv J Λ U M N f).hom.app V x = f.val.app V x := rfl

/-- The original slice-Hom comparison is natural in the whole target coefficient. -/
def overHomValuedNatIso (M : ModuleSheaf.{c, h, r, m} J Λ) :
    SheafOfModules.overFunctor (constantRing J Λ) U ⋙
        preadditiveCoyoneda.obj (op (M.over U)) ≅
      (moduleSheafEquivalence J Λ).inverse ⋙ J.overPullback (ModuleCat.{m} Λ) U ⋙
        preadditiveCoyoneda.obj (op ((J.overPullback (ModuleCat.{m} Λ) U).obj
          ((moduleSheafEquivalence J Λ).inverse.obj M))) :=
  NatIso.ofComponents (fun N => (overHomValuedAddEquiv J Λ U M N).toAddCommGrpIso)
    (fun f => by
      ext g
      rfl)

end Ring

section Commutative

variable [CommRing Λ]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify (J.over U) RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [(J.over U).WEqualsLocallyBijective RingCat.{r}]
  [(J.over U).HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [HasWeakSheafify J AddCommGrpCat.{m}] [HasWeakSheafify (J.over U) AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m})]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m})]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

/-- Original internal-Hom sections specialize the whole slice comparison. -/
def sectionValuedHomAddEquiv (M N : ModuleSheaf.{c, h, r, m} J Λ) :
    (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U) ≃+
      ((J.overPullback (ModuleCat.{m} Λ) U).obj ((moduleSheafEquivalence J Λ).inverse.obj M) ⟶
        (J.overPullback (ModuleCat.{m} Λ) U).obj ((moduleSheafEquivalence J Λ).inverse.obj N)) :=
  (SheafOfModules.InternalHom.sectionHomAddEquiv (commutativeSheaf J Λ) M N U).trans
    ((overHomValuedNatIso J Λ U M).app N).addCommGroupIsoToAddEquiv

/-- The section comparison preserves the actual slice-linear transformation. -/
theorem sectionValuedHomAddEquiv_apply_app (M N : ModuleSheaf.{c, h, r, m} J Λ)
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U))
    (V : (Over U)ᵒᵖ) (x : M.val.obj (op V.unop.left)) :
    (sectionValuedHomAddEquiv J Λ U M N s).hom.app V x = s.val.app V x := rfl

/-- Source precomposition remains the original module-valued source map on the slice. -/
theorem sectionValuedHomAddEquiv_precompose
    {M M' N : ModuleSheaf.{c, h, r, m} J Λ} (a : M' ⟶ M)
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U)) :
    sectionValuedHomAddEquiv J Λ U M' N
        ((SheafOfModules.InternalHom.map (commutativeSheaf J Λ) a (𝟙 N)).val.app (op U) s) =
      (J.overPullback (ModuleCat.{m} Λ) U).map ((moduleSheafEquivalence J Λ).inverse.map a) ≫
        sectionValuedHomAddEquiv J Λ U M N s := by
  apply ObjectProperty.hom_ext
  ext V x
  rfl

/-- Target postcomposition remains the original module-valued coefficient map on the slice. -/
theorem sectionValuedHomAddEquiv_postcompose
    {M N N' : ModuleSheaf.{c, h, r, m} J Λ} (b : N ⟶ N')
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U)) :
    sectionValuedHomAddEquiv J Λ U M N'
        ((SheafOfModules.InternalHom.map (commutativeSheaf J Λ) (𝟙 M) b).val.app (op U) s) =
      sectionValuedHomAddEquiv J Λ U M N s ≫
        (J.overPullback (ModuleCat.{m} Λ) U).map ((moduleSheafEquivalence J Λ).inverse.map b) := by
  apply ObjectProperty.hom_ext
  ext V x
  rfl

end Commutative

end ModuleCat.Sheaf.ConstantRing
