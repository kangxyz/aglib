/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Additive
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Sections
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Restriction
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The original internal Hom in its source variable

The source functor is the flip of the existing bifunctor. Its section
comparison is the original slice-Hom equivalence, natural in the source.
Finite limits follow from the actual slice restriction and native Yoneda.
Injectivity of the actual restricted target gives preservation of epimorphisms
and hence exactness. This supplies the genuine source short exact sequences
used by the original target-resolution construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r

namespace SheafOfModules.InternalHom

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})]
  (R : Sheaf J CommRingCat.{max c h r})

/-- Original source precomposition, obtained by flipping the existing bifunctor. -/
abbrev sourceFunctor (N : SheafOfModulesOfCommRing R) :
    (SheafOfModulesOfCommRing R)ᵒᵖ ⥤ SheafOfModulesOfCommRing R :=
  (bifunctor.{c, h, r} R).flip.obj N

/-- The source functor keeps the existing internal-Hom object. -/
theorem sourceFunctor_obj (N : SheafOfModulesOfCommRing R)
    (M : (SheafOfModulesOfCommRing R)ᵒᵖ) :
    (sourceFunctor.{c, h, r} R N).obj M = sheaf R M.unop N := rfl

/-- The source functor keeps the original restricted precomposition arrow. -/
theorem sourceFunctor_map (N : SheafOfModulesOfCommRing R)
    {M M' : (SheafOfModulesOfCommRing R)ᵒᵖ} (a : M ⟶ M') :
    (sourceFunctor.{c, h, r} R N).map a = map R a.unop (𝟙 N) := rfl

/-- The target-variable map of the flipped bifunctor is the original postcomposition. -/
theorem sourceFunctor_postcompose_app {N N' : SheafOfModulesOfCommRing R} (b : N ⟶ N')
    (M : (SheafOfModulesOfCommRing R)ᵒᵖ) :
    ((bifunctor.{c, h, r} R).flip.map b).app M = map R (𝟙 M.unop) b := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Original source precomposition is additive. -/
instance sourceFunctor_additive (N : SheafOfModulesOfCommRing R) :
    (sourceFunctor.{c, h, r} R N).Additive where
  map_add {X Y f g} := by
    apply SheafOfModules.hom_ext
    ext U : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom R Y.unop N U.unop) = _
    ext V m
    exact (s.val.app V).hom.map_add _ _

/-- The whole flipped bifunctor is additive in the target on its original maps. -/
instance bifunctor_flip_additive : (bifunctor.{c, h, r} R).flip.Additive where
  map_add {X Y f g} := by
    apply NatTrans.ext
    funext M
    exact (homFunctor.{c, h, r} R M.unop).map_add

set_option backward.isDefEq.respectTransparency false in
/-- Original sections of the source functor are native Hom on the original slice. -/
def sectionHomSourceNatIso (N : SheafOfModulesOfCommRing R) (U : C) :
    sourceFunctor.{c, h, r} R N ⋙ SheafOfModules.evaluation
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (op U) ⋙
          forget₂ (ModuleCat _) AddCommGrpCat ≅
      (SheafOfModules.overFunctor.{max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).op ⋙
          preadditiveYoneda.obj (N.over U) :=
  NatIso.ofComponents
    (fun M => (sectionHomAddEquiv R M.unop N U).toAddCommGrpIso) (fun a => by
      ext s
      change sectionHomAddEquiv R _ N U ((map R a.unop (𝟙 N)).val.app (op U) s) =
        (SheafOfModules.overFunctor _ U).map a.unop ≫ sectionHomAddEquiv R _ N U s
      rw [sectionHomAddEquiv_map, CategoryTheory.Functor.map_id, Category.comp_id])

/-- Every component is the same original section-to-slice-Hom function. -/
theorem sectionHomSourceNatIso_hom_app_apply (N : SheafOfModulesOfCommRing R) (U : C)
    (M : (SheafOfModulesOfCommRing R)ᵒᵖ)
    (s : (sheaf R M.unop N).val.obj (op U)) :
    (sectionHomSourceNatIso.{c, h, r} R N U).hom.app M s = sectionHomEquiv R M.unop N U s := rfl

variable [HasSheafify J AddCommGrpCat.{max c h r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}]

/-- Source internal Hom preserves finite limits through the original evaluation comparisons. -/
instance sourceFunctor_preservesFiniteLimits [HasBinaryProducts C]
    (N : SheafOfModulesOfCommRing R) :
    PreservesFiniteLimits (sourceFunctor.{c, h, r} R N) := by
  let I := SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
    sheafToPresheaf J AddCommGrpCat.{max c h r}
  have : PreservesFiniteLimits (sourceFunctor.{c, h, r} R N ⋙ I) := by
    apply preservesFiniteLimits_of_evaluation
    intro U
    let : PreservesFiniteLimits ((SheafOfModules.overFunctor.{max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U.unop).op) :=
      preservesFiniteLimits_op _
    exact preservesFiniteLimits_of_natIso (sectionHomSourceNatIso.{c, h, r} R N U.unop).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (sourceFunctor.{c, h, r} R N) I

/-- Injectivity of the actual restricted target gives the original sheaf epimorphism. -/
instance sourceFunctor_preservesEpimorphisms (N : SheafOfModulesOfCommRing R)
    [∀ U : C, Injective (N.over U)] :
    (sourceFunctor.{c, h, r} R N).PreservesEpimorphisms where
  preserves a ha := by
    let := ha
    let : Mono a.unop := inferInstance
    let : ∀ U : C, Mono ((SheafOfModules.overFunctor _ U).map a.unop) := by
      intro U
      infer_instance
    exact precompose_epi_of_injective_over R N a.unop

/-- The source functor into an actual slice-injective target is exact. -/
instance sourceFunctor_preservesHomology [HasBinaryProducts C]
    (N : SheafOfModulesOfCommRing R) [∀ U : C, Injective (N.over U)] :
    (sourceFunctor.{c, h, r} R N).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The original source sequence is reversed by actual internal-Hom precomposition maps. -/
theorem shortExact_source [HasBinaryProducts C]
    (N : SheafOfModulesOfCommRing R) [∀ U : C, Injective (N.over U)]
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (hS : S.ShortExact) :
    (S.op.map (sourceFunctor.{c, h, r} R N)).ShortExact := by
  let : PreservesFiniteColimits (sourceFunctor.{c, h, r} R N) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact hS.op.map_of_exact _

/-- The original internal-Hom complexes form a whole contravariant source functor.
The target complex and all its differential maps are retained. -/
def sourceComplexFunctor {ι : Type*} (d : ComplexShape ι)
    (K : HomologicalComplex (SheafOfModulesOfCommRing R) d) :
    (SheafOfModulesOfCommRing R)ᵒᵖ ⥤
      HomologicalComplex (SheafOfModulesOfCommRing R) d where
  obj M := ((homFunctor.{c, h, r} R M.unop).mapHomologicalComplex d).obj K
  map a := (NatTrans.mapHomologicalComplex (precomposeNatTrans.{c, h, r} R a.unop) d).app K
  map_id M := by
    simp only [unop_id, precomposeNatTrans_id, NatTrans.mapHomologicalComplex_id,
      NatTrans.id_app]
  map_comp a b := by
    rw [unop_comp, ← precomposeNatTrans_comp, NatTrans.mapHomologicalComplex_comp]
    rfl

/-- The source-complex functor is additive through its original termwise source maps. -/
instance sourceComplexFunctor_additive {ι : Type*} (d : ComplexShape ι)
    (K : HomologicalComplex (SheafOfModulesOfCommRing R) d) :
    (sourceComplexFunctor.{c, h, r} R d K).Additive where
  map_add {X Y f g} := by
    ext i : 1
    change (sourceFunctor.{c, h, r} R (K.X i)).map (f + g) =
      (sourceFunctor.{c, h, r} R (K.X i)).map f +
        (sourceFunctor.{c, h, r} R (K.X i)).map g
    exact (sourceFunctor.{c, h, r} R (K.X i)).map_add

omit [HasSheafify J AddCommGrpCat.{max c h r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}] in
/-- Evaluation of the original source-complex sequence is the actual source-Hom sequence. -/
theorem sourceComplexFunctor_shortComplex_eval {ι : Type*} (d : ComplexShape ι)
    (K : HomologicalComplex (SheafOfModulesOfCommRing R) d)
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (i : ι) :
    ((S.op.map (sourceComplexFunctor.{c, h, r} R d K)).map
      (HomologicalComplex.eval (SheafOfModulesOfCommRing R) d i)) =
        S.op.map (sourceFunctor.{c, h, r} R (K.X i)) := rfl

/-- Slice injectivity of the actual target terms makes the original Hom-source sequence
short exact as a sequence of complexes, without a finite or free source premise. -/
theorem shortExact_sourceComplex [HasBinaryProducts C] {ι : Type*} (d : ComplexShape ι)
    (K : HomologicalComplex (SheafOfModulesOfCommRing R) d)
    [∀ i : ι, ∀ U : C, Injective ((K.X i).over U)]
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (hS : S.ShortExact) :
    (S.op.map (sourceComplexFunctor.{c, h, r} R d K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  rw [sourceComplexFunctor_shortComplex_eval]
  exact shortExact_source.{c, h, r} R (K.X i) S hS

end SheafOfModules.InternalHom
