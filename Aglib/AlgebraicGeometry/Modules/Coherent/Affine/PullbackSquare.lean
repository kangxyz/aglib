/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.FGModuleCat.ScalarExtension
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.Coherent.FlatPullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.CategoryTheory.SmallModel.Functor
public import Aglib.CategoryTheory.SmallModel.Functoriality

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Coherent.Affine.PullbackSquare` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b273d9f384b45daa6229590f0bb0189d53d5efac362b7950e6527a08937c5d83`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules.Coherent
  (coherentExactPullback coherentExactStructure coherentPullback coherent_obj_quasicoherent)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (FiniteTypeSheaves finiteTypeSheavesSpecModuleEquivalence finiteTypeSheavesToModules)
open _root_.CategoryTheory.ExactCategory (ExactFunctor)
open _root_.ModuleCat (finiteModule finiteModuleExactStructure)
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Affine.PullbackSquare
universe u
section Affine
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable [IsNoetherianRing R] [IsNoetherianRing S]

/-- The canonical fromTildeΓ counit on the actual coherent affine objects. -/
def coherentSourceTildeIso (R : CommRingCat.{u}) [IsNoetherianRing R] :
    (finiteTypeSheavesToModules (Spec R) ⋙ moduleSpecΓFunctor) ⋙ tilde.functor R ≅
      finiteTypeSheavesToModules (Spec R) :=
  NatIso.ofComponents (fun M => by
    letI : M.obj.IsQuasicoherent := coherent_obj_quasicoherent M
    letI : IsIso M.obj.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ _).mp inferInstance
    exact asIso M.obj.fromTildeΓ)
    (fun f => Scheme.Modules.fromTildeΓNatTrans.naturality f.hom)

/-- The actual affine sheaf pullback/global-sections square, before lifting
to finite-module subcategories. -/
def coherentPullbackAmbientSquare :
    (finiteTypeSheavesToModules (Spec R) ⋙ Scheme.Modules.pullback (Spec.map φ)) ⋙
      moduleSpecΓFunctor ≅
    (finiteTypeSheavesToModules (Spec R) ⋙ moduleSpecΓFunctor) ⋙
      ModuleCat.extendScalars φ.hom := by
  let T := finiteTypeSheavesToModules (Spec R) ⋙ moduleSpecΓFunctor
  let e : finiteTypeSheavesToModules (Spec R) ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      (T ⋙ ModuleCat.extendScalars φ.hom) ⋙ tilde.functor S :=
    Functor.isoWhiskerRight (coherentSourceTildeIso R).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft T (Scheme.Modules.tildePullbackIso φ) ≪≫
      (Functor.associator _ _ _).symm
  exact Functor.isoWhiskerRight e moduleSpecΓFunctor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (T ⋙ ModuleCat.extendScalars φ.hom)
      (tilde.toTildeΓNatIso (R := S)).symm ≪≫ Functor.rightUnitor _

/-- The same canonical comparison on the actual finite-module categories. -/
def coherentPullbackSquare :
    coherentPullback (Spec.map φ) ⋙ (finiteTypeSheavesSpecModuleEquivalence S).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence R).functor ⋙ FGModuleCat.finiteModuleExtension φ :=
  ((finiteModule S).fullyFaithfulι.whiskeringRight _).preimageIso
    (coherentPullbackAmbientSquare φ)

variable [Flat (Spec.map φ)]

/-- These composites are exactly the two routes in the affine square. -/
def pullbackThenGlobalSectionsExact :
    ExactFunctor (coherentExactStructure (Spec R)) (finiteModuleExactStructure.{u, u} S) :=
  (coherentExactPullback (Spec.map φ)).comp
      (Scheme.Modules.Coherent.globalSectionsExact S)

def globalSectionsThenExtensionExact :
    ExactFunctor (coherentExactStructure (Spec R)) (finiteModuleExactStructure.{u, u} S) :=
  (Scheme.Modules.Coherent.globalSectionsExact R).comp
    (FGModuleCat.finiteModuleExtensionExact φ (Flat.SpecMap_iff.mp inferInstance))

/-- The actual affine comparison descended through the specified SmallModels. -/
def affinePullbackSmallModelIso :
    (pullbackThenGlobalSectionsExact φ).smallModel.{u + 1}.toFunctor ≅
      (globalSectionsThenExtensionExact φ).smallModel.{u + 1}.toFunctor :=
  _root_.CategoryTheory.ExactCategory.ExactFunctor.smallModelNatIso (coherentPullbackSquare φ)

end Affine
section Fields
variable (K L : Type u) [Field K] [Field L] (f : K →+* L)
/-- Every field homomorphism supplies the genuine flatness used by G-pullback. -/
instance fieldSpecMapFlat : Flat (Spec.map (CommRingCat.ofHom f)) :=
  Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField K) f)

end Fields
end AlgebraicGeometry.Scheme.Modules.Coherent.Affine.PullbackSquare
