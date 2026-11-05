/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FiniteCompactificationComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ModuleHigherImageComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleModuleTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.CategoryTheory.Abelian.ObjectProperty.Retract
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleRestriction

/-! # Actual coprime descent for compactified higher images

The original finite-etale unit and trace split before applying the original
compactified higher-image functor. The finite exceptional compositor identifies
the covering term. No open immersion is treated as proper, and no conclusion
about constructibility is included in the finite comparison's hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wY wX wS wG wF wGF

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {Y X S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) [IsFinite g]
    [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [gModels : ∀ C : Hom.DenseCompactification g,
      HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
    [fModels : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
    [gfModels : ∀ C : Hom.DenseCompactification (g ≫ f),
      HasDerivedCategory.{wGF} (ModuleSheaf C.Xbar Λ)]

/-- Evaluation of the whole finite comparison in the original valued coefficient
conventions. The only coefficient restriction is its literal positive annihilator. -/
def finiteModuleCompactificationValuedCompObjIso
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification (g ≫ f))
    (E : ModuleValuedSheaf Y Λ) (n : ℕ) (hn : 0 < n) (hE : n • 𝟙 E = 0) (q : ℕ) :
    (moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage D.toCompactification Λ q).obj
          ((moduleSheafEquivalence Y Λ).functor.obj E)) ≅
      (moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C.toCompactification Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj ((moduleValuedDirectImage g Λ).obj E))) := by
  let : (moduleSheafEquivalence Y Λ).functor.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive.{u + 1, u, u + 1, u + 1}
      Y.smallEtaleTopology Λ
  let EN : (moduleAnnihilated Y Λ n).FullSubcategory :=
    ⟨(moduleSheafEquivalence Y Λ).functor.obj E, by
      change n • 𝟙 ((moduleSheafEquivalence Y Λ).functor.obj E) = 0
      let A := (moduleSheafEquivalence Y Λ).functor
      exact (A.map_nsmul.trans (congrArg (fun a => n • a) (A.map_id E))).symm.trans
        ((congrArg A.map hE).trans (A.map_zero E E))⟩
  exact (moduleSheafEquivalence S Λ).inverse.mapIso
    (((moduleAnnihilatedFiniteCompactificationIso f Λ g C D n hn q).app EN) ≪≫
      (moduleCompactificationHigherDirectImage C.toCompactification Λ q).mapIso
        (moduleDirectImageValuedNativeObjIso g Λ E))

/-- A finite-etale cover of rank prime to the coefficient annihilator descends
actual compactified higher-image constructibility via the original trace retract. -/
theorem moduleCompactificationHigherImage_isConstructible_of_finiteEtale_coprime
    [IsNoetherianRing Λ] (C : Hom.DenseCompactification f) (T : Scheme.FiniteEtale X)
    [HasDerivedCategory.{wY} (ModuleSheaf T.obj.left Λ)]
    [tModels : ∀ D : Hom.DenseCompactification T.obj.hom,
      HasDerivedCategory.{wG} (ModuleSheaf D.Xbar Λ)]
    [tfModels : ∀ D : Hom.DenseCompactification (T.obj.hom ≫ f),
      HasDerivedCategory.{wGF} (ModuleSheaf D.Xbar Λ)]
    (D : Hom.DenseCompactification (T.obj.hom ≫ f))
    (r : ℕ) (hr : ∀ x : X, T.obj.hom.finrank x = r)
    (F : ModuleValuedSheaf X Λ) (n : ℕ) (hn : 0 < n) (hcop : r.Coprime n)
    (hF : n • 𝟙 F = 0) (q : ℕ)
    (hT : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage D.toCompactification Λ q).obj
          ((moduleSheafEquivalence T.obj.left Λ).functor.obj
            ((Constructible.Modules.moduleInverseImage Λ T.obj.hom).obj F))))) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C.toCompactification Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj F))) := by
  let P : ObjectProperty (ModuleValuedSheaf S Λ) := Constructible.Modules.IsConstructible
  let H := (moduleSheafEquivalence X Λ).functor ⋙
    moduleCompactificationHigherDirectImage C.toCompactification Λ q ⋙
      (moduleSheafEquivalence S Λ).inverse
  obtain ⟨tr, htr⟩ := exists_finiteEtale_moduleSheafTrace Λ T r hr
  apply P.prop_obj_of_coprime_trace
    ((Constructible.Modules.moduleImageAdjunction Λ T.obj.hom).unit.app F)
    (tr.app F) r n (htr F) hcop hF H
  have hE : n • 𝟙 ((Constructible.Modules.moduleInverseImage Λ T.obj.hom).obj F) = 0 := by
    let Q := Constructible.Modules.moduleInverseImage Λ T.obj.hom
    let : (Constructible.Modules.moduleEtaleRestriction Λ T.obj.hom).Additive :=
      { map_add := by intro A B a b; rfl }
    let : Q.Additive := Functor.additive_of_iso
      (Constructible.Modules.moduleInverseImageEtaleIso Λ T.obj.hom).symm
    exact (Q.map_nsmul.trans (congrArg (fun a => n • a) (Q.map_id F))).symm.trans
      ((congrArg Q.map hF).trans (Q.map_zero F F))
  exact (Constructible.Modules.isConstructible_iff_of_iso
    (finiteModuleCompactificationValuedCompObjIso f T.obj.hom Λ C D
      ((Constructible.Modules.moduleInverseImage Λ T.obj.hom).obj F) n hn hE q)).mp hT

end AlgebraicGeometry.Scheme.EtaleCohomology
