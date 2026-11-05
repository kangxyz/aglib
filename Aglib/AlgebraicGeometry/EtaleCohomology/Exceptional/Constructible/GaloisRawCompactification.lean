/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.GaloisCompactification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.AnnihilatedDensification
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive

/-! # Galois-trivialized finiteness for an original nondense compactification

Schematic densification and the original annihilated higher-image comparison
remove the density restriction on the supplied compactification. The original
source, target and ambient module objects and derived worlds are retained.
Only the newly produced dense models use the standard realization.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wM wS wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Prime-killed Galois-trivialized finite-type coefficients have constructible
higher images for every supplied actual compactification, even when its open
immersion is not dense. No finite underlying additive group is assumed. -/
theorem galoisModuleRawCompactificationHigherImage_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] [ConnectedSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
    (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
    (p : ℕ) [Fact p.Prime]
    (Y : Scheme.FiniteEtale X) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (F : ModuleValuedSheaf X Λ) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0)
    (t : (Constructible.Modules.moduleInverseImage Λ Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj F))) := by
  let : IsLocallyNoetherian C.Xbar := LocallyOfFiniteType.isLocallyNoetherian C.p
  let : CompactSpace C.Xbar := QuasiCompact.compactSpace_of_compactSpace C.p
  let : IsNoetherian C.Xbar := ⟨⟩
  let : ∀ D : Hom.DenseCompactification f,
      HasDerivedCategory.{u + 2} (ModuleSheaf D.Xbar Λ) :=
    fun _ => HasDerivedCategory.standard _
  let : (moduleSheafEquivalence X Λ).functor.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive.{u + 1, u, u + 1, u + 1}
      X.smallEtaleTopology Λ
  have hF : p • 𝟙 F = 0 :=
    moduleSheaf_nsmul_id_eq_zero_of_trivialization Λ Y.obj.hom F M p hM t
  let E := (moduleSheafEquivalence X Λ).functor
  have hG : p • 𝟙 (E.obj F) = 0 :=
    (E.map_nsmul.trans (congrArg (fun a => p • a) (E.map_id F))).symm.trans
      ((congrArg E.map hF).trans (E.map_zero F F))
  let G : (moduleAnnihilated X Λ p).FullSubcategory := ⟨E.obj F, hG⟩
  let e := (moduleAnnihilatedCompactificationDensificationIso C Λ p
    (Nat.Prime.pos (Fact.out)) q).app G
  apply (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence S Λ).inverse.mapIso e)).mpr
  exact galoisModuleCompactificationHigherImage_isConstructible
    f Λ (Hom.Compactification.densify C) p Y F M hM t q

end AlgebraicGeometry.Scheme.EtaleCohomology
