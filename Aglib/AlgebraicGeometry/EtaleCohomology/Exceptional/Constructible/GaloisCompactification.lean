/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.PGroupCompactification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FiniteEtaleCompactificationDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.FiniteEtaleDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSylowCover

/-! # Galois trivializations for genuinely compactified higher images

The original Sylow intermediate cover, p-group producer, and finite exceptional
composition comparison prove constructibility for nonproper sources as well.
Only new intermediate schemes and their compactifications use standard models.
The supplied source, target, and outer compactification models are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wM wMS wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Any actual prime-killed finite-type Galois trivialization gives constructible
higher images for the supplied genuine compactification of a possibly nonproper
morphism. No finite underlying group or properness of the source map is assumed. -/
theorem galoisModuleCompactificationHigherImage_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] [ConnectedSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
    [fModels : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    (C : Hom.DenseCompactification f)
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
        ((moduleCompactificationHigherDirectImage C.toCompactification Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj F))) := by
  let P : Sylow p (Aut Y) := Classical.choice inferInstance
  let Z := Scheme.FiniteEtale.galoisSubgroupQuotient Y P.toSubgroup
  let V := Scheme.FiniteEtale.galoisSubgroupRelative Y P.toSubgroup
  let E := (Constructible.Modules.moduleInverseImage Λ Z.obj.hom).obj F
  let : ConnectedSpace Z.obj.left := inferInstance
  let : PreGaloisCategory.IsGalois V :=
    Scheme.FiniteEtale.galoisSubgroupRelative_isGalois Y P.toSubgroup
  let : Surjective V.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupRelative_surjective Y P.toSubgroup
  let : ConnectedSpace V.obj.left := inferInstanceAs (ConnectedSpace Y.obj.left)
  let : CompactSpace V.obj.left := inferInstanceAs (CompactSpace Y.obj.left)
  let : QuasiSeparatedSpace V.obj.left := inferInstanceAs (QuasiSeparatedSpace Y.obj.left)
  have htriangle : V.obj.hom ≫ Z.obj.hom = Y.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupQuotientπ_structure Y P.toSubgroup
  let t' : (Constructible.Modules.moduleInverseImage Λ V.obj.hom).obj E ≅
      (constantSheaf V.obj.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
    ((Constructible.Modules.moduleInverseImageComp Λ Z.obj.hom V.obj.hom).app F).symm ≪≫
      eqToIso (congrArg (fun a => (Constructible.Modules.moduleInverseImage Λ a).obj F)
        htriangle) ≪≫ t
  let : HasDerivedCategory.{u + 2} (ModuleSheaf Z.obj.left Λ) :=
    HasDerivedCategory.standard _
  let : ∀ D : Hom.DenseCompactification Z.obj.hom,
      HasDerivedCategory.{u + 2} (ModuleSheaf D.Xbar Λ) :=
    fun _ => HasDerivedCategory.standard _
  let : ∀ D : Hom.DenseCompactification (Z.obj.hom ≫ f),
      HasDerivedCategory.{u + 2} (ModuleSheaf D.Xbar Λ) :=
    fun _ => HasDerivedCategory.standard _
  let D := moduleExceptionalCompactification (Z.obj.hom ≫ f)
  have hZ : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage D.toCompactification Λ q).obj
          ((moduleSheafEquivalence Z.obj.left Λ).functor.obj E))) :=
    pGroupModuleCompactificationHigherImage_isConstructible.{u, u + 2, wMS, wAS}
      D.toCompactification Λ p V (Scheme.FiniteEtale.galoisSylowRelative_isPGroup Y P)
      E M hM t' q
  exact moduleCompactificationHigherImage_isConstructible_of_finiteEtale_coprime
    f Λ C Z D P.toSubgroup.index
    (Scheme.FiniteEtale.galoisSubgroupQuotient_finrank Y P.toSubgroup)
    F p (Nat.Prime.pos (Fact.out)) (Scheme.FiniteEtale.galoisSylow_index_coprime Y P)
    (moduleSheaf_nsmul_id_eq_zero_of_trivialization Λ Y.obj.hom F M p hM t) q hZ

end AlgebraicGeometry.Scheme.EtaleCohomology
