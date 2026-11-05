/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.ConstantCompactification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PGroupModuleSheaves
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage

/-! # Nonproper p-group trivializations and actual compactified higher images

The exact input is the original coefficient equivalence followed by actual
lower shriek into the supplied compactification. Invariant-section subobjects
and actual cokernels feed the same generic right-derived producer. The open
source is never asserted proper.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wM wS wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Actual p-group trivializations give constructibility for the original
compactified higher image even when the source morphism is not proper. -/
theorem pGroupModuleCompactificationHigherImage_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] [ConnectedSpace X]
    {f : X ⟶ S} (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
    (p : ℕ) [Fact p.Prime]
    (Y : Scheme.FiniteEtale X) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (hY : IsPGroup p (Aut Y))
    (F : ModuleValuedSheaf X Λ) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0)
    (t : (Constructible.Modules.moduleInverseImage Λ Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj F))) := by
  let : (moduleSheafEquivalence X Λ).functor.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive.{u + 1, u, u + 1, u + 1}
      X.smallEtaleTopology Λ
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let K := (moduleSheafEquivalence X Λ).functor ⋙ moduleLowerShriek C.j Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  apply Constructible.Modules.property_of_pGroup_trivialization Y p hY
    (fun E => ∀ k : ℕ, P (((moduleDirectImage C.p Λ).rightDerived k).obj (K.obj E)))
    ?_ ?_ ?_ F M hM t q
  · intro N _ hN k
    exact constantTorsionModuleCompactificationHigherImage_isConstructible C Λ p
      (Nat.Prime.pos (Fact.out)) N hN k
  · intro E E' e hE k
    exact P.prop_of_iso (((moduleDirectImage C.p Λ).rightDerived k).mapIso
      (K.mapIso e)) (hE k)
  · intro T hT h₁ h₃ k
    exact (moduleDirectImage C.p Λ).rightDerived_property_of_shortExact P
      (T.map K) (hT.map_of_exact K) h₁ h₃ k

end AlgebraicGeometry.Scheme.EtaleCohomology
