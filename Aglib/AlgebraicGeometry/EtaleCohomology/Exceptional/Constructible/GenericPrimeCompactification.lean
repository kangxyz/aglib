/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.GaloisRawCompactification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericTrivializationConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstantValueAnnihilator

/-! # Actual generic compactified finiteness for prime-killed coefficients

For a constructible module on an integral source, its actual dense affine
Galois trivialization is produced internally. The proved Galois compactified
producer gives finiteness over the original possibly infinite coefficient
ring. No finite underlying group or supplied generic trivialization appears
in the conclusion. This is a generic-open producer, not the global support
induction or the arbitrary positive-annihilator theorem.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Over any Noetherian coefficient ring, every original
prime-killed constructible module on an integral source has a genuine dense affine open
whose compactified higher images are constructible in every natural degree. -/
theorem exists_dense_open_moduleCompactificationHigherImage_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] [IsIntegral X]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    (p : ℕ) [Fact p.Prime]
    (F : ModuleValuedSheaf X Λ) (hF : Constructible.Modules.IsConstructible F)
    (hFkill : p • 𝟙 F = 0) :
    ∃ (U : Scheme.{u}) (j : U ⟶ X),
      IsAffine U ∧ IsOpenImmersion j ∧ IsDominant j ∧ ConnectedSpace U ∧
      ∀ (C : Hom.Compactification (j ≫ f)) (q : ℕ),
        Constructible.Modules.IsConstructible
          ((moduleSheafEquivalence S Λ).inverse.obj
            ((moduleCompactificationHigherDirectImage C Λ q).obj
              ((moduleSheafEquivalence U Λ).functor.obj
                ((Constructible.Modules.moduleInverseImage Λ j).obj F)))) := by
  let t := Constructible.Modules.denseGaloisConstantTrivializationOfConstructible F hF
  let : IsAffine t.base := t.affine_base
  let : IsOpenImmersion t.inclusion := t.open_inclusion
  let : IsDominant t.inclusion := t.dense_inclusion
  let : ConnectedSpace t.base := t.connected_base
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let : PreGaloisCategory.IsGalois t.cover := t.galois_cover
  let : ConnectedSpace t.cover.obj.left := t.connected_cover
  let : Surjective t.cover.obj.hom := t.surjective_cover
  let : CompactSpace t.cover.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace t.cover.obj.hom
  let : QuasiSeparatedSpace t.cover.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated t.cover.obj.hom
  let : Module.Finite Λ t.value := t.finite_value
  let E := (Constructible.Modules.moduleInverseImage Λ t.inclusion).obj F
  let e : (Constructible.Modules.moduleInverseImage Λ t.cover.obj.hom).obj E ≅
      (constantSheaf t.cover.obj.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        t.value :=
    ((Constructible.Modules.moduleInverseImageComp Λ t.inclusion t.cover.obj.hom).app F).symm ≪≫
      t.iso
  have hkill : ∀ x : t.value, p • x = 0 :=
    Constructible.Modules.value_annihilator_of_etale_trivialization Λ
      (t.cover.obj.hom ≫ t.inclusion) F t.value p hFkill t.iso
  let : HasDerivedCategory.{u + 2} (ModuleSheaf t.base Λ) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (ModuleSheaf S Λ) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (AbelianSheaf.{u, u + 1} S) :=
    HasDerivedCategory.standard _
  refine ⟨t.base, t.inclusion, t.affine_base, t.open_inclusion, t.dense_inclusion,
    t.connected_base, ?_⟩
  intro C q
  let : HasDerivedCategory.{u + 2} (ModuleSheaf C.Xbar Λ) := HasDerivedCategory.standard _
  exact galoisModuleRawCompactificationHigherImage_isConstructible
    (t.inclusion ≫ f) C Λ p t.cover E t.value hkill e q

end AlgebraicGeometry.Scheme.EtaleCohomology
