/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.ConstructibleAnnihilator
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericTrivializationConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstantValueTorsion

/-! # Generic compactified finiteness for internally torsion coefficients

The actual dense Galois trivialization has finite-type value. Internal torsion
and qcqs continuity supply a positive annihilator of that value, which descends
to the original open restriction. No annihilator is supplied by the caller.
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

/-- Internally torsion constructible coefficients admit an actual dense affine
open with constructible compactified higher images in all natural degrees. -/
theorem exists_dense_open_moduleCompactificationHigherImage_torsion_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] [IsIntegral X]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    (F : ModuleValuedSheaf X Λ) (hF : Constructible.Modules.IsConstructible F)
    (hFt : Sheaf.IsTorsion ((Constructible.Modules.moduleUnderlying Λ X).obj F)) :
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
  have hPull := IsTorsion.inverseImage (t.cover.obj.hom ≫ t.inclusion) hFt
  have hVal := hPull.of_mono
    ((Constructible.Modules.moduleInverseImageUnderlyingIso Λ
      (t.cover.obj.hom ≫ t.inclusion)).hom.app F)
  have hConstant := hVal.of_mono
    ((Constructible.Modules.moduleUnderlying Λ t.cover.obj.left).map t.iso.inv)
  obtain ⟨n, hn, hkill⟩ :=
    Constructible.Modules.constantModuleValue_exists_positive_annihilator Λ
      t.cover.obj.left t.value hConstant
  have hEkill : n • 𝟙 E = 0 :=
    moduleSheaf_nsmul_id_eq_zero_of_trivialization Λ t.cover.obj.hom E t.value n hkill e
  have hE : Constructible.Modules.IsConstructible E :=
    Constructible.Modules.isConstructible_pullback t.inclusion hF
  refine ⟨t.base, t.inclusion, t.affine_base, t.open_inclusion, t.dense_inclusion,
    t.connected_base, ?_⟩
  intro C q
  exact moduleCompactificationHigherImage_annihilated_isConstructible
    (t.inclusion ≫ f) C Λ n hn E hE hEkill q

end AlgebraicGeometry.Scheme.EtaleCohomology
