/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.CoverConservativity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureKernels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitInverseImage
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantPresentation
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnitValued
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureCokernels
public import Aglib.Algebra.Module.ZMod.FiniteDual

/-!
# Native finite free presentations and copresentations on finite étale covers

The actual lower-shriek free epimorphism and its original coefficient maps
are constructed in this coefficient owner. In the opposite
direction, finite lifted-ZMod module values embed in finite powers of the
original regular module by their original linear dual. The original right
adjunction unit then gives a native cofree monomorphism on the same finite
connected Galois trivializing cover. No curve, field, Ext, trace or duality
perfectness hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace ModuleCat

/-- The native lifted-ZMod dual separates points of a finite module. Full
additive forgetting lifts each separating original ZMod functional back to
the original lifted coefficient module. -/
private theorem uLiftZMod_dual_eval_injective (n : ℕ) (hn : 0 < n)
    (M : ModuleCat.{v} (ULift.{v} (ZMod n))) [Finite M] :
    Function.Injective (Module.Dual.eval (ULift.{v} (ZMod n)) M) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Λ := ULift.{v} (ZMod n)
  have hkill (x : M) : n • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := Λ)]
    have hz : (n : Λ) = 0 := by
      apply ULift.ext
      change (n : ZMod n) = 0
      exact ZMod.natCast_self n
    rw [hz, zero_smul]
  let : Module (ZMod n) M := AddCommGroup.zmodModule hkill
  let Q := forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}
  let : Q.Full := ModuleCat.uLiftZMod_forget₂_full n
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  by_contra hne
  obtain ⟨f, hf⟩ := ZMod.exists_dual_apply_ne_zero n M hne
  let fA : M →+ ZMod n := LinearMap.toAddMonoidHom f
  let a : M →+ Λ :=
    { toFun := fun y => ULift.up (fA y)
      map_zero' := by apply ULift.ext; exact fA.map_zero
      map_add' := fun y z => by apply ULift.ext; exact fA.map_add y z }
  let aA : Q.obj M ⟶ Q.obj (ModuleCat.of Λ Λ) := AddCommGrpCat.ofHom a
  let g : M ⟶ ModuleCat.of Λ Λ := Q.preimage aA
  have hg : g.hom x = a x := ConcreteCategory.congr_hom (Q.map_preimage aA) x
  have hzero : g.hom x = 0 := DFunLike.congr_fun hx g.hom
  apply hf
  have hz : a x = 0 := hg.symm.trans hzero
  exact congrArg ULift.down hz

/-- A finite module over the original lifted positive ZMod ring embeds in a
finite free module. The map is finite coordinate evaluation on its native
linear dual; no freeness of the original value is assumed. -/
theorem exists_mono_finPi_uLiftZMod (n : ℕ) (hn : 0 < n)
    (M : ModuleCat.{v} (ULift.{v} (ZMod n))) [Finite M] :
    ∃ (m : ℕ) (i : M ⟶ ModuleCat.of (ULift.{v} (ZMod n))
      (Fin m → ULift.{v} (ZMod n))), Mono i := by
  classical
  let Λ := ULift.{v} (ZMod n)
  by_cases h1 : n = 1
  · have hzero : IsZero M := (IsZero.iff_id_eq_zero M).mpr (by
      ext x
      change x = 0
      have hz : (1 : Λ) = 0 := by
        apply ULift.ext
        change (1 : ZMod n) = 0
        rw [h1]
        exact Subsingleton.elim _ _
      simpa only [one_smul, zero_smul] using congrArg (fun a : Λ => a • x) hz)
    let : Subsingleton M := ModuleCat.subsingleton_of_isZero hzero
    refine ⟨0, 0, (ModuleCat.mono_iff_injective _).mpr ?_⟩
    exact fun x y _ => Subsingleton.elim x y
  · let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let I := Module.Dual Λ M
    let : Finite I := Finite.of_injective (fun f : I => (f : M → Λ)) DFunLike.coe_injective
    let : Fintype I := Fintype.ofFinite I
    let e := (Fintype.equivFin I).symm
    let i : M →ₗ[Λ] (Fin (Fintype.card I) → Λ) := LinearMap.pi (fun j => e j)
    refine ⟨Fintype.card I, ModuleCat.ofHom i, (ModuleCat.mono_iff_injective _).mpr ?_⟩
    intro x y hxy
    apply uLiftZMod_dual_eval_injective n hn M
    apply LinearMap.ext
    intro f
    have h := congrFun hxy ((Fintype.equivFin I) f)
    change i x ((Fintype.equivFin I) f) = i y ((Fintype.equivFin I) f) at h
    change f x = f y
    simpa only [i, LinearMap.pi_apply, e, Equiv.symm_apply_apply] using h

end ModuleCat

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules ModuleCat.Sheaf.hasSheafify
  Abelian.hasFiniteBiproducts
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

local instance moduleSheaf_hasFiniteBiproducts (U : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] : HasFiniteBiproducts (ModuleSheaf U Λ) :=
  HasFiniteBiproducts.of_hasFiniteProducts


section ConstantPowers

variable (U : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

local instance moduleUnitConstantLinearMap_locallySurjective :
    Presheaf.IsLocallySurjective U.smallEtaleTopology
      (ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap U.smallEtaleTopology Λ) := by
  exact ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_isLocallySurjective
    U.smallEtaleTopology Λ

local instance moduleUnitConstantLinearMap_locallyInjective :
    Presheaf.IsLocallyInjective U.smallEtaleTopology
      (ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap U.smallEtaleTopology Λ) := by
  exact ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_isLocallyInjective
    U.smallEtaleTopology Λ

/-- The original locally bijective constant-unit map gives an actual
module-valued constant presentation of the original native unit. -/
def moduleUnitConstantValuedIso :
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ≅
      (moduleSheafEquivalence U Λ).inverse.obj (moduleUnit U Λ) :=
  @ModuleCat.Sheaf.constantPresentationIso.{u + 1, u, u + 1}
    U.Etale inferInstance U.smallEtaleTopology Λ inferInstance (ModuleCat.of Λ Λ)
    ((moduleSheafEquivalence U Λ).inverse.obj (moduleUnit U Λ))
    (ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap U.smallEtaleTopology Λ)
    (moduleUnitConstantLinearMap_locallySurjective U Λ)
    (moduleUnitConstantLinearMap_locallyInjective U Λ)

/-- The entire presentation retains the original constant-ring unit map. -/
theorem moduleUnitConstantValuedIso_unit :
    ModuleCat.Sheaf.constantUnit U.smallEtaleTopology (ModuleCat.of Λ Λ) ≫
        (moduleUnitConstantValuedIso U Λ).hom.hom =
      ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap U.smallEtaleTopology Λ :=
  @ModuleCat.Sheaf.constantPresentationIso_unit.{u + 1, u, u + 1}
    U.Etale inferInstance U.smallEtaleTopology Λ inferInstance (ModuleCat.of Λ Λ)
    ((moduleSheafEquivalence U Λ).inverse.obj (moduleUnit U Λ))
    (ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap U.smallEtaleTopology Λ)
    (moduleUnitConstantLinearMap_locallySurjective U Λ)
    (moduleUnitConstantLinearMap_locallyInjective U Λ)

/-- The same constant presentation, through the original coefficient
equivalence and its original counit, is the native constant unit isomorphism. -/
def moduleUnitConstantIso :
    (moduleSheafEquivalence U Λ).functor.obj
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≅
      moduleUnit U Λ :=
  (moduleSheafEquivalence U Λ).functor.mapIso (moduleUnitConstantValuedIso U Λ) ≪≫
    (moduleSheafEquivalence U Λ).counitIso.app (moduleUnit U Λ)

/-- A finite biproduct of original native units is the original constant free
module, through the actual biproduct and coefficient-equivalence maps. -/
def moduleFiniteFreeConstantIso (m : ℕ) :
    (⨁ fun _ : Fin m => moduleUnit U Λ) ≅
      (moduleSheafEquivalence U Λ).functor.obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin m → Λ))) := by
  let : (moduleSheafEquivalence U Λ).functor.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive U.smallEtaleTopology Λ
  let T := constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (moduleSheafEquivalence U Λ).functor
  let : T.Additive := inferInstance
  exact biproduct.mapIso (fun _ : Fin m => (moduleUnitConstantIso U Λ).symm) ≪≫
    (Functor.mapBiproduct T (fun _ : Fin m => ModuleCat.of Λ Λ)).symm ≪≫
      T.mapIso (ModuleCat.biproductIsoPi (fun _ : Fin m => ModuleCat.of Λ Λ))

end ConstantPowers

section LocallyConstantCoefficients

variable (U : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- The original native unit is finite-type locally constant through its
actual original constant-module presentation. -/
theorem moduleUnit_isFiniteTypeLocallyConstant :
    Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj (moduleUnit U Λ)) :=
  (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso
    (moduleUnitConstantValuedIso U Λ)).mp
      (Constructible.Modules.isFiniteTypeLocallyConstant_constant U (ModuleCat.of Λ Λ))

/-- Finite biproducts of the actual native units are finite-type locally
constant, retaining the same coefficient equivalence and free-module value. -/
theorem moduleUnitBiproduct_isFiniteTypeLocallyConstant (m : ℕ) :
    Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj (⨁ fun _ : Fin m => moduleUnit U Λ)) := by
  let E := moduleSheafEquivalence U Λ
  let C := constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let e := E.inverse.mapIso (moduleFiniteFreeConstantIso U Λ m) ≪≫
    E.unitIso.symm.app (C.obj (ModuleCat.of Λ (Fin m → Λ)))
  exact (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso e).mpr
    (Constructible.Modules.isFiniteTypeLocallyConstant_constant U
      (ModuleCat.of Λ (Fin m → Λ)))

/-- The actual native kernel remains finite-LCC over a Noetherian coefficient
ring when both original source and target are finite-LCC. -/
theorem moduleKernel_isFiniteTypeLocallyConstant [IsNoetherianRing Λ]
    {F G : ModuleSheaf U Λ} (a : F ⟶ G)
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj F))
    (hG : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj G)) :
    Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj (kernel a)) := by
  let E := (moduleSheafEquivalence U Λ).inverse
  exact (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso
    (PreservesKernel.iso E a)).mpr
      (Constructible.Modules.isFiniteTypeLocallyConstant_kernel (E.map a) hF hG)

end LocallyConstantCoefficients
section SurjectiveEtale

variable {V U : Scheme.{u}} (f : V ⟶ U) [Etale f]
  (Λ : Type (u + 1)) [CommRing Λ]

/-- The native ringed-module inverse image is faithful on a surjective étale
map, through the existing original module-valued comparison. -/
theorem moduleInverseImage_faithful_of_surjective [Surjective f] :
    (moduleInverseImage f Λ).Faithful := by
  let : (moduleValuedInverseImage f Λ).Faithful :=
    Constructible.Modules.moduleInverseImage_faithful_of_surjective Λ f
  exact Functor.Faithful.of_iso (moduleInverseImageTransportIso f Λ).symm

/-- The original lower-shriek counit is epi for a surjective étale map.
This uses the original adjunction and faithful inverse image, without any
comparison between lower shriek and finite direct image. -/
theorem moduleLowerShriek_counit_epi_of_surjective [Surjective f]
    (M : ModuleSheaf U Λ) : Epi ((moduleLowerShriekAdjunction f Λ).counit.app M) := by
  let := moduleInverseImage_faithful_of_surjective f Λ
  exact Adjunction.counit_epi_of_R_faithful (moduleLowerShriekAdjunction f Λ) M

end SurjectiveEtale

section UnitCounit

variable {V U : Scheme.{u}} (f : V ⟶ U) [Etale f] (n : ℕ)

/-- The original lower-shriek counit with its original constant-unit source
comparison. It is defined before taking any cohomology group. -/
def moduleUnitLowerShriekCounit :
    (moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit V (ULift.{u + 1} (ZMod n))) ⟶ moduleUnit U (ULift.{u + 1} (ZMod n)) :=
  (moduleLowerShriek f (ULift.{u + 1} (ZMod n))).map (moduleUnitInverseImageIso f n).inv ≫
    (moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).counit.app
      (moduleUnit U (ULift.{u + 1} (ZMod n)))

/-- The same original unit-normalized counit is epi on a surjective étale cover. -/
theorem moduleUnitLowerShriekCounit_epi [Surjective f] : Epi (moduleUnitLowerShriekCounit f n) := by
  let := moduleLowerShriek_counit_epi_of_surjective f (ULift.{u + 1} (ZMod n))
    (moduleUnit U (ULift.{u + 1} (ZMod n)))
  change Epi (_ ≫ _)
  infer_instance

end UnitCounit

section FinitePresentation

variable {U : Scheme.{u}} [ConnectedSpace U] (n : ℕ) (hn : 0 < n)

include hn in
/-- Every actual finite-LCC lifted-ZMod coefficient receives an actual epi
from the lower shriek of a finite biproduct of native units on a constructed
connected Galois finite étale cover. The finite coefficient itself need not be free. -/
theorem exists_galois_unit_biproduct_lowerShriek_epi
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    ∃ Y : Scheme.FiniteEtale U,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∃ (m : ℕ) (a : (moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))) ⟶ F), Epi a := by
  let Λ := ULift.{u + 1} (ZMod n)
  let T := Constructible.Modules.uLiftZModGaloisCoverConstantTrivialization n hn
    ((moduleSheafEquivalence U Λ).inverse.obj F) hF
  let Y := T.cover
  let : Surjective Y.obj.hom := T.surjective_cover
  let : Module.Finite Λ T.value := T.finite_value
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' Λ T.value
  let qM : ModuleCat.of Λ (Fin m → Λ) ⟶ T.value := ModuleCat.ofHom q
  let : Epi qM := (ModuleCat.epi_iff_surjective qM).mpr hq
  let E := moduleSheafEquivalence Y.obj.left Λ
  let C := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let : C.IsLeftAdjoint :=
    (constantSheafAdj Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (etaleTerminalIsTerminal Y.obj.left)).isLeftAdjoint
  let pullIso : (moduleInverseImage Y.obj.hom Λ).obj F ≅ E.functor.obj (C.obj T.value) :=
    (moduleInverseImageTransportIso Y.obj.hom Λ).app F ≪≫ E.functor.mapIso T.iso
  let g : (⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ) ⟶
      (moduleInverseImage Y.obj.hom Λ).obj F :=
    (moduleFiniteFreeConstantIso Y.obj.left Λ m).hom ≫ E.functor.map (C.map qM) ≫ pullIso.inv
  let : Epi g := by
    change Epi (_ ≫ _ ≫ _)
    infer_instance
  let := moduleLowerShriek_counit_epi_of_surjective Y.obj.hom Λ F
  let a := (moduleLowerShriek Y.obj.hom Λ).map g ≫
    (moduleLowerShriekAdjunction Y.obj.hom Λ).counit.app F
  refine ⟨Y, T.galois_cover, T.connected_cover, T.surjective_cover, m, a, ?_⟩
  change Epi (_ ≫ _)
  infer_instance

end FinitePresentation

variable {U : Scheme.{u}} (n : ℕ) (hn : 0 < n)

/-- The unit of the original right image adjunction is monic on a surjective
étale cover. This is faithful inverse image applied to the original unit. -/
theorem moduleInverseImageAdjunction_unit_mono_of_surjective
    {V : Scheme.{u}} (f : V ⟶ U) [Etale f] [Surjective f]
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) :
    Mono ((moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).unit.app F) := by
  let := moduleInverseImage_faithful_of_surjective f (ULift.{u + 1} (ZMod n))
  exact Adjunction.unit_mono_of_L_faithful
    (moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))) F

include hn in
/-- Every original finite locally constant lifted-ZMod coefficient embeds in
the direct image of finite powers of the native unit on a constructed actual
connected Galois finite étale cover. Its degree need not be invertible. -/
theorem exists_galois_unit_biproduct_directImage_mono [ConnectedSpace U]
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    ∃ Y : Scheme.FiniteEtale U,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∃ (m : ℕ) (a : F ⟶ (moduleDirectImage Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))), Mono a := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Λ := ULift.{u + 1} (ZMod n)
  let T := Constructible.Modules.uLiftZModGaloisCoverConstantTrivialization n hn
    ((moduleSheafEquivalence U Λ).inverse.obj F) hF
  let Y := T.cover
  let : Surjective Y.obj.hom := T.surjective_cover
  let : Module.Finite Λ T.value := T.finite_value
  let : Finite T.value := Module.finite_of_finite Λ
  obtain ⟨m, i, hi⟩ := ModuleCat.exists_mono_finPi_uLiftZMod n hn T.value
  let : Mono i := hi
  let E := moduleSheafEquivalence Y.obj.left Λ
  let C := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let : PreservesFiniteLimits C :=
    Limits.comp_preservesFiniteLimits (Functor.const Y.obj.left.Etaleᵒᵖ)
      (presheafToSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let pullIso : (moduleInverseImage Y.obj.hom Λ).obj F ≅ E.functor.obj (C.obj T.value) :=
    (moduleInverseImageTransportIso Y.obj.hom Λ).app F ≪≫ E.functor.mapIso T.iso
  let g : (moduleInverseImage Y.obj.hom Λ).obj F ⟶
      (⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ) :=
    pullIso.hom ≫ E.functor.map (C.map i) ≫ (moduleFiniteFreeConstantIso Y.obj.left Λ m).inv
  let : Mono g := by
    change Mono (_ ≫ _ ≫ _)
    infer_instance
  let := moduleInverseImageAdjunction_unit_mono_of_surjective n Y.obj.hom F
  let a := (moduleInverseImageAdjunction Y.obj.hom Λ).unit.app F ≫
    (moduleDirectImage Y.obj.hom Λ).map g
  refine ⟨Y, T.galois_cover, T.connected_cover, T.surjective_cover, m, a, ?_⟩
  change Mono (_ ≫ _)
  infer_instance

/-- Finite étale direct image preserves native finite local constancy through
the original coefficient equivalence and existing module-valued theorem. -/
theorem moduleDirectImage_isFiniteTypeLocallyConstant
    (Λ : Type (u + 1)) [CommRing Λ] {V : Scheme.{u}}
    (f : V ⟶ U) [IsFinite f] [Etale f]
    (P : ModuleSheaf V Λ)
    (hP : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence V Λ).inverse.obj P)) :
    Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj ((moduleDirectImage f Λ).obj P)) :=
  (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso
    ((moduleDirectImageComparison f Λ).app P)).mpr
      (Constructible.Modules.isFiniteTypeLocallyConstant_finiteEtaleDirectImage f hP)

/-- Native cokernels of finite local systems retain their actual finite local
constancy over a Noetherian coefficient ring. -/
theorem moduleCokernel_isFiniteTypeLocallyConstant
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    {F G : ModuleSheaf U Λ} (a : F ⟶ G)
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj F))
    (hG : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj G)) :
    Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj (cokernel a)) := by
  let E := (moduleSheafEquivalence U Λ).inverse
  exact (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso
    (PreservesCokernel.iso E a)).mpr
      (Constructible.Modules.isFiniteTypeLocallyConstant_cokernel (E.map a) hF hG)

end AlgebraicGeometry.Scheme.EtaleCohomology
