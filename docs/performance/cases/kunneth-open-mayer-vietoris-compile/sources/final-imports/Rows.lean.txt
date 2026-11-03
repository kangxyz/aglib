/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpen
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris.LinearAlgebra
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars.Zero
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The original structural-linear mixed-open Mayer–Vietoris rows -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

namespace KunnethOpenMayerVietoris

/-- The original structural-linear cohomology module on one open. -/
abbrev structureOpenModule (T : FScheme k) (U : T.left.Opens) (n : ℕ) :
    ModuleCat.{u + 1} k :=
  (moduleHPrimePresheaf T.left (constants T) (SheafOfModules.unit T.left.ringCatSheaf) n).obj
    (op U)

/-- The carrier of the original categorical biproduct in one second degree. -/
abbrev structureOpenMVMiddleFamily (U V : Y.left.Opens) (q : ℕ) : Type (u + 1) :=
  (structureOpenModule Y U q ⊞ structureOpenModule Y V q : ModuleCat.{u + 1} k)

/-- The existing ordinary cohomology module, with its original structural scalar action. -/
def structureOriginalFirstModule (T : FScheme k) (p : ℕ) : ModuleCat.{u + 1} k := by
  letI := AlgebraicGeometry.Scheme.structureCohomologyModule T p
  exact ModuleCat.of k (structureCohomology k T p)

/-- The original native restriction pair, viewed as a linear map. -/
def structureOpenMVFirst (U V : Y.left.Opens) (q : ℕ) :
    structureOpenCohomology Y (U ⊔ V) q →ₗ[k] structureOpenMVMiddleFamily Y U V q :=
  (moduleMayerVietorisToBiprod Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q).hom

/-- The original native difference map, viewed as a linear map. -/
def structureOpenMVSecond (U V : Y.left.Opens) (q : ℕ) :
    structureOpenMVMiddleFamily Y U V q →ₗ[k] structureOpenCohomology Y (U ⊓ V) q :=
  (moduleMayerVietorisFromBiprod Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q).hom

/-- The original restriction pair through the chosen biproduct comparison. -/
theorem structureOpenMVFirst_value (T : FScheme k) (U V : T.left.Opens)
    (n : ℕ) (x : structureOpenCohomology T (U ⊔ V) n) :
    (ModuleCat.biprodIsoProd (structureOpenModule T U n)
        (structureOpenModule T V n)).hom (structureOpenMVFirst T U V n x) =
      (structureOpenRestriction T (homOfLE le_sup_left) n x,
        structureOpenRestriction T (homOfLE le_sup_right) n x) := by
  exact Kunneth.MayerVietoris.biprodIsoProd_lift_value
    (structureOpenModule T U n) (structureOpenModule T V n)
    (structureOpenModule T (U ⊔ V) n)
    ((moduleHPrimePresheaf T.left (constants T)
      (SheafOfModules.unit T.left.ringCatSheaf) n).map (homOfLE le_sup_left).op)
    ((moduleHPrimePresheaf T.left (constants T)
      (SheafOfModules.unit T.left.ringCatSheaf) n).map (homOfLE le_sup_right).op) x

/-- Extract exactness over the original six arrows before comparing their native carriers. -/
theorem structureOpenMV_exact (U V : Y.left.Opens) (q : ℕ) :
    Function.Exact (structureOpenMVFirst Y U V q) (structureOpenMVSecond Y U V q) ∧
      Function.Exact (structureOpenMVSecond Y U V q)
        (structureOpenMayerVietorisDelta Y U V q) ∧
      Function.Exact (structureOpenMayerVietorisDelta Y U V q)
        (structureOpenMVFirst Y U V (q + 1)) := by
  exact Kunneth.MayerVietoris.functionExact_mk5
    (moduleMayerVietorisToBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (moduleMayerVietorisFromBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (moduleMayerVietorisDelta Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (moduleMayerVietorisToBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V (q + 1))
    (moduleMayerVietorisFromBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V (q + 1))
    (moduleMayerVietorisSequence_exact Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)

/-- Exactness of the first original native Mayer–Vietoris pair. -/
theorem structureOpenMV_exact_first (U V : Y.left.Opens) (q : ℕ) :
    Function.Exact (structureOpenMVFirst Y U V q) (structureOpenMVSecond Y U V q) :=
  (structureOpenMV_exact Y U V q).1

/-- Exactness at the original native intersection cohomology. -/
theorem structureOpenMV_exact_second (U V : Y.left.Opens) (q : ℕ) :
    Function.Exact (structureOpenMVSecond Y U V q)
      (structureOpenMayerVietorisDelta Y U V q) :=
  (structureOpenMV_exact Y U V q).2.1

/-- Exactness after the original native Mayer–Vietoris boundary. -/
theorem structureOpenMV_exact_third (U V : Y.left.Opens) (q : ℕ) :
    Function.Exact (structureOpenMayerVietorisDelta Y U V q)
      (structureOpenMVFirst Y U V (q + 1)) :=
  (structureOpenMV_exact Y U V q).2.2

/-- The original degree-zero native restriction pair is injective. -/
theorem structureOpenMV_first_zero_injective (U V : Y.left.Opens) :
    Function.Injective (structureOpenMVFirst Y U V 0) := by
  let : Mono (moduleMayerVietorisToBiprod Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V 0) :=
    moduleMayerVietorisToBiprod_mono_zero Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The original coordinate tensor restriction-pair map, retaining its two module families. -/
def structureOpenKunnethMVFirst (U V : Y.left.Opens) (n : ℕ) :=
  Kunneth.MayerVietoris.tensorModuleMap (structureOriginalFirstModule X)
    (structureOpenModule Y (U ⊔ V))
    (fun q => (structureOpenModule Y U q ⊞ structureOpenModule Y V q : ModuleCat.{u + 1} k))
    (fun q => moduleMayerVietorisToBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q) n

/-- The original coordinate tensor difference map, with the same original module families. -/
def structureOpenKunnethMVSecond (U V : Y.left.Opens) (n : ℕ) :=
  Kunneth.MayerVietoris.tensorModuleMap (structureOriginalFirstModule X)
    (fun q => (structureOpenModule Y U q ⊞ structureOpenModule Y V q : ModuleCat.{u + 1} k))
    (structureOpenModule Y (U ⊓ V))
    (fun q => moduleMayerVietorisFromBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q) n

/-- Flat first factors preserve the original first exact pair. -/
theorem structureOpenKunnethMV_exact_first (U V : Y.left.Opens) (n : ℕ) :
    Function.Exact (structureOpenKunnethMVFirst X Y U V n)
      (structureOpenKunnethMVSecond X Y U V n) :=
  Kunneth.MayerVietoris.tensorModuleMap_exact (structureOriginalFirstModule X)
    (structureOpenModule Y (U ⊔ V))
    (fun q => (structureOpenModule Y U q ⊞ structureOpenModule Y V q : ModuleCat.{u + 1} k))
    (structureOpenModule Y (U ⊓ V))
    (fun q => moduleMayerVietorisToBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (fun q => moduleMayerVietorisFromBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (fun q => structureOpenMV_exact_first Y U V q) n

/-- The original tensor difference image is the signed boundary kernel. -/
theorem structureOpenKunnethMV_exact_second (U V : Y.left.Opens) (n : ℕ) :
    Function.Exact (structureOpenKunnethMVSecond X Y U V n)
      (Kunneth.MayerVietoris.tensorBoundary (R := k) (structureCohomology k X)
        (fun q => structureOpenMayerVietorisDelta Y U V q) n) :=
  Kunneth.MayerVietoris.tensorModuleMap_boundary_exact (structureOriginalFirstModule X)
    (fun q => (structureOpenModule Y U q ⊞ structureOpenModule Y V q : ModuleCat.{u + 1} k))
    (structureOpenModule Y (U ⊓ V)) (structureOpenModule Y (U ⊔ V))
    (fun q => moduleMayerVietorisFromBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (fun q => moduleMayerVietorisDelta Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (fun q => structureOpenMV_exact_second Y U V q) n

/-- The original signed boundary image is the next restriction-pair kernel. -/
theorem structureOpenKunnethMV_exact_third (U V : Y.left.Opens) (n : ℕ) :
    Function.Exact
      (Kunneth.MayerVietoris.tensorBoundary (R := k) (structureCohomology k X)
        (fun q => structureOpenMayerVietorisDelta Y U V q) n)
      (structureOpenKunnethMVFirst X Y U V (n + 1)) :=
  Kunneth.MayerVietoris.boundary_tensorModuleMap_exact (structureOriginalFirstModule X)
    (structureOpenModule Y (U ⊓ V)) (structureOpenModule Y (U ⊔ V))
    (fun q => (structureOpenModule Y U q ⊞ structureOpenModule Y V q : ModuleCat.{u + 1} k))
    (fun q => moduleMayerVietorisDelta Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (fun q => moduleMayerVietorisToBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (fun q => structureOpenMV_exact_third Y U V q)
    (structureOpenMV_first_zero_injective Y U V) n

/-- Only the native tensor/product and finite-support distributions enter the middle. -/
def structureOpenMVMiddleSourceEquiv (U V : Y.left.Opens) (n : ℕ) :=
  Kunneth.MayerVietoris.tensorModuleBiprodEquiv (structureOriginalFirstModule X)
    (structureOpenModule Y U) (structureOpenModule Y V) n

/-- The two actual mixed maps form the original binary-product middle arrow. -/
def structureOpenMVMiddleMap (U V : Y.left.Opens) (n : ℕ) :=
  (CategoryTheory.Iso.toLinearEquiv (ModuleCat.biprodIsoProd
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n)
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n))).symm.toLinearMap ∘ₗ
    (LinearMap.prodMap (structureOpenKunnethMap X Y U n) (structureOpenKunnethMap X Y V n)) ∘ₗ
      (structureOpenMVMiddleSourceEquiv X Y U V n).toLinearMap

/-- The original middle map is bijective when its two mixed maps are bijective. -/
theorem structureOpenMVMiddleMap_bijective (U V : Y.left.Opens) (n : ℕ)
    (hU : Function.Bijective (structureOpenKunnethMap X Y U n))
    (hV : Function.Bijective (structureOpenKunnethMap X Y V n)) :
    Function.Bijective (structureOpenMVMiddleMap X Y U V n) := by
  exact (CategoryTheory.Iso.toLinearEquiv (ModuleCat.biprodIsoProd _ _)).symm.bijective.comp
    ((Function.Bijective.prodMap hU hV).comp
      (structureOpenMVMiddleSourceEquiv X Y U V n).bijective)

/-- The original tensor restriction pair is injective in total degree zero. -/
theorem structureOpenKunnethMV_first_zero_injective (U V : Y.left.Opens) :
    Function.Injective (structureOpenKunnethMVFirst X Y U V 0) :=
  Kunneth.MayerVietoris.tensorModuleMap_zero_injective (structureOriginalFirstModule X)
    (structureOpenModule Y (U ⊔ V))
    (fun q => (structureOpenModule Y U q ⊞ structureOpenModule Y V q : ModuleCat.{u + 1} k))
    (fun q => moduleMayerVietorisToBiprod Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V q)
    (structureOpenMV_first_zero_injective Y U V)

end KunnethOpenMayerVietoris

end AlgebraicGeometry.Scheme.Cohomology
