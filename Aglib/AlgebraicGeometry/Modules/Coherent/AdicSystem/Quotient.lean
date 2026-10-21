/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Basic
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Descent
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Unit

/-! # Universal properties of the native ideal-sheaf quotients -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (K : X.IdealSheafData)

/-- The actual quotient is annihilated by its defining ideal sheaf. -/
theorem idealSheafQuotient_killed (F : X.Modules) :
    killedByIdealSheaf K ((idealSheafQuotientFunctor X K).obj F) := by
  change killedByIdealSheaf K ((pushforward K.subschemeι).obj
    ((pullback K.subschemeι).obj F))
  simpa only [K.ker_subschemeι] using
    killedByIdealSheaf_pushforward_ker K.subschemeι ((pullback K.subschemeι).obj F)

/-- Descend an original morphism into a coefficient killed by the ideal. -/
def idealSheafQuotientDesc {F G : X.Modules} (f : F ⟶ G)
    (hG : killedByIdealSheaf K G) :
    (idealSheafQuotientFunctor X K).obj F ⟶ G :=
  (idealSheafQuotientFunctor X K).map f ≫
    (closedImmersionDescentIso K.subschemeι G (by rwa [K.ker_subschemeι])).hom

@[reassoc (attr := simp)]
theorem idealSheafQuotientUnit_desc {F G : X.Modules} (f : F ⟶ G)
    (hG : killedByIdealSheaf K G) :
    (idealSheafQuotientUnit X K).app F ≫ idealSheafQuotientDesc X K f hG = f := by
  dsimp only [idealSheafQuotientDesc]
  rw [← Category.assoc, ← (idealSheafQuotientUnit X K).naturality f, Category.assoc]
  simp only [Functor.id_map]
  change f ≫ (closedImmersionDescentIso K.subschemeι G
    (by rwa [K.ker_subschemeι])).inv ≫
    (closedImmersionDescentIso K.subschemeι G (by rwa [K.ker_subschemeι])).hom = f
  exact (congrArg (fun k : G ⟶ G => f ≫ k)
    (Iso.inv_hom_id (closedImmersionDescentIso K.subschemeι G
      (by rwa [K.ker_subschemeι])))).trans (Category.comp_id f)

/-- Reduction along an inclusion of arbitrary ideal sheaves. -/
def idealSheafQuotientMap {J : X.IdealSheafData} (h : K ≤ J) (F : X.Modules) :
    (idealSheafQuotientFunctor X K).obj F ⟶
      (idealSheafQuotientFunctor X J).obj F :=
  idealSheafQuotientDesc X K ((idealSheafQuotientUnit X J).app F)
    (killedByIdealSheaf_of_le h (idealSheafQuotient_killed X J F))

@[reassoc (attr := simp)]
theorem idealSheafQuotientUnit_map {J : X.IdealSheafData} (h : K ≤ J) (F : X.Modules) :
    (idealSheafQuotientUnit X K).app F ≫ idealSheafQuotientMap X K h F =
      (idealSheafQuotientUnit X J).app F :=
  idealSheafQuotientUnit_desc X K _ _

@[simp]
theorem idealSheafQuotientMap_refl (F : X.Modules) :
    idealSheafQuotientMap X K (le_refl K) F = 𝟙 _ := by
  apply (cancel_epi ((idealSheafQuotientUnit X K).app F)).mp
  simp

@[reassoc (attr := simp)]
theorem idealSheafQuotientMap_comp {J L : X.IdealSheafData} (h : K ≤ J) (k : J ≤ L)
    (F : X.Modules) :
    idealSheafQuotientMap X K h F ≫ idealSheafQuotientMap X J k F =
      idealSheafQuotientMap X K (h.trans k) F := by
  apply (cancel_epi ((idealSheafQuotientUnit X K).app F)).mp
  simp

/-- Ideal-sheaf reduction commutes with the original coefficient morphism. -/
@[reassoc]
theorem idealSheafQuotientMap_naturality {J : X.IdealSheafData} (h : K ≤ J)
    {F G : X.Modules} (f : F ⟶ G) :
    (idealSheafQuotientFunctor X K).map f ≫ idealSheafQuotientMap X K h G =
      idealSheafQuotientMap X K h F ≫ (idealSheafQuotientFunctor X J).map f := by
  apply (cancel_epi ((idealSheafQuotientUnit X K).app F)).mp
  rw [← Category.assoc, ← (idealSheafQuotientUnit X K).naturality f,
    Category.assoc, idealSheafQuotientUnit_map,
    ← Category.assoc, idealSheafQuotientUnit_map]
  exact (idealSheafQuotientUnit X J).naturality f

/-- Quotienting successively by a smaller and a larger ideal yields the
original larger-ideal quotient, canonically on the original units. -/
def idealSheafQuotientReductionIso {J : X.IdealSheafData} (h : K ≤ J) (F : X.Modules) :
    (idealSheafQuotientFunctor X J).obj ((idealSheafQuotientFunctor X K).obj F) ≅
      (idealSheafQuotientFunctor X J).obj F where
  hom := idealSheafQuotientDesc X J (idealSheafQuotientMap X K h F)
    (idealSheafQuotient_killed X J F)
  inv := idealSheafQuotientDesc X J
    ((idealSheafQuotientUnit X K).app F ≫
      (idealSheafQuotientUnit X J).app ((idealSheafQuotientFunctor X K).obj F))
    (idealSheafQuotient_killed X J ((idealSheafQuotientFunctor X K).obj F))
  hom_inv_id := by
    apply (cancel_epi ((idealSheafQuotientUnit X J).app
      ((idealSheafQuotientFunctor X K).obj F))).mp
    apply (cancel_epi ((idealSheafQuotientUnit X K).app F)).mp
    simp
  inv_hom_id := by
    apply (cancel_epi ((idealSheafQuotientUnit X J).app F)).mp
    simp

@[reassoc (attr := simp)]
theorem idealSheafQuotientUnit_reductionIso_hom {J : X.IdealSheafData} (h : K ≤ J)
    (F : X.Modules) :
    (idealSheafQuotientUnit X J).app
        ((pushforward K.subschemeι).obj ((pullback K.subschemeι).obj F)) ≫
      (idealSheafQuotientReductionIso X K h F).hom = idealSheafQuotientMap X K h F :=
  idealSheafQuotientUnit_desc X J _ (idealSheafQuotient_killed X J F)

namespace AdicSystem

variable {X K} [IsLocallyNoetherian X] (F : AdicSystem X K)

/-- The reduction isomorphism is uniquely specified by its original transition. -/
theorem reductionIso_unique (n : ℕ)
    (e : (idealSheafQuotientFunctor X (K ^ n)).obj (F.obj.obj (Opposite.op (n + 1))) ≅
      F.obj.obj (Opposite.op n))
    (he : (idealSheafQuotientUnit X (K ^ n)).app (F.obj.obj (Opposite.op (n + 1))) ≫
      e.hom = F.transition n) : e = F.reductionIso n := by
  apply Iso.ext
  apply (cancel_epi ((idealSheafQuotientUnit X (K ^ n)).app
    (F.obj.obj (Opposite.op (n + 1))))).mp
  exact he.trans (F.unit_reductionIso_hom n).symm

instance transition_epi (n : ℕ) : Epi (F.transition n) := by
  rw [← F.unit_reductionIso_hom n]
  infer_instance

end AdicSystem

end AlgebraicGeometry.Scheme.Modules.Coherent
