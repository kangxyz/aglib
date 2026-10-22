/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenIdealPullback

/-! # Actual restriction of an independent ideal quotient -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (K : X.IdealSheafData)

/-- Restriction, rather than a substitute coefficient functor, commutes with quotient. -/
def restrictQuotientIso (M : X.Modules) [M.IsQuasicoherent] :
    ((idealSheafQuotientFunctor X K).obj M).restrict j ≅
      (idealSheafQuotientFunctor Y (K.comap j)).obj (M.restrict j) :=
  (restrictFunctorIsoPullback j).app _ ≪≫ idealSheafPullbackQuotientIso j K M ≪≫
    (idealSheafQuotientFunctor Y (K.comap j)).mapIso
      ((restrictFunctorIsoPullback j).app M).symm

/-- The restriction comparison retains the original quotient unit. -/
@[reassoc]
theorem restrictQuotientIso_unit (M : X.Modules) [M.IsQuasicoherent] :
    (restrictFunctor j).map ((idealSheafQuotientUnit X K).app M) ≫
      (restrictQuotientIso j K M).hom =
    (idealSheafQuotientUnit Y (K.comap j)).app (M.restrict j) := by
  have hn : (restrictFunctor j).map ((idealSheafQuotientUnit X K).app M) ≫
      ((restrictFunctorIsoPullback j).app ((idealSheafQuotientFunctor X K).obj M)).hom =
    ((restrictFunctorIsoPullback j).app M).hom ≫
      (pullback j).map ((idealSheafQuotientUnit X K).app M) :=
    (restrictFunctorIsoPullback j).hom.naturality ((idealSheafQuotientUnit X K).app M)
  dsimp only [restrictQuotientIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [idealSheafPullbackQuotientIso_unit_assoc]
  rw [← (idealSheafQuotientUnit Y (K.comap j)).naturality]
  simp

/-- Actual restricted coefficient maps form the original quotient square. -/
@[reassoc]
theorem restrictQuotientIso_naturality {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (restrictFunctor j).map ((idealSheafQuotientFunctor X K).map f) ≫
      (restrictQuotientIso j K N).hom =
    (restrictQuotientIso j K M).hom ≫
      (idealSheafQuotientFunctor Y (K.comap j)).map ((restrictFunctor j).map f) := by
  apply (cancel_epi ((restrictFunctor j).map ((idealSheafQuotientUnit X K).app M))).mp
  rw [← Functor.map_comp_assoc, ← (idealSheafQuotientUnit X K).naturality f]
  simp only [Functor.id_map, Functor.map_comp, Category.assoc]
  rw [restrictQuotientIso_unit, ← Category.assoc, restrictQuotientIso_unit]
  exact (idealSheafQuotientUnit Y (K.comap j)).naturality ((restrictFunctor j).map f)

end AlgebraicGeometry.Scheme.Modules.Coherent
