/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.DerivedAdjoint
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedH1Kernel
public import Aglib.CategoryTheory.Adjunction.ShiftedHom.RightComposition

/-! The original Kummer boundary in shifted derived adjunction. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open GroupCohomology.Kummer.Coefficients

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w dX dS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))

/-- The original Kummer boundary and the original derived connecting arrow agree
in the actual shifted adjunct of a degree-one class. -/
theorem derivedKummerTriangle_originalAdjunct_boundary (c : Sheaf.H.{w} (gm X) 1) :
    let A := AbelianSheaf.{u, u + 1} S
    let B := AbelianSheaf.{u, u + 1} X
    let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let U₀ := (DerivedCategory.Plus.singleFunctor A 0).obj U
    let K := (DerivedCategory.Plus.singleFunctor B 0).obj (mu X n)
    let e := ((inverseImage p).rightDerivedFunctorPlusSingleIso 0).app U ≪≫
      (DerivedCategory.Plus.singleFunctor B 0).mapIso
        ((inverseImageConstantIso p).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    let η := ((DerivedCategory.Plus.singleFunctors A).shiftIso (-1) 1 0 (by omega)).app U
    let T := derivedKummerTriangle p n hn hi
    let a := (shiftEquiv' (DerivedCategory.Plus A) (-1) 1 (by omega)).toAdjunction
    (derivedImageAdjunction p).shiftedHomEquiv (2 : ℤ) U₀ K
        (e.hom ≫ (boundary X n hn hi 1 c).homPlus) =
      ShiftedHom.comp
        ((a.homEquiv U₀ T.obj₃) (η.hom ≫ cohomologyOriginalDerivedAdjunct p (gm X) c) :
          ShiftedHom U₀ T.obj₃ (1 : ℤ))
        (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) (by omega) := by
  intro A B U U₀ K e η T a
  let M := (DerivedCategory.Plus.singleFunctor B 0).obj (gm X)
  let R := derivedDirectImage p
  let adj := derivedImageAdjunction p
  let b : ShiftedHom M K (1 : ℤ) := (shortExact X n hn hi).singleTrianglePlus.mor₃
  let d : Ext (gm X) (mu X n) 1 := (shortExact X n hn hi).extClass
  let x : ShiftedHom ((derivedInverseImage p).obj U₀) M (1 : ℤ) := e.hom ≫ c.homPlus
  let z := adj.shiftedHomEquiv (1 : ℤ) U₀ M x
  have hξ : (a.homEquiv U₀ T.obj₃) (η.hom ≫ cohomologyOriginalDerivedAdjunct p (gm X) c) = z := by
    let v := (a.homEquiv U₀ T.obj₃).symm z
    have h : η.hom ≫ cohomologyOriginalDerivedAdjunct p (gm X) c = v :=
      η.hom_inv_id_assoc v
    exact (congrArg (a.homEquiv U₀ T.obj₃) h).trans ((a.homEquiv U₀ T.obj₃).apply_symm_apply z)
  have hδ : ShiftedHom.map (b : ShiftedHom M K (1 : ℤ)) R = T.mor₃ := rfl
  change adj.shiftedHomEquiv (2 : ℤ) U₀ K
    (e.hom ≫ (c.comp d rfl).homPlus) =
      ShiftedHom.comp
        ((a.homEquiv U₀ T.obj₃) (η.hom ≫ cohomologyOriginalDerivedAdjunct p (gm X) c) :
          ShiftedHom U₀ T.obj₃ (1 : ℤ))
        (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) (by omega)
  have hd : d.homPlus = b := Ext.homPlus_extClass (shortExact X n hn hi)
  have hc := Ext.homPlus_comp c d (rfl : 1 + 1 = 2)
  rw [hξ, hc, hd]
  have hh : e.hom ≫ c.homPlus.comp (b : ShiftedHom M K (1 : ℤ)) (by omega : 1 + 1 = (2 : ℤ)) =
      x.comp (b : ShiftedHom M K (1 : ℤ)) (by omega) := by
    simp only [ShiftedHom.comp, x, Category.assoc]
    rfl
  rw [hh, adj.shiftedHomEquiv_postcomp, hδ]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
