/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.DerivedAdjoint
public import Aglib.CategoryTheory.Adjunction.ShiftedHom.TransportedSources

/-! Coefficient naturality of the original degree-one derived adjunct. -/

open CategoryTheory CategoryTheory.Abelian

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open DerivedCategory

universe u dX dS w

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- An original coefficient map postcomposes the original degree-one adjunct. -/
theorem cohomologyOriginalDerivedAdjunct_map
    {M N : AbelianSheaf.{u, u + 1} X} (f : M ⟶ N) (c : Sheaf.H.{w} M 1) :
    cohomologyOriginalDerivedAdjunct p N (Sheaf.H.map f 1 c) =
      cohomologyOriginalDerivedAdjunct p M c ≫ (derivedDirectImage p).map
        ((Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).map f) := by
  let A := AbelianSheaf.{u, u + 1} S
  let B := AbelianSheaf.{u, u + 1} X
  let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let U₀ := (Plus.singleFunctor A 0).obj U
  let P := Plus.singleFunctor B 0
  let D := derivedDirectImage p
  let adj := derivedImageAdjunction p
  let e := ((inverseImage p).rightDerivedFunctorPlusSingleIso 0).app U ≪≫
    P.mapIso ((inverseImageConstantIso p).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let m : ShiftedHom ((derivedInverseImage p).obj U₀) (P.obj M) (1 : ℤ) := e.hom ≫ c.homPlus
  let m' : ShiftedHom ((derivedInverseImage p).obj U₀) (P.obj N) (1 : ℤ) :=
    e.hom ≫ (Sheaf.H.map f 1 c).homPlus
  have hc : (Sheaf.H.map f 1 c).homPlus = c.homPlus ≫ (P.map f)⟦(1 : ℤ)⟧' := by
    change (c.comp (Ext.mk₀ f) (add_zero 1)).homPlus = _
    rw [Ext.homPlus_comp, Ext.homPlus_mk₀]
    exact ShiftedHom.comp_mk₀ c.homPlus 0 rfl (P.map f)
  have hm : m' = m ≫ (P.map f)⟦(1 : ℤ)⟧' :=
    (congrArg (fun a => e.hom ≫ a) hc).trans (Category.assoc _ _ _).symm
  have h := (congrArg (adj.shiftedHomEquiv 1 U₀ (P.obj N)) hm).trans
    (adj.shiftedHomEquiv_postcomp_shift m (P.map f))
  let η := ((Plus.singleFunctors A).shiftIso (-1) 1 0 (by omega)).app U
  let s : shiftFunctor (Plus A) (-1 : ℤ) ⊣ shiftFunctor (Plus A) (1 : ℤ) :=
    (shiftEquiv' (Plus A) (-1 : ℤ) 1 (by omega)).toAdjunction
  let z := adj.shiftedHomEquiv 1 U₀ (P.obj M) m
  let z' := adj.shiftedHomEquiv 1 U₀ (P.obj N) m'
  let b := D.map (P.map f)
  change η.inv ≫ (s.homEquiv U₀ (D.obj (P.obj N))).symm z' =
    (η.inv ≫ (s.homEquiv U₀ (D.obj (P.obj M))).symm z) ≫ b
  have h₁ := congrArg ((s.homEquiv U₀ (D.obj (P.obj N))).symm) h
  have h₂ := s.homEquiv_naturality_right_symm z b
  exact (congrArg (fun x => η.inv ≫ x) (h₁.trans h₂)).trans (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
