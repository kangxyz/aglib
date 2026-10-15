/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorFiniteFree
public import Aglib.Algebra.Homology.ShortComplex.Retract

/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/TensorExact.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 58]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Exact tensor with finite-free retract coefficients

An actual coefficient retraction gives an actual retraction of tensor short
complexes. Tensoring by a finite-free retract therefore preserves short exactness.
This is a finite-projective coefficient theorem; no local-freeness or restriction
comparison is assumed or claimed here.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A coefficient retraction gives the original tensor-map retraction on short complexes. -/
def tensorShortComplexRetract (S : ShortComplex (SheafOfModulesOfCommRing R))
    {M N : SheafOfModulesOfCommRing R} (h : Retract M N) :
    Retract (S.map (tensorLeftFunctor R M)) (S.map (tensorLeftFunctor R N)) where
  i := S.mapNatTrans ((tensorFunctor R).map h.i)
  r := S.mapNatTrans ((tensorFunctor R).map h.r)
  retract := by
    ext : 1
    · exact congrArg (fun α => α.app S.X₁) (h.map (tensorFunctor R)).retract
    · exact congrArg (fun α => α.app S.X₂) (h.map (tensorFunctor R)).retract
    · exact congrArg (fun α => α.app S.X₃) (h.map (tensorFunctor R)).retract

/-- The actual tensor with a finite-free retract preserves the original short exact sequence. -/
theorem tensor_shortExact_of_retract_finiteFree
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (hS : S.ShortExact)
    {M : SheafOfModulesOfCommRing R} (I : Type u) [Finite I]
    (h : Retract M (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I)) :
    (S.map (tensorLeftFunctor R M)).ShortExact :=
  ShortComplex.shortExact_of_retract (tensorShortComplexRetract R S h)
    (hS.map_of_exact (tensorLeftFunctor R _))

end SheafOfModulesOfCommRing
