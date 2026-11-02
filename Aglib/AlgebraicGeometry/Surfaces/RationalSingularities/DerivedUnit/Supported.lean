/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Supported
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Regular

/-!
# The original supported structure unit from rationality of one stalk

The actual proper Cartesian local model is a normal birational modification
of the ORIGINAL stalk spectrum. Its genuine rationality kills its SAME H1;
the existing supported R1 comparison and surface theorem then make the
original global derived structure unit invertible. No global rationality,
later completion, finite-parent-map or canonical premise is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

local instance rationalSupportedStructureDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- Rationality of the ORIGINAL stalk discharges the original derived unit
of an actual supported proper birational surface map. Properness of the
supplied local model follows from the SAME Cartesian square; its normality
and original birational field map are genuine geometric data. -/
theorem isIso_moduleDerivedPushforwardUnit_of_supported_rational_stalk
    {X Z T : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsIntegral T]
    [IsLocallyNoetherian X]
    (f : Z ⟶ X) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdZ : topologicalKrullDim Z ≤ 2)
    (x : X) (hx : IsClosed ({x} : Set X))
    (a : T ⟶ Z) (p : T ⟶ Spec (X.presheaf.stalk x)) [IsDominant p]
    (H : IsPullback a p f (X.fromSpecStalk x))
    (hT : NormalStalks T)
    (hpff : IsIso (CommRingCat.ofHom (functionFieldMap p)))
    (hU : IsIso (f ∣_ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)))
    (hRat : NormalModificationH1Vanishing (X.presheaf.stalk x)) :
    IsIso (moduleDerivedPushforwardUnit X f) := by
  let : IsProper p := MorphismProperty.of_isPullback H inferInstance
  have hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf T (SheafOfModules.unit T.ringCatSheaf)) 1) :=
    hRat T p hT hpff
  have hR1 := firstHigherImage_isZero_of_localStructureH1_of_isIso_complement
    f x hx a p H hU hH
  exact isIso_moduleDerivedPushforwardUnit_of_surface_R1_isZero f hX hff hdZ hR1

end AlgebraicGeometry.Scheme.RationalSingularities
