/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Coherent

/-!
# Shift closure of coherent native homology

The comparison is the component of the original native homology shift
sequence. It retains the supplied derived category and its independent
universe. Together with the existing exact-five extension argument, it
makes coherent native homology a triangulated object property.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- The original native comparison between homology of a shift and shifted homology. -/
def modulePlusHomologyShiftIso (K : DerivedCategory.Plus X.Modules) (n i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor X.Modules i).obj (K⟦n⟧) ≅
      (DerivedCategory.Plus.homologyFunctor X.Modules (n + i)).obj K :=
  ((DerivedCategory.Plus.homologyFunctor X.Modules 0).shiftIso n i (n + i) rfl).app K

/-- The homology shift comparison preserves each original coefficient arrow. -/
@[reassoc]
theorem modulePlusHomologyShiftIso_hom_naturality
    {K L : DerivedCategory.Plus X.Modules} (f : K ⟶ L) (n i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor X.Modules i).map (f⟦n⟧') ≫
        (modulePlusHomologyShiftIso X L n i).hom =
      (modulePlusHomologyShiftIso X K n i).hom ≫
        (DerivedCategory.Plus.homologyFunctor X.Modules (n + i)).map f :=
  ((DerivedCategory.Plus.homologyFunctor X.Modules 0).shiftIso n i (n + i) rfl).hom.naturality f

variable [IsLocallyNoetherian X]

/-- Coherence of the original homology sheaves is preserved by every integer shift. -/
theorem coherentHomologyObjects_shift (K : DerivedCategory.Plus X.Modules)
    (hK : coherentHomologyObjects X K) (n : ℤ) :
    coherentHomologyObjects X (K⟦n⟧) := by
  intro i
  exact (QuasiCoherent.affineLocallyFiniteType X).prop_of_iso
    (modulePlusHomologyShiftIso X K n i).symm (hK (n + i))

instance coherentHomologyObjects_isStableUnderShift :
    (coherentHomologyObjects X).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK => coherentHomologyObjects_shift X K hK n⟩

instance coherentHomologyObjects_isTriangulated : (coherentHomologyObjects X).IsTriangulated where

/-- The native coherent-homology condition is equivalent before and after any shift. -/
theorem coherentHomologyObjects_shift_iff (K : DerivedCategory.Plus X.Modules) (n : ℤ) :
    coherentHomologyObjects X (K⟦n⟧) ↔ coherentHomologyObjects X K :=
  (coherentHomologyObjects X).prop_shift_iff_of_isStableUnderShift K n

end AlgebraicGeometry.Scheme.Modules
