/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Projection.Coherence
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Projection.Amplitude
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Coherent.Shift

/-!
# Bounded coherent images of actual projective-space projections

The original derived image of every coherent module, placed in any integer
degree, has coherent homology. The shared coherent-homology object property
and sole finite Postnikov induction extend this to every cohomologically
bounded coherent object. Combined with the independently proved amplitude,
the native derived image retains bounds `[l,b+n]`. No coefficient flatness,
termwise coherence or proper-finiteness family is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The already installed ambient derived category of actual scheme modules. -/
local instance projectiveProjectionCoherentStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y) (f : Y ⟶ Spec (.of R))
  (h : IsPullback a p (toSpec R ι) f) (n : ℕ) (e : ι ≃ Fin (n + 1))

include h e

/-- The original derived image of a coherent coefficient in degree zero
has coherent native homology in every integer degree. -/
theorem projectiveProjection_derivedSingle_zero_coherent
    (M : X.Modules) (hM : affineLocallyFiniteType X M) :
    Scheme.Modules.coherentHomologyObjects Y
      ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
  intro i
  by_cases hi : 0 ≤ i
  · lift i to ℕ using hi
    exact (affineLocallyFiniteType Y).prop_of_iso
      (((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso i).app M)
      (projectiveProjection_higherDirectImage_coherent R ι a p f h n e M hM i)
  · exact (affineLocallyFiniteType Y).prop_of_isZero
      ((Scheme.Modules.pushforward p).isZero_homology_rightDerivedFunctorPlus_of_isGE
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) 0 i (by omega))

/-- The original derived image of a coherent module in any integer degree
has coherent native homology, using the sole native shift comparison. -/
theorem projectiveProjection_derivedSingle_coherent
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (i : ℤ) :
    Scheme.Modules.coherentHomologyObjects Y
      ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M)) := by
  let F := (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
  let C := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M
  have hC : Scheme.Modules.coherentHomologyObjects Y (F.obj C) :=
    projectiveProjection_derivedSingle_zero_coherent R ι a p f h n e M hM
  let E : (F.obj C)⟦-i⟧ ≅
      F.obj ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M) :=
    (((DerivedCategory.Plus.singleFunctors X.Modules).postcomp F).shiftIso
      (-i) i 0 (by omega)).app M
  exact (Scheme.Modules.coherentHomologyObjects Y).prop_of_iso E
    (Scheme.Modules.coherentHomologyObjects_shift Y (F.obj C) hC (-i))

/-- Actual projective-space projection preserves coherent homology of every
cohomologically bounded object. The source guard forms the shared coherent
property; it also follows geometrically from the locally Noetherian base. -/
theorem projectiveProjection_derived_coherent [IsLocallyNoetherian X]
    (K : DerivedCategory.Plus X.Modules) (l b : ℤ) [K.IsGE l] [K.IsLE b]
    (hK : Scheme.Modules.coherentHomologyObjects X K) :
    Scheme.Modules.coherentHomologyObjects Y
      ((Scheme.Modules.derivedPushforwardPlus p).obj K) := by
  let F := (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
  let P := (Scheme.Modules.coherentHomologyObjects Y).inverseImage F
  apply DerivedCategory.Plus.property_of_homology_bounds P K l b
  intro i _ _
  exact projectiveProjection_derivedSingle_coherent R ι a p f h n e
    ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K) (hK i) i

/-- The actual derived image is coherent and bounded in `[l,b+n]`, with no
condition on a representative's terms and no relative-flatness premise. -/
theorem projectiveProjection_derived_bounded_coherent [IsLocallyNoetherian X]
    (K : DerivedCategory.Plus X.Modules) (l b : ℤ) [K.IsGE l] [K.IsLE b]
    (hK : Scheme.Modules.coherentHomologyObjects X K) :
    Scheme.Modules.coherentHomologyObjects Y
        ((Scheme.Modules.derivedPushforwardPlus p).obj K) ∧
      ((Scheme.Modules.derivedPushforwardPlus p).obj K).IsGE l ∧
        ((Scheme.Modules.derivedPushforwardPlus p).obj K).IsLE (b + n) := by
  refine ⟨projectiveProjection_derived_coherent R ι a p f h n e K l b hK,
    projectiveProjection_derived_bounds R ι a p f h n e K l b ?_⟩
  intro i _ _
  exact quasicoherent_of_affineCharts _ (fun A j _ => (hK i A j).1)

end AlgebraicGeometry.Scheme.Cohomology
