/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Single
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Coherent.Single
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Coherent.Shift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov

/-!
# Actual finite derived images of bounded coherent objects

Finite pushforward preserves the original finite-type quasicoherent
predicate. The actual affine acyclic-single comparison therefore gives
coherent native homology on each coherent single. Its amplitude is zero.
The sole finite Postnikov argument extends these conclusions to bounded
coherent native derived objects, preserving their original interval of
homology bounds. Exactness of finite pushforward on all module sheaves
is not assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The installed standard ambient derived category of actual module sheaves. -/
local instance finiteCoherentStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f]

section CoherentSingle

variable [IsLocallyNoetherian Y]

/-- Every original higher direct image of a coherent coefficient under a finite
morphism is coherent. Positive higher images are actually zero. -/
theorem finite_higherDirectImage_coherent (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (q : ℕ) :
    affineLocallyFiniteType Y (((Scheme.Modules.pushforward f).rightDerived q).obj M) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)
  cases q with
  | zero =>
    exact (affineLocallyFiniteType Y).prop_of_iso
      (((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf).app M).symm
      (FiniteMorphism.affineLocallyFiniteType_pushforward f hM)
  | succ n =>
    exact (affineLocallyFiniteType Y).prop_of_isZero
      (Scheme.Modules.isZero_rightDerived_pushforward_succ f M n)

/-- The actual finite derived image of a coherent coefficient in degree zero
has coherent native homology, through the original affine unit comparison. -/
theorem finite_derivedSingle_zero_coherent (M : X.Modules)
    (hM : affineLocallyFiniteType X M) :
    Scheme.Modules.coherentHomologyObjects Y
      ((Scheme.Modules.derivedPushforwardPlus f).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)
  exact (Scheme.Modules.coherentHomologyObjects Y).prop_of_iso
    (Scheme.Modules.affineDerivedPushforwardSingleIso f M).symm
    (Scheme.Modules.coherentHomologyObjects_single Y ((Scheme.Modules.pushforward f).obj M)
      (FiniteMorphism.affineLocallyFiniteType_pushforward f hM) 0)

/-- A coherent coefficient in any original integer degree has coherent actual
finite derived image, using the native single shift comparison. -/
theorem finite_derivedSingle_coherent (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (i : ℤ) :
    Scheme.Modules.coherentHomologyObjects Y
      ((Scheme.Modules.derivedPushforwardPlus f).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M)) := by
  let F := (Scheme.Modules.pushforward f).rightDerivedFunctorPlus
  let C := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M
  have hC : Scheme.Modules.coherentHomologyObjects Y (F.obj C) :=
    finite_derivedSingle_zero_coherent f M hM
  let E : (F.obj C)⟦-i⟧ ≅
      F.obj ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M) :=
    (((DerivedCategory.Plus.singleFunctors X.Modules).postcomp F).shiftIso
      (-i) i 0 (by omega)).app M
  exact (Scheme.Modules.coherentHomologyObjects Y).prop_of_iso E
    (Scheme.Modules.coherentHomologyObjects_shift Y (F.obj C) hC (-i))

end CoherentSingle

/-- A finite derived image of a quasicoherent native single has upper bound
equal to the original degree of that single. No Noetherianity is needed. -/
theorem finite_derivedSingle_isLE (M : X.Modules) [M.IsQuasicoherent] (i : ℤ) :
    ((Scheme.Modules.derivedPushforwardPlus f).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M)).IsLE i := by
  let F := (Scheme.Modules.pushforward f).rightDerivedFunctorPlus
  let C := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M
  let : (F.obj C).IsLE 0 := (Scheme.Modules.affineDerivedPushforwardSingle_bounds f M).2
  let : ((F.obj C)⟦-i⟧).IsLE i :=
    DerivedCategory.Plus.TStructure.t.isLE_shift (F.obj C) 0 (-i) i (by omega)
  let E : (F.obj C)⟦-i⟧ ≅
      F.obj ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M) :=
    (((DerivedCategory.Plus.singleFunctors X.Modules).postcomp F).shiftIso
      (-i) i 0 (by omega)).app M
  exact DerivedCategory.Plus.TStructure.t.isLE_of_iso E i

/-- The actual finite derived image retains the upper bound of a bounded object
with quasicoherent original homology in its actual homology interval. -/
theorem finite_derived_isLE (K : DerivedCategory.Plus X.Modules) (l b : ℤ)
    [K.IsGE l] [K.IsLE b]
    (hK : ∀ i : ℤ, l ≤ i → i ≤ b →
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    ((Scheme.Modules.derivedPushforwardPlus f).obj K).IsLE b := by
  let F := (Scheme.Modules.pushforward f).rightDerivedFunctorPlus
  let t := DerivedCategory.Plus.TStructure.t (C := Y.Modules)
  let P : ObjectProperty (DerivedCategory.Plus X.Modules) := fun L => (F.obj L).IsLE b
  let : P.IsClosedUnderIsomorphisms :=
    { of_iso := fun E hE => by
        let : (F.obj _).IsLE b := hE
        exact t.isLE_of_iso (F.mapIso E) b }
  let : P.ContainsZero :=
    { exists_zero := ⟨0, isZero_zero _, t.isLE_of_isZero (F.map_isZero (isZero_zero _)) b⟩ }
  let : P.IsTriangulatedClosed₂ := .mk'
    (fun T hT h₁ h₃ => t.isLE₂ (F.mapTriangle.obj T) (F.map_distinguished T hT) b h₁ h₃)
  apply DerivedCategory.Plus.property_of_homology_bounds P K l b
  intro i hli hib
  let : ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent := hK i hli hib
  let : (F.obj ((DerivedCategory.Plus.singleFunctor X.Modules i).obj
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K))).IsLE i :=
    finite_derivedSingle_isLE f _ i
  exact t.isLE_of_le _ i b hib

/-- Actual finite derived image preserves the full original homology interval. -/
theorem finite_derived_bounds (K : DerivedCategory.Plus X.Modules) (l b : ℤ)
    [K.IsGE l] [K.IsLE b]
    (hK : ∀ i : ℤ, l ≤ i → i ≤ b →
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    ((Scheme.Modules.derivedPushforwardPlus f).obj K).IsGE l ∧
      ((Scheme.Modules.derivedPushforwardPlus f).obj K).IsLE b :=
  ⟨(Scheme.Modules.pushforward f).rightDerivedFunctorPlus_isGE K l,
    finite_derived_isLE f K l b hK⟩

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Every bounded object with coherent native homology has coherent actual
finite derived image. No representative-term condition is imposed. -/
theorem finite_derived_coherent (K : DerivedCategory.Plus X.Modules) (l b : ℤ)
    [K.IsGE l] [K.IsLE b] (hK : Scheme.Modules.coherentHomologyObjects X K) :
    Scheme.Modules.coherentHomologyObjects Y
      ((Scheme.Modules.derivedPushforwardPlus f).obj K) := by
  let F := (Scheme.Modules.pushforward f).rightDerivedFunctorPlus
  let P := (Scheme.Modules.coherentHomologyObjects Y).inverseImage F
  apply DerivedCategory.Plus.property_of_homology_bounds P K l b
  intro i _ _
  exact finite_derivedSingle_coherent f
    ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K) (hK i) i

/-- Finite derived direct image preserves bounded coherent homology and the
same interval `[l,b]`, through the installed original derived functor. -/
theorem finite_derived_bounded_coherent (K : DerivedCategory.Plus X.Modules) (l b : ℤ)
    [K.IsGE l] [K.IsLE b] (hK : Scheme.Modules.coherentHomologyObjects X K) :
    Scheme.Modules.coherentHomologyObjects Y
        ((Scheme.Modules.derivedPushforwardPlus f).obj K) ∧
      ((Scheme.Modules.derivedPushforwardPlus f).obj K).IsGE l ∧
        ((Scheme.Modules.derivedPushforwardPlus f).obj K).IsLE b := by
  refine ⟨finite_derived_coherent f K l b hK, finite_derived_bounds f K l b ?_⟩
  intro i _ _
  exact quasicoherent_of_affineCharts _ (fun R j _ => (hK i R j).1)

end AlgebraicGeometry.Scheme.Cohomology
