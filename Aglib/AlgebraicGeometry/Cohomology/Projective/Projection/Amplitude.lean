/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Projection.Vanishing
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov

/-!
# Derived amplitude of actual projective-space projections

The original derived direct image of a quasicoherent module in degree `i`
has upper bound `i + n`. The native single-functor shift comparison retains
the installed derived functor. The sole finite Postnikov induction then
gives upper bound `b + n` for a cohomologically bounded object whose original
homology sheaves are quasicoherent. No termwise quasicoherence, finite-type
condition, Noetherianity or flatness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.ProjectiveSpace
open ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The already installed ambient derived category of actual scheme modules. -/
local instance projectiveProjectionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}}
  (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y) (f : Y ⟶ Spec (.of R))
  (h : IsPullback a p (toSpec R ι) f) (n : ℕ) (e : ι ≃ Fin (n + 1))

include h e

/-- The installed derived image of a quasicoherent coefficient in degree zero
has upper bound equal to the projective dimension. -/
theorem projectiveProjection_derivedSingle_zero_isLE
    (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)).IsLE (n : ℤ) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro i hi
  lift i to ℕ using (by omega : 0 ≤ i)
  exact (projectiveProjection_higherDirectImage_isZero R ι a p f h n e M i
    (by omega)).of_iso (((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso i).app M).symm

/-- The original derived image of a quasicoherent module in any integer degree
has the corresponding translated upper bound. -/
theorem projectiveProjection_derivedSingle_isLE
    (M : X.Modules) [M.IsQuasicoherent] (i : ℤ) :
    ((Scheme.Modules.derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M)).IsLE (i + n) := by
  let F := (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
  let C := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M
  let : (F.obj C).IsLE (n : ℤ) :=
    projectiveProjection_derivedSingle_zero_isLE R ι a p f h n e M
  let : ((F.obj C)⟦-i⟧).IsLE (i + n) :=
    DerivedCategory.Plus.TStructure.t.isLE_shift (F.obj C) n (-i) (i + n) (by omega)
  let E : (F.obj C)⟦-i⟧ ≅
      F.obj ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M) :=
    (((DerivedCategory.Plus.singleFunctors X.Modules).postcomp F).shiftIso
      (-i) i 0 (by omega)).app M
  exact DerivedCategory.Plus.TStructure.t.isLE_of_iso E (i + n)

/-- The actual derived direct image sends bounded quasicoherent homology in
`[l,b]` to upper bound `b+n`. Only the original homology layers in that interval
are required to be quasicoherent; no representative-term condition is imposed. -/
theorem projectiveProjection_derived_isLE
    (K : DerivedCategory.Plus X.Modules) (l b : ℤ) [K.IsGE l] [K.IsLE b]
    (hK : ∀ i : ℤ, l ≤ i → i ≤ b →
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    ((Scheme.Modules.derivedPushforwardPlus p).obj K).IsLE (b + n) := by
  let F := (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
  let t := DerivedCategory.Plus.TStructure.t (C := Y.Modules)
  let P : ObjectProperty (DerivedCategory.Plus X.Modules) :=
    fun L => (F.obj L).IsLE (b + n)
  let : P.IsClosedUnderIsomorphisms :=
    { of_iso := fun E hE => by
        let : (F.obj _).IsLE (b + n) := hE
        exact t.isLE_of_iso (F.mapIso E) (b + n) }
  let : P.ContainsZero :=
    { exists_zero := ⟨0, isZero_zero _,
        t.isLE_of_isZero (F.map_isZero (isZero_zero _)) (b + n)⟩ }
  let : P.IsTriangulatedClosed₂ := .mk'
    (fun T hT h₁ h₃ => t.isLE₂ (F.mapTriangle.obj T) (F.map_distinguished T hT)
      (b + n) h₁ h₃)
  apply DerivedCategory.Plus.property_of_homology_bounds P K l b
  intro i hli hib
  let : ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent :=
    hK i hli hib
  let : (F.obj ((DerivedCategory.Plus.singleFunctor X.Modules i).obj
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K))).IsLE (i + n) :=
    projectiveProjection_derivedSingle_isLE R ι a p f h n e _ i
  exact t.isLE_of_le _ (i + n) (b + n) (by omega)

/-- The original derived image has the full interval bound `[l,b+n]`.
Its lower bound is the sole generic right-derived lower-bound theorem. -/
theorem projectiveProjection_derived_bounds
    (K : DerivedCategory.Plus X.Modules) (l b : ℤ) [K.IsGE l] [K.IsLE b]
    (hK : ∀ i : ℤ, l ≤ i → i ≤ b →
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    ((Scheme.Modules.derivedPushforwardPlus p).obj K).IsGE l ∧
      ((Scheme.Modules.derivedPushforwardPlus p).obj K).IsLE (b + n) :=
  ⟨(Scheme.Modules.pushforward p).rightDerivedFunctorPlus_isGE K l,
    projectiveProjection_derived_isLE R ι a p f h n e K l b hK⟩

end AlgebraicGeometry.Scheme.Cohomology
