/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.MaximalModel.R1
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Stalk.Structure
public import Aglib.AlgebraicGeometry.Descent.LocalModification
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Regular

/-!
# Universal original H1 vanishing at closed nongeneric stalks

A complete normal local surface with a uniform original H1 bound admits an
actual normal proper birational model whose closed nongeneric stalks satisfy
the existing universal normal-modification H1-vanishing predicate.

The original R1 producer, constructed local replacement and actual pullback
stalk/cohomology comparison retain each caller's local scheme and morphism.
No completeness of those stalks, finite Cohen extension into them, or
resolution conclusion is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- A genuine original global R1-vanishing model has universal original H1
vanishing at each closed nongeneric stalk. Each caller's local model is
extended by the actual replacement producer and retained in its pullback square. -/
theorem normalModificationH1Vanishing_stalk_of_original_R1_vanishing
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (hR1 : ∀ (Y : Scheme.{u}) [IsIntegral Y] (h : Y ⟶ X)
      [IsProper h] [IsDominant h],
      NormalStalks Y → IsIso (CommRingCat.ofHom (functionFieldMap h)) →
        IsZero (((Scheme.Modules.pushforward h).rightDerived 1).obj
          (FiniteTraceCoordinates.structureModule Y)))
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X) :
    letI : IsDomain (X.presheaf.stalk x) := (hX x).1
    NormalModificationH1Vanishing (X.presheaf.stalk x) := by
  let : IsDomain (X.presheaf.stalk x) := (hX x).1
  intro T hT p hp hpd hTN hpff
  let : IsIntegral T := hT
  let : IsProper p := hp
  let : IsDominant p := hpd
  obtain ⟨G⟩ := Scheme.LocalModification.exists_localReplacement
    X hX hdX x hx hxη hTN p hpff
  let : IsIntegral G.Y := G.integral
  let : IsProper G.h := G.proper
  let : IsDominant G.h := G.dominant
  have hz : IsZero (((Scheme.Modules.pushforward G.h).rightDerived 1).obj
      (show G.Y.Modules from SheafOfModules.unit G.Y.ringCatSheaf)) :=
    hR1 G.Y G.h G.normal G.fieldIso
  exact Cohomology.original_localStructureH1_subsingleton_of_R1_isZero
    G.h x G.a p G.square hz

/-- A uniform original H1 bound over a complete normal local surface yields
an actual normal proper birational model with universal original H1 vanishing
at every closed nongeneric stalk. No completeness or finite coefficient-ring
extension is asserted for those stalks. -/
theorem exists_model_closed_nongeneric_stalk_vanishing
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hd : ringKrullDim A = 2) (hbound : Cohomology.NormalModificationH1Bounded A) :
    ∃ (X : Scheme.{u}) (hX : IsIntegral X),
      letI := hX
      ∃ (f : X ⟶ Spec (.of A)) (hf : IsProper f) (hdom : IsDominant f),
        letI := hf
        letI := hdom
        ∃ hXN : NormalStalks X,
          IsIso (CommRingCat.ofHom (functionFieldMap f)) ∧ IsNoetherian X ∧
          ∀ (x : X), IsClosed ({x} : Set X) → x ≠ genericPoint X →
            letI : IsDomain (X.presheaf.stalk x) := (hXN x).1
            NormalModificationH1Vanishing (X.presheaf.stalk x) := by
  obtain ⟨X, hX, rest⟩ := Cohomology.exists_normal_model_original_R1_vanishing A hd hbound
  let : IsIntegral X := hX
  obtain ⟨f, hf, hdom, rest⟩ := rest
  let : IsProper f := hf
  let : IsDominant f := hdom
  obtain ⟨hXN, hff, hR1⟩ := rest
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := { __ := (inferInstance : IsLocallyNoetherian X) }
  have hdX : topologicalKrullDim X ≤ 2 :=
    Cohomology.actualModel_dimension_of_complete_surface A f hd hff
  refine ⟨X, hX, f, hf, hdom, hXN, hff, inferInstance, ?_⟩
  intro x hx hxη
  exact normalModificationH1Vanishing_stalk_of_original_R1_vanishing
    X hXN hdX hR1 x hx hxη

end AlgebraicGeometry.Scheme.RationalSingularities
