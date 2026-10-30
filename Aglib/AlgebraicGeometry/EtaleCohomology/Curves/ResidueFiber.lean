/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteCoverBaseChange
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The literal closed fibre of a finite cover of the projective line

The fibre is the original categorical pullback. Its finite map to the projective
line over the residue field is constructed from the native projective-line base
change isomorphism. No Noetherian hypothesis is imposed on the local base ring.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (p : Y ⟶ ProjectiveLine.projectiveP1 R)

/-- The original closed fibre, with no replacement of its underlying scheme. -/
abbrev residueFiber : Scheme.{u} :=
  pullback (p ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)

/-- The original structural map of the closed fibre to the residue field. -/
abbrev residueFiberStructureMap : residueFiber p ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  pullback.snd (p ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)

/-- Base change of the original finite map, followed by the native projective-line comparison. -/
def residueFiberLineOverMap :
    Over.mk (residueFiberStructureMap p) ⟶
      Over.mk (ProjectiveLine.structureMap (IsLocalRing.ResidueField R)) :=
  AlgebraicGeometry.ProjectiveSpace.finiteCoverBaseChangeOverMap (IsLocalRing.residue R) p

/-- The finite cover of the projective line on the literal closed fibre. -/
def residueFiberLineMap :
    residueFiber p ⟶ ProjectiveLine.projectiveP1 (IsLocalRing.ResidueField R) :=
  (residueFiberLineOverMap p).left

@[reassoc (attr := simp)]
theorem residueFiberLineMap_structureMap :
    residueFiberLineMap p ≫ ProjectiveLine.structureMap (IsLocalRing.ResidueField R) =
      residueFiberStructureMap p :=
  (residueFiberLineOverMap p).w

instance [IsFinite p] : IsFinite (residueFiberLineMap p) :=
  inferInstanceAs (IsFinite
    (AlgebraicGeometry.ProjectiveSpace.finiteCoverBaseChangeMap (IsLocalRing.residue R) p))

instance [IsFinite p] : IsProper (residueFiberStructureMap p) := by
  let : IsProper (p ≫ ProjectiveLine.structureMap R) := inferInstance
  change IsProper (pullback.snd (p ≫ ProjectiveLine.structureMap R)
    (LocalRing.residueSpecMap R))
  infer_instance

/-- The closed fibre is Noetherian even when the local base ring is not. -/
theorem residueFiber_isNoetherian [IsFinite p] : IsNoetherian (residueFiber p) := by
  let : IsLocallyNoetherian (residueFiber p) :=
    LocallyOfFiniteType.isLocallyNoetherian (residueFiberStructureMap p)
  let : CompactSpace (residueFiber p) :=
    QuasiCompact.compactSpace_of_compactSpace (residueFiberStructureMap p)
  exact ⟨⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
