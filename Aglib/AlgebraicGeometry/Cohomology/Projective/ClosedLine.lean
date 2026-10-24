/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Vanishing
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.StructureQuotient
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit

/-!
# Structure cohomology of an actual closed projective line subscheme

The original closed-immersion ideal sequence and the two standard affine
charts of projective one-space give positive-degree vanishing for the
actual structure module on any closed subscheme over a commutative ring.
The original closed-pushforward cohomology equivalence retains its maps
and coefficient actions.

The current consumer is structure cohomology of the actual two-generator
blowups used in regular-source point-blowup chains.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- An actual closed subscheme of projective one-space over an affine base
has zero positive-degree cohomology of its original structure module. -/
public theorem subsingleton_structureCohomology_of_closedLine
    (A : Type u) [CommRing A] (ι : Type u) (e : ι ≃ Fin 2)
    {Z : Scheme.{u}} (i : Z ⟶ ProjectiveSpace A ι) [IsClosedImmersion i]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf Z (SheafOfModules.unit Z.ringCatSheaf)) q) := by
  let OZ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let OP : (ProjectiveSpace A ι).Modules :=
    SheafOfModules.unit (ProjectiveSpace A ι).ringCatSheaf
  let F : (ProjectiveSpace A ι).Modules := (Scheme.Modules.pushforward i).obj OZ
  let J : (ProjectiveSpace A ι).Modules := kernel (Scheme.Hom.structureModuleMap i)
  let : OZ.IsQuasicoherent := Scheme.Modules.isQuasicoherent_unit Z
  let : OP.IsQuasicoherent := Scheme.Modules.isQuasicoherent_unit (ProjectiveSpace A ι)
  let : F.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i OZ
  let : J.IsQuasicoherent :=
    Scheme.Modules.QuasiCoherent.quasicoherent_kernel (Scheme.Hom.structureModuleMap i)
  have hOP : Subsingleton
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) OP) q) :=
    moduleCohomology_subsingleton_of_iso (twistingZeroIso A ι) q
      (twistingCohomology_subsingleton_of_neg_le_degree A ι 1 e 0 q
        (by decide) (Nat.ne_of_gt hq))
  have hJ : Subsingleton
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) J) (q + 1)) :=
    projectiveCohomology_subsingleton_of_gt A ι 1 e J (q + 1)
      (Nat.succ_lt_succ hq)
  have hF : Subsingleton
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) F) q) :=
    moduleCohomology_subsingleton_X₃ (Scheme.Hom.idealSequence i)
      (Scheme.Hom.idealSequence_shortExact i) q hOP hJ
  let E :
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) F) q ≃
        Sheaf.H.{u + 1} (moduleAddSheaf Z OZ) q :=
    (projectiveEmbeddingCohomologyLinearEquiv A ι i OZ q).toEquiv
  exact ⟨fun x y => E.symm.injective (@Subsingleton.elim _ hF _ _)⟩

end AlgebraicGeometry.Scheme.Cohomology
