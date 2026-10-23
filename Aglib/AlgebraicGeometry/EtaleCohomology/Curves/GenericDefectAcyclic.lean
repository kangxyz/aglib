/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ClosedSupportAcyclic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericDefectExhaustion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsCoefficientContinuity

/-! # Positive original cohomology of the actual generic-unit defects -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} [IsNoetherian X]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Finite-support coefficient continuity is computed in a standard large Ext
universe, then transported to the arbitrary original Ext universe. -/
theorem subsingleton_H_of_finiteSupportColimit_isIso
    (F : AbelianSheaf.{u, u + 1} X) [IsIso (finiteSupportColimitMap F)]
    (hsep : ∀ x : X, IsClosed ({x} : Set X) → IsSepClosed (X.residueField x))
    (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H.{w} F q) := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := HasExt.standard _
  let G := finiteSupportDiagram F
  let H := (Sheaf.functorH X.smallEtaleTopology q :
    AbelianSheaf.{u, u + 1} X ⥤ AddCommGrpCat.{u + 2})
  have hzero : IsZero (G ⋙ H) := by
    apply Functor.isZero
    intro W
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    exact pointSupportedSubobject_subsingleton_H F (finiteSupportSet X W)
      (finiteSupportSet_finite X W) (finiteSupportSet_closed_points X W)
      (fun x => hsep x.val (finiteSupportSet_closed_points X W x.val x.property)) q hq
  have hc : IsZero (colimit (G ⋙ H)) := (colimit.isColimit (G ⋙ H)).isZero_pt hzero
  have hcol : IsZero (H.obj (colimit G)) :=
    hc.of_iso (Continuity.qcqsCoefficientFilteredColimitIso G q).symm
  have hF : IsZero (H.obj F) :=
    hcol.of_iso (H.mapIso (asIso (finiteSupportColimitMap F))).symm
  let : Subsingleton (Sheaf.H.{u + 2} F q) := AddCommGrpCat.isZero_iff_subsingleton.mp hF
  let e : Sheaf.H.{w} F q ≃ Sheaf.H.{u + 2} F q := Ext.chgUniv
  exact e.injective.subsingleton

/-- The original generic-unit kernel has zero positive cohomology on a Noetherian
curve whose closed residue fields are separably closed. -/
theorem genericKernel_subsingleton_H (hdim : topologicalKrullDim X ≤ 1)
    (hsep : ∀ x : X, IsClosed ({x} : Set X) → IsSepClosed (X.residueField x))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} (kernel (genericArtinUnit X)) q) := by
  let := genericKernel_finiteSupportColimit_isIso hdim
  exact subsingleton_H_of_finiteSupportColimit_isIso _ hsep q hq

/-- The original generic-unit cokernel has zero positive cohomology under the same
hypotheses, without replacing a section by a globally chosen quotient representative. -/
theorem genericCokernel_subsingleton_H (hdim : topologicalKrullDim X ≤ 1)
    (hsep : ∀ x : X, IsClosed ({x} : Set X) → IsSepClosed (X.residueField x))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} (cokernel (genericArtinUnit X)) q) := by
  let := genericCokernel_finiteSupportColimit_isIso hdim
  exact subsingleton_H_of_finiteSupportColimit_isIso _ hsep q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
