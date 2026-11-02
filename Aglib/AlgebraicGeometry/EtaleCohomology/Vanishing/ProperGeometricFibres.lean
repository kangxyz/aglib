/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsField
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-! # Proper higher-image vanishing from original geometric-fibre cohomology

Proper base change identifies the original higher-image stalk with the
original higher image of the pulled-back coefficient over a separably closed
field. The original cohomology-to-sections map and terminal germ then transfer
vanishing from original `Sheaf.H`. All algebraically closed geometric stalks
detect zero sheaves over an arbitrary base.

The geometric-fibre vanishing hypothesis is explicit. This is an assembly
lemma, not a proof of a positive-dimensional cohomological-dimension bound.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

private theorem isZero_identityStalk_higherDirectImage_of_H
    (K : Type u) [Field K] [IsSepClosed K]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (G : AbelianSheaf.{u, u + 1} Y) (q : ℕ)
    (hH : Subsingleton (Sheaf.H.{e} G q)) :
    IsZero ((pointSmallEtale (𝟙 (Spec (.of K)))).sheafFiber
      (A := AddCommGrpCat.{u + 1}) |>.obj ((higherDirectImage p q).obj G)) := by
  let := hH
  have hsections : Subsingleton
      (((higherDirectImage p q).obj G).obj.obj (op (etaleTerminal (Spec (.of K))))) :=
    (cohomologyToHigherSections_bijective_of_isSepClosed K p G q).2.subsingleton
  have hzero : IsZero
      (((higherDirectImage p q).obj G).obj.obj (op (etaleTerminal (Spec (.of K))))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr hsections
  let γ := (pointSmallEtale (𝟙 (Spec (.of K)))).toPresheafFiber
    (etaleTerminal (Spec (.of K))) (fieldTerminalPoint K)
    ((higherDirectImage p q).obj G).obj
  have : IsIso γ := by
    dsimp only [γ]
    infer_instance
  exact hzero.of_iso (asIso γ).symm

/-- Vanishing of the original cohomology of one literal geometric fibre
implies vanishing of the corresponding original higher-image stalk.
The original fibre Ext universe is arbitrary. No dimension or finiteness
assumption on the base is needed. -/
theorem isZero_stalk_higherDirectImage_of_geometricFiber_H
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) (q : ℕ)
    (K : Type u) [Field K] [IsSepClosed K] (η : Spec (.of K) ⟶ S)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback f η))]
    (hH : Subsingleton
      (Sheaf.H.{e} ((inverseImage (pullback.fst f η)).obj F) q)) :
    IsZero ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.obj
      ((higherDirectImage f q).obj F)) := by
  let L := (higherDirectImage f q).obj F
  let Φ := (pointSmallEtale (𝟙 (Spec (.of K)))).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  let H : IsPullback (pullback.fst f η) (pullback.snd f η) f η :=
    IsPullback.of_hasPullback f η
  let β := (higherBaseChangeMap f (pullback.snd f η) η (pullback.fst f η)
    H.w.symm q).app F
  have : IsIso β :=
    Proper.properHigherBaseChange_isIso f (pullback.snd f η) η
      (pullback.fst f η) H F hF q
  have htarget : IsZero
      (Φ.obj ((higherDirectImage (pullback.snd f η) q).obj
        ((inverseImage (pullback.fst f η)).obj F))) :=
    isZero_identityStalk_higherDirectImage_of_H K (pullback.snd f η)
      ((inverseImage (pullback.fst f η)).obj F) q hH
  have hpullback : IsZero (Φ.obj ((inverseImage η).obj L)) :=
    htarget.of_iso (Φ.mapIso (asIso β))
  have hsource : IsZero
      ((pointSmallEtale (𝟙 (Spec (.of K)) ≫ η)).sheafFiber
        (A := AddCommGrpCat.{u + 1}) |>.obj L) :=
    hpullback.of_iso ((StalkInverseImage.stalkUnitNatIso η
      (𝟙 (Spec (.of K)))).app L)
  simpa only [Category.id_comp] using hsource

/-- Original cohomology vanishing on every algebraically closed geometric
fibre gives vanishing of the original proper higher direct image of a locally
torsion coefficient. The independent supplied fibre Ext universe is retained;
the higher-image object itself is the native natural-degree right derivative.
-/
theorem isZero_higherDirectImage_obj_of_geometricFiber_H
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) (q : ℕ)
    [∀ (K : Type u) [Field K] [IsAlgClosed K] (η : Spec (.of K) ⟶ S),
      HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback f η))]
    (hH : ∀ (K : Type u) [Field K] [IsAlgClosed K] (η : Spec (.of K) ⟶ S),
      Subsingleton (Sheaf.H.{e} ((inverseImage (pullback.fst f η)).obj F) q)) :
    IsZero ((higherDirectImage f q).obj F) := by
  let L := (higherDirectImage f q).obj F
  have : IsIso (0 : L ⟶ L) := by
    apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 S)
    intro K _ _ η _
    have hzero := isZero_stalk_higherDirectImage_of_geometricFiber_H
      f F hF q K η (hH K η)
    exact hzero.isIso hzero _
  exact (isIsoZero_iff_source_target_isZero L L).mp inferInstance |>.1

section StandardExt

attribute [local instance] HasExt.standard

/-- The same geometric-fibre criterion with the native standard Ext instances
supplied internally; no fibre Ext-existence hypothesis remains. -/
theorem isZero_higherDirectImage_obj_of_geometricFiber_H_standard
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) (q : ℕ)
    (hH : ∀ (K : Type u) [Field K] [IsAlgClosed K] (η : Spec (.of K) ⟶ S),
      Subsingleton (Sheaf.H.{u + 2} ((inverseImage (pullback.fst f η)).obj F) q)) :
    IsZero ((higherDirectImage f q).obj F) := by
  let : ∀ (K : Type u) [Field K] [IsAlgClosed K] (η : Spec (.of K) ⟶ S),
      HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (pullback f η)) :=
    fun K _ _ η => HasExt.standard _
  exact isZero_higherDirectImage_obj_of_geometricFiber_H f F hF q hH

end StandardExt

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
