/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.FiniteModificationTorsion
public import Aglib.AlgebraicGeometry.Normalization.FiniteTypeField
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR
public import Aglib.AlgebraicGeometry.Dimension.DenseOpenComplement
public import Aglib.AlgebraicGeometry.Dimension.Finite

/-! # Original normalization reduction for torsion cohomology

The finite normalization of an integral proper field scheme is normal,
birational, and surjective. The actual proper birational generic-point
extension gives an isomorphism open. Its produced boundary has smaller
dimension. The original unit-cokernel sequence reduces vanishing to the
normalization in the same degree and the boundary in the preceding degree.
No chosen normalization, common coefficient annihilator, or perfection of
the field is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Same-degree vanishing on normal integral proper schemes and
preceding-degree vanishing in one smaller dimension imply vanishing on
integral proper schemes, through their original finite normalization. -/
theorem subsingleton_H_of_normal_and_boundary
    {k : Type u} [Field k] (d n : ℕ)
    (hnormal : ∀ (Y : Scheme.{u}) [IsIntegral Y] (pY : Y ⟶ Spec (.of k)) [IsProper pY],
      NormalStalks Y → topologicalKrullDim Y ≤ (d + 1 : ℕ) →
        ∀ G : AbelianSheaf.{u, u + 1} Y, IsTorsion Y G →
          Subsingleton (Sheaf.H.{u + 2} G (n + 1)))
    (hboundary : ∀ (Z : Scheme.{u}) (pZ : Z ⟶ Spec (.of k)) [IsProper pZ],
      topologicalKrullDim Z ≤ (d : ℕ) →
        ∀ G : AbelianSheaf.{u, u + 1} Z, IsTorsion Z G →
          Subsingleton (Sheaf.H.{u + 2} G n))
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    Subsingleton (Sheaf.H.{e} F (n + 1)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  let γ := X.fromSpecStalk (genericPoint X)
  let Y := γ.normalization
  let b : Y ⟶ X := γ.fromNormalization
  let : IsIntegral Y := inferInstanceAs (IsIntegral γ.normalization)
  let : IsFinite b := genericNormalization_isFinite_of_finiteType_field k X p
  let : IsDominant b := genericNormalization_isDominant X
  let : Surjective b :=
    surjective_of_isDominant_of_isClosed_range b b.isClosedMap.isClosed_range
  have hff := genericNormalization_fieldMap_isIso X
  obtain ⟨U, hηU, hUiso⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_valuationRing b hff (genericPoint X)
  let : IsIso (b ∣_ U) := hUiso
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨genericPoint X, hηU⟩)
  obtain ⟨Z, i, hi, hcomp, hdimZ⟩ :=
    U.ι.exists_closedComplement_topologicalKrullDim_le d hdim
  let : IsClosedImmersion i := hi
  let : IsIso (pullback.snd b U.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  have hY : Subsingleton (Sheaf.H.{u + 2} ((inverseImage b).obj F) (n + 1)) :=
    hnormal Y (b ≫ p) (genericNormalization_normalStalks X)
      (b.topologicalKrullDim_le_of_isFinite.trans hdim) _ (hF.inverseImage b)
  exact subsingleton_H_of_finiteModification_torsion b U.ι i hcomp F hF n hY
    (hboundary Z (i ≫ p) hdimZ)

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
