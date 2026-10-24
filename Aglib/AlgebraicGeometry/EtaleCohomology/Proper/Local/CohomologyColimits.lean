/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.GenuineModules
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.QcqsComparison

/-! # Original cohomology colimits of genuine coefficient diagrams

Fixed-scheme coefficient continuity on a qcqs scheme proves preservation of
the original filtered colimits by its original cohomology functor. Scalar
forgetting preserves colimits at the coefficient/index size. The original
inverse image is a left adjoint. Their compositions therefore preserve the
source and pulled-back target cohomology colimits of any genuine module
diagram at that size, at every modulus.

The two Ext universes are independent. Their group categories must have the
specified index colimits; at Ext universe `u + 2` these colimits are supplied
internally. The comparison maps below are the actual native `colimit.post`
maps. Module injective acyclicity remains a separate assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u eX eS

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

variable {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]

/-- The actual source cohomology functor preserves the colimit of every
genuine module diagram at the original coefficient/index size. -/
theorem genuineCohomology_preservesColimit
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasColimitsOfShape I AddCommGrpCat.{eX}]
    (n : ℕ) (D : I ⥤ Reduction.ZModSheaf X n) (q : ℕ) :
    PreservesColimit D (Reduction.zmodUnderlying X n ⋙ cohomologyFunctor.{u, eX} X q) := by
  have : PreservesColimitsOfShape I (cohomologyFunctor.{u, eX} X q) :=
    qcqsCohomologyFunctor_preservesColimitsOfShape X q
  infer_instance

/-- After the original inverse image along an arbitrary scheme map, target
cohomology preserves the same genuine coefficient colimit. Only the target
scheme needs to be qcqs for this assertion. -/
theorem genuinePullbackCohomology_preservesColimit
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    [HasColimitsOfShape I AddCommGrpCat.{eS}]
    (i : S ⟶ X) (n : ℕ) (D : I ⥤ Reduction.ZModSheaf X n) (q : ℕ) :
    PreservesColimit D
      (Reduction.zmodUnderlying X n ⋙ inverseImage i ⋙ cohomologyFunctor.{u, eS} S q) := by
  have : (inverseImage i).IsLeftAdjoint := (inverseImageAdjunction i).isLeftAdjoint
  have : PreservesColimitsOfShape I (cohomologyFunctor.{u, eS} S q) :=
    qcqsCohomologyFunctor_preservesColimitsOfShape S q
  infer_instance

/-- Both original universal cohomology comparisons are isomorphisms. The
source and target Ext models and their group colimits remain independent.
Each map is normalized by the native `colimit.ι_post` equation on the
original genuine diagram's colimit injections. -/
theorem genuineCohomologyColimitComparisons_isIso
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    [HasColimitsOfShape I AddCommGrpCat.{eX}]
    [HasColimitsOfShape I AddCommGrpCat.{eS}]
    (i : S ⟶ X) (n : ℕ) (D : I ⥤ Reduction.ZModSheaf X n) (p q : ℕ) :
    IsIso (colimit.post D
      (Reduction.zmodUnderlying X n ⋙ cohomologyFunctor.{u, eX} X p)) ∧
    IsIso (colimit.post D
      (Reduction.zmodUnderlying X n ⋙ inverseImage i ⋙ cohomologyFunctor.{u, eS} S q)) := by
  have : PreservesColimit D
      (Reduction.zmodUnderlying X n ⋙ cohomologyFunctor.{u, eX} X p) :=
    genuineCohomology_preservesColimit n D p
  have : PreservesColimit D
      (Reduction.zmodUnderlying X n ⋙ inverseImage i ⋙ cohomologyFunctor.{u, eS} S q) :=
    genuinePullbackCohomology_preservesColimit i n D q
  exact ⟨inferInstance, inferInstance⟩

section StandardExt

attribute [local instance] HasExt.standard

/-- The preservation hypotheses for the local criterion, with source degree
zero and every target degree. At Ext universe `u + 2`, both Ext models and
the group colimits of the original `Type (u + 1)` index are internal. -/
theorem genuineCohomologyColimits_standard
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (i : S ⟶ X) (n : ℕ) (D : I ⥤ Reduction.ZModSheaf X n) :
    PreservesColimit D
      (Reduction.zmodUnderlying X n ⋙ cohomologyFunctor.{u, u + 2} X 0) ∧
    ∀ q : ℕ, PreservesColimit D
      (Reduction.zmodUnderlying X n ⋙ inverseImage i ⋙ cohomologyFunctor.{u, u + 2} S q) := by
  have : HasColimitsOfShape I AddCommGrpCat.{u + 2} := inferInstance
  exact ⟨genuineCohomology_preservesColimit n D 0,
    fun q => genuinePullbackCohomology_preservesColimit i n D q⟩

end StandardExt

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
