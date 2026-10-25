/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.HigherDirectImageColimits
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Colimit

/-! # Original higher exchange on internally torsion coefficients

Both original exchange functors preserve the actual sequential coefficient
colimit for qcqs vertical maps. Naturality and the literal positive factorial-
annihilator cocone reduce its component at a torsion sheaf to its components
at genuinely killed coefficients. No uniform annihilator is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

private theorem natTrans_colimit_post
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    (L R : C ⥤ D) (α : L ⟶ R) (K : J ⥤ C) :
    colimit.post K L ≫ α.app (colimit K) =
      colim.map (Functor.whiskerLeft K α) ≫ colimit.post K R := by
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_post_assoc, colimit.ι_map_assoc, colimit.ι_post]
  exact α.naturality (colimit.ι K j)

private theorem natTrans_isIso_at_colimit
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    (L R : C ⥤ D) (α : L ⟶ R) (K : J ⥤ C)
    [PreservesColimit K L] [PreservesColimit K R]
    (c : Cocone K) (hc : IsColimit c)
    (hα : ∀ j, IsIso (α.app (K.obj j))) : IsIso (α.app c.pt) := by
  let (j : J) : IsIso ((Functor.whiskerLeft K α).app j) := hα j
  let : IsIso (Functor.whiskerLeft K α) :=
    NatIso.isIso_of_isIso_app (Functor.whiskerLeft K α)
  let : IsIso (α.app (colimit K)) := by
    apply (isIso_comp_left_iff (colimit.post K L) (α.app (colimit K))).mp
    rw [natTrans_colimit_post L R α K]
    infer_instance
  let e : colimit K ≅ c.pt := (colimit.isColimit K).coconePointUniqueUpToIso hc
  apply (isIso_comp_left_iff (L.map e.hom) (α.app c.pt)).mp
  rw [α.naturality e.hom]
  infer_instance

universe w

private theorem natTrans_isIso_of_internalTorsion
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    [HasColimitsOfShape ℕ D]
    (L R : Sheaf J AddCommGrpCat.{w} ⥤ D) (α : L ⟶ R)
    [PreservesColimitsOfShape ℕ L] [PreservesColimitsOfShape ℕ R]
    (hbounded : ∀ (n : ℕ), n ≠ 0 →
      ∀ F : Sheaf J AddCommGrpCat.{w}, n • 𝟙 F = 0 → IsIso (α.app F))
    (F : Sheaf J AddCommGrpCat.{w}) (hF : Sheaf.IsTorsion F) : IsIso (α.app F) :=
  natTrans_isIso_at_colimit L R α (Sheaf.factorialAnnihilatorDiagram F)
    (Sheaf.factorialAnnihilatorCocone F) (Sheaf.factorialAnnihilatorCoconeIsColimit F hF)
    (fun i => hbounded (i + 1).factorial
      (ne_of_gt (Sheaf.factorialAnnihilatorDiagram_exponent_pos i))
      ((Sheaf.factorialAnnihilatorDiagram F).obj i)
      (Sheaf.factorialAnnihilatorDiagram_annihilated F i))

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']

/-- For qcqs vertical maps, comparison on every genuinely positive killed
coefficient implies invertibility of the defined higher exchange on every
internally torsion coefficient. All four derived models remain independent. -/
theorem higherBaseChangeMap_isIso_of_torsion_of_killed (q : ℕ)
    (hbounded : ∀ (n : ℕ), n ≠ 0 →
      ∀ F : AbelianSheaf.{u, u + 1} X, n • 𝟙 F = 0 →
        IsIso ((higherBaseChangeMap f f' g g' h q).app F))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) := by
  let : PreservesColimitsOfShape ℕ (higherDirectImage f q) :=
    Continuity.higherDirectImage_preservesSequentialColimits f q
  let : PreservesColimitsOfShape ℕ (higherDirectImage f' q) :=
    Continuity.higherDirectImage_preservesSequentialColimits f' q
  let L := higherDirectImage f q ⋙ inverseImage g
  let R := inverseImage g' ⋙ higherDirectImage f' q
  let α : L ⟶ R := higherBaseChangeMap f f' g g' h q
  let : PreservesColimitsOfShape ℕ L := inferInstance
  let : PreservesColimitsOfShape ℕ R := inferInstance
  exact natTrans_isIso_of_internalTorsion L R α hbounded F hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
