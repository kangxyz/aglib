/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Section.Span

/-! # Exact original closed-section Godement span consumers

Adapted from `QuillenTest/GodementClosedSectionSpan.lean` in the delivered archive.

The source-total arrow retains the literal original geometric section inverse
followed by the actual pushed augmentation. Both arrows keep their original
quasi-isomorphism statements under exactly the original geometric hypotheses.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Godement

namespace AglibTest.ArchiveGodementClosedSectionSpan

/-- The source-total arrow has exactly its original component, definitionally. -/
theorem source_arrow_original_component {X Y : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ X)
    (h : s ≫ p = 𝟙 X) (K : CochainComplex.Plus X.Modules) :
    (sectionSourceTotalToRepeated s p h).app K =
      (sectionComplexPlusIso s p h).inv.app ((godementTotalPlus X).obj K) ≫
        (Scheme.Modules.pushforward p).mapCochainComplexPlus.map
          ((godementTotalPlusUnit Y).app
            ((Scheme.Modules.pushforward s).mapCochainComplexPlus.obj
              ((godementTotalPlus X).obj K))) := rfl

/-- Closed pushforward gives the original first span arrow its genuine weak law. -/
theorem original_first_arrow_quasiIso {X Y : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ X)
    [IsClosedImmersion s] (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((sectionTotalToRepeated s p).app K).hom :=
  sectionTotalToRepeated_quasiIso s p K

/-- The second original span arrow is weak with the original section equality alone. -/
theorem original_source_arrow_quasiIso {X Y : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ X)
    (h : s ≫ p = 𝟙 X) (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((sectionSourceTotalToRepeated s p h).app K).hom :=
  sectionSourceTotalToRepeated_quasiIso s p h K

end AglibTest.ArchiveGodementClosedSectionSpan
