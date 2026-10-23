/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic
public import Mathlib.CategoryTheory.Yoneda

/-! # The original integer source at a terminal site object

The constant integer sheaf and the free representable of a terminal object
represent the same actual section functor. The canonical comparison retains
that evaluation, so it can transport original Ext classes without changing
the cohomology theory.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Hypercohomology

universe c h t

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h t}] {T : C} (hT : IsTerminal T)

/-- The original constant integer sheaf is canonically the free representable
of a terminal site object. -/
def constantIntegerFreeTerminalIso :
    (constantSheaf J AddCommGrpCat.{max h t}).obj
      (AddCommGrpCat.of (ULift.{max h t} ℤ)) ≅ freeAbelianSheaf.{t} J T := by
  let E := ((sheafSections J AddCommGrpCat.{max h t}).obj (op T)) ⋙
    forget AddCommGrpCat.{max h t}
  let c : E.CorepresentableBy ((constantSheaf J AddCommGrpCat.{max h t}).obj
      (AddCommGrpCat.of (ULift.{max h t} ℤ))) :=
    { homEquiv := ModuleCoefficients.constantHomSectionsEquiv hT _
      homEquiv_comp g a := ModuleCoefficients.constantHomSectionsEquiv_naturality hT g a }
  let f : E.CorepresentableBy (freeAbelianSheaf.{t} J T) :=
    { homEquiv := sectionsEquiv J T _
      homEquiv_comp g a := sectionsEquiv_naturality J T a g }
  exact c.uniqueUpToIso f

/-- The source comparison is normalized by the actual section represented by
an arrow out of the free representable. -/
theorem constantIntegerFreeTerminalIso_evaluation
    (F : Sheaf J AddCommGrpCat.{max h t}) (a : freeAbelianSheaf.{t} J T ⟶ F) :
    ModuleCoefficients.constantHomSectionsEquiv hT F
      ((constantIntegerFreeTerminalIso J hT).hom ≫ a) = sectionsEquiv J T F a := by
  rw [ModuleCoefficients.constantHomSectionsEquiv_naturality]
  change a.hom.app (op T)
    (ModuleCoefficients.constantHomSectionsEquiv hT _
      ((ModuleCoefficients.constantHomSectionsEquiv hT _).symm
        (sectionsEquiv J T _ (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  simpa only [Category.id_comp] using (sectionsEquiv_naturality J T (𝟙 _) a).symm

end CategoryTheory.Sheaf.Hypercohomology
