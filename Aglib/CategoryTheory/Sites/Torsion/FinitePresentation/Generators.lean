/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-! # Actual free representables and their scalar quotients

The integer free sheaf is the existing sheafified Yoneda construction. Its
scalar quotient is the native cokernel, and its universal property retains
the original section and coefficient maps. The section-value universe and
the larger native Hom universe are related by an explicit `ULift`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.TorsionFinitePresentation

universe t v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- Original evaluation of an abelian sheaf at the specified site object. -/
abbrev evaluation (U : C) : Sheaf J AddCommGrpCat.{max v t} ⥤ Type (max v t) :=
  (sheafSections J AddCommGrpCat.{max v t}).obj (op U) ⋙
    forget AddCommGrpCat.{max v t}

/-- The actual integer free representable represents evaluation in the honest Hom universe. -/
def freeRepresentableEvaluationIso (U : C) :
    coyoneda.obj (op (Hypercohomology.freeAbelianSheaf.{t} J U)) ≅
      evaluation J U ⋙ uliftFunctor.{u} :=
  NatIso.ofComponents
    (fun F => ((Hypercohomology.sectionsEquiv J U F).trans Equiv.ulift.symm).toIso)
    (by
      intro F G q
      ext b
      exact congrArg ULift.up
        (Hypercohomology.sectionsEquiv_naturality J U b q))

/-- The universe comparison changes only the wrapper of the original evaluated section. -/
@[simp]
theorem freeRepresentableEvaluationIso_hom_apply (U : C)
    (F : Sheaf J AddCommGrpCat.{max v t})
    (b : Hypercohomology.freeAbelianSheaf.{t} J U ⟶ F) :
    (TypeCat.Hom.hom
      (X := Hypercohomology.freeAbelianSheaf.{t} J U ⟶ F)
      (Y := ULift.{u} (F.obj.obj (op U)))
      ((freeRepresentableEvaluationIso J U).hom.app F)) b =
      ULift.up (Hypercohomology.sectionsEquiv J U F b) := rfl

/-- The genuine free scalar-quotient sheaf on a representable, as a native cokernel. -/
def freeZModRepresentable (n : ℕ) (U : C) : Sheaf J AddCommGrpCat.{max v t} :=
  cokernel (n • 𝟙 (Hypercohomology.freeAbelianSheaf.{t} J U))

/-- The original cokernel map from the existing integer free representable. -/
abbrev freeZModRepresentableπ (n : ℕ) (U : C) :
    Hypercohomology.freeAbelianSheaf.{t} J U ⟶ freeZModRepresentable J n U :=
  cokernel.π (n • 𝟙 (Hypercohomology.freeAbelianSheaf.{t} J U))

/-- Multiplication by the scalar annihilates the original quotient map. -/
@[simp]
theorem nsmul_freeZModRepresentableπ (n : ℕ) (U : C) :
    n • freeZModRepresentableπ J n U = 0 := by
  simpa only [Preadditive.nsmul_comp, Category.id_comp] using
    (cokernel.condition (n • 𝟙 (Hypercohomology.freeAbelianSheaf.{t} J U)))

/-- The actual scalar-quotient sheaf is killed by its defining scalar. -/
@[simp]
theorem nsmul_id_freeZModRepresentable (n : ℕ) (U : C) :
    n • 𝟙 (freeZModRepresentable J n U) = 0 := by
  apply (cancel_epi (freeZModRepresentableπ J n U)).1
  simp only [Preadditive.comp_nsmul, Category.comp_id,
    nsmul_freeZModRepresentableπ, comp_zero]

/-- The original integer-free relation is precisely the literal section-annihilation equation. -/
theorem freeRepresentable_relation_iff (n : ℕ) (U : C)
    (F : Sheaf J AddCommGrpCat.{max v t})
    (b : Hypercohomology.freeAbelianSheaf.{t} J U ⟶ F) :
    (n • 𝟙 (Hypercohomology.freeAbelianSheaf.{t} J U)) ≫ b = 0 ↔
      n • Hypercohomology.sectionsEquiv J U F b = 0 := by
  have hθ (c : Hypercohomology.freeAbelianSheaf.{t} J U ⟶ F) :
      Hypercohomology.sectionsAddEquiv J U F c =
        Hypercohomology.sectionsEquiv J U F c := rfl
  have hsmul : Hypercohomology.sectionsEquiv J U F (n • b) =
      n • Hypercohomology.sectionsEquiv J U F b :=
    (hθ (n • b)).symm.trans
      ((map_nsmul (Hypercohomology.sectionsAddEquiv J U F) n b).trans
        (congrArg (fun s => n • s) (hθ b)))
  have hzero : Hypercohomology.sectionsEquiv J U F 0 = 0 :=
    (hθ 0).symm.trans (map_zero (Hypercohomology.sectionsAddEquiv J U F))
  rw [Preadditive.nsmul_comp, Category.id_comp]
  constructor
  · intro hb
    exact hsmul.symm.trans
      ((congrArg (Hypercohomology.sectionsEquiv J U F) hb).trans hzero)
  · intro hb
    apply (Hypercohomology.sectionsEquiv J U F).injective
    exact hsmul.trans (hb.trans hzero.symm)

/-- The native scalar quotient represents exactly the original sections killed by `n`. -/
def freeZModSectionsEquiv (n : ℕ) (U : C) (F : Sheaf J AddCommGrpCat.{max v t}) :
    (freeZModRepresentable J n U ⟶ F) ≃
      {s : F.obj.obj (op U) // n • s = 0} :=
  (Cofork.IsColimit.homIso
    (cokernelIsCokernel (n • 𝟙 (Hypercohomology.freeAbelianSheaf.{t} J U))) F).trans
      ((Hypercohomology.sectionsEquiv J U F).subtypeEquiv (by
        intro b
        simpa only [zero_comp] using freeRepresentable_relation_iff J n U F b))

/-- The quotient universal property uses the original quotient map and evaluated section. -/
@[simp]
theorem freeZModSectionsEquiv_val (n : ℕ) (U : C)
    (F : Sheaf J AddCommGrpCat.{max v t}) (b : freeZModRepresentable J n U ⟶ F) :
    (freeZModSectionsEquiv J n U F b).val =
      Hypercohomology.sectionsEquiv J U F (freeZModRepresentableπ J n U ≫ b) := rfl

/-- A killed section is recovered identically through the original quotient map. -/
@[simp]
theorem freeZModSectionsEquiv_symm_π (n : ℕ) (U : C)
    (F : Sheaf J AddCommGrpCat.{max v t}) (s : {s : F.obj.obj (op U) // n • s = 0}) :
    Hypercohomology.sectionsEquiv J U F
        (freeZModRepresentableπ J n U ≫ (freeZModSectionsEquiv J n U F).symm s) = s.val :=
  congrArg Subtype.val ((freeZModSectionsEquiv J n U F).apply_symm_apply s)

/-- The free scalar-quotient property retains every original additive coefficient map. -/
theorem freeZModSectionsEquiv_naturality (n : ℕ) (U : C)
    {F G : Sheaf J AddCommGrpCat.{max v t}}
    (b : freeZModRepresentable J n U ⟶ F) (q : F ⟶ G) :
    (freeZModSectionsEquiv J n U G (b ≫ q)).val =
      q.hom.app (op U) (freeZModSectionsEquiv J n U F b).val := by
  change Hypercohomology.sectionsEquiv J U G
      (freeZModRepresentableπ J n U ≫ (b ≫ q)) =
    q.hom.app (op U)
      (Hypercohomology.sectionsEquiv J U F (freeZModRepresentableπ J n U ≫ b))
  rw [← Category.assoc]
  exact Hypercohomology.sectionsEquiv_naturality J U _ q

end CategoryTheory.Sheaf.TorsionFinitePresentation
