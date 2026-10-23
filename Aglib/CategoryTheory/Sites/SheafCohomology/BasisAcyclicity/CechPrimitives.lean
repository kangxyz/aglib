/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoverResolution
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Primitive transport through the original sheafification adjunction

The original free-presheaf differential and its sheafification have equivalent
primitive equations. This is a literal adjunction calculation, without an
injectivity, acyclicity, or cohomological-vanishing hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Presheaf.Cech

universe c h r

variable {C : Type c} [Category.{h} C]
  {F G : Cᵒᵖ ⥤ Type r} (f : F ⟶ G)
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{r}]
  (A : Sheaf J AddCommGrpCat.{r})

/-- Exact primitive equations in the original free-presheaf cochains give
exact primitive equations in the original sheafified free cochains. -/
theorem sheaf_primitive_of_free_primitive (n : ℕ)
    (h : ∀ c : (freeComplex f).X (n + 1) ⟶ A.obj,
      (freeComplex f).d (n + 2) (n + 1) ≫ c = 0 →
      ∃ b : (freeComplex f).X n ⟶ A.obj, (freeComplex f).d (n + 1) n ≫ b = c)
    (c : (sheafComplex f J).X (n + 1) ⟶ A)
    (hc : (sheafComplex f J).d (n + 2) (n + 1) ≫ c = 0) :
    ∃ b : (sheafComplex f J).X n ⟶ A, (sheafComplex f J).d (n + 1) n ≫ b = c := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{r}
  let e (i : ℕ) := adj.homAddEquiv ((freeComplex f).X i) A
  have hd (i : ℕ) (b : (sheafComplex f J).X i ⟶ A) :
      e (i + 1) ((sheafComplex f J).d (i + 1) i ≫ b) =
        (freeComplex f).d (i + 1) i ≫ e i b :=
    adj.homEquiv_naturality_left _ _
  have hc' : (freeComplex f).d (n + 2) (n + 1) ≫ e (n + 1) c = 0 := by
    calc
      _ = e (n + 2) ((sheafComplex f J).d (n + 2) (n + 1) ≫ c) :=
        (hd (n + 1) c).symm
      _ = e (n + 2) 0 := congrArg (e (n + 2)) hc
      _ = 0 := map_zero (e (n + 2))
  obtain ⟨b, hb⟩ := h (e (n + 1) c) hc'
  refine ⟨(e n).symm b, (e (n + 1)).injective ?_⟩
  calc
    _ = (freeComplex f).d (n + 1) n ≫ e n ((e n).symm b) := hd n ((e n).symm b)
    _ = (freeComplex f).d (n + 1) n ≫ b :=
      congrArg (fun x => (freeComplex f).d (n + 1) n ≫ x) ((e n).apply_symm_apply b)
    _ = e (n + 1) c := hb

end CategoryTheory.Presheaf.Cech
