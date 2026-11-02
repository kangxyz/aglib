/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedPullbackUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeSections

/-! # Original connected base change on global sections

The literal ordinary exchange is tested on original global sections. The
original whole comparison equation and the two original horizontal section
pullbacks prove invertibility on these sections for bounded coefficients.
This does not assert that direct image is conservative or that the exchange
is already an isomorphism of sheaves. Local connected factorization for a
smooth morphism is a separate geometric construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/-- Cancel the complete original section square in its single category. -/
private theorem comparison_isIso_of_section_square
    {C : Type*} [Category C] {A B D E R : C}
    (a : A ⟶ B) (m : B ⟶ D) (e : D ≅ R) (d : A ≅ E) (c : E ⟶ R)
    [IsIso a] [IsIso c] (h : a ≫ m ≫ e.hom = d.hom ≫ c) : IsIso m := by
  have : IsIso (a ≫ m ≫ e.hom) := by
    rw [h]
    infer_instance
  let : IsIso (m ≫ e.hom) := IsIso.of_isIso_comp_left a (m ≫ e.hom)
  exact IsIso.of_isIso_comp_right m e.hom

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Original direct image retains a specified annihilator on the coefficient. -/
theorem directImage_nsmul_id_eq_zero_of_killed
    {X S : Scheme.{u}} (f : X ⟶ S) (F : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (hF : n • 𝟙 F = 0) : n • 𝟙 ((directImage f).obj F) = 0 := by
  have h := congrArg (fun a : F ⟶ F => (directImage f).map a) hF
  simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] using h

/-- The literal Cartesian ordinary exchange induces an isomorphism on
original global sections for an arbitrary bounded coefficient. This is a
section theorem, not a claim that the original exchange sheaf map is invertible. -/
theorem baseChangeMap_globalSections_isIso_of_geometricallyConnected
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] [GeometricallyConnected g] [UniversallyOpen g]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso ((globalSections S').map
      ((baseChangeMap f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).app F)) := by
  let : IsIso (globalSectionsPullback g ((directImage f).obj F)) :=
    globalSectionsPullback_isIso_of_geometricallyConnected g ((directImage f).obj F)
      n hn (directImage_nsmul_id_eq_zero_of_killed f F n hF)
  let : IsIso (globalSectionsPullback (pullback.snd g f) F) :=
    globalSectionsPullback_isIso_of_geometricallyConnected (pullback.snd g f) F n hn hF
  exact comparison_isIso_of_section_square
    (globalSectionsPullback g ((directImage f).obj F))
    ((globalSections S').map
      ((baseChangeMap f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).app F))
    ((directImageGlobalSectionsIso (pullback.fst g f)).app
      ((inverseImage (pullback.snd g f)).obj F))
    ((directImageGlobalSectionsIso f).app F)
    (globalSectionsPullback (pullback.snd g f) F)
    (baseChangeMap_globalSections f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition F)

end AlgebraicGeometry.Scheme.EtaleCohomology
