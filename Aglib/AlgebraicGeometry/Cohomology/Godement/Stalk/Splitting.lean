/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Resolution

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementStalkSplit.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 176]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Natural splittings of the Godement resolution after taking an actual module stalk

The actual point projection followed by the stalk/skyscraper counit retracts
an original germ map after taking its actual module stalk.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The original projection to the skyscraper at the chosen point, natural in the sheaf. -/
def godementPointProjection (X : Scheme.{u}) (x : X) :
    godementFirstProduct X ⟶ moduleStalk X x ⋙ moduleSkyscraper X x where
  app M := Pi.π (fun y : X => (moduleSkyscraper X y).obj ((moduleStalk X y).obj M)) x
  naturality {M N} f := by
    change CategoryTheory.Limits.Pi.map
      (fun y => (moduleSkyscraper X y).map ((moduleStalk X y).map f)) ≫ Pi.π _ x = _
    rw [CategoryTheory.Limits.Pi.map_π]
    rfl

/-- The actual natural retraction on the module stalk. -/
def godementStalkRetraction (X : Scheme.{u}) (x : X) :
    godementFirstProduct X ⋙ moduleStalk X x ⟶ moduleStalk X x where
  app M := (moduleStalk X x).map ((godementPointProjection X x).app M) ≫
    (moduleStalkSkyscraperAdjunction X x).counit.app ((moduleStalk X x).obj M)
  naturality {M N} f := by
    dsimp only [Functor.comp_map]
    rw [← Category.assoc, ← Functor.map_comp, (godementPointProjection X x).naturality,
      Functor.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map,
      Category.assoc] using
      (moduleStalk X x).map ((godementPointProjection X x).app M) ≫=
        (moduleStalkSkyscraperAdjunction X x).counit.naturality ((moduleStalk X x).map f)

/-- The germ map is naturally retracted on every actual module stalk. -/
@[reassoc (attr := simp)]
theorem godementStalkRetraction_unit (X : Scheme.{u}) (x : X) (M : X.Modules) :
    (moduleStalk X x).map ((godementFirstProductUnit X).app M) ≫
      (godementStalkRetraction X x).app M = 𝟙 _ := by
  dsimp only [godementStalkRetraction]
  rw [← Category.assoc, ← Functor.map_comp]
  change (moduleStalk X x).map
    ((godementFirstProductUnit X).app M ≫
      Pi.π (fun y : X => (moduleSkyscraper X y).obj ((moduleStalk X y).obj M)) x) ≫
        (moduleStalkSkyscraperAdjunction X x).counit.app ((moduleStalk X x).obj M) =
          𝟙 ((moduleStalk X x).obj M)
  rw [godementFirstProductUnit_π]
  change (moduleStalk X x).map ((moduleStalkSkyscraperAdjunction X x).unit.app M) ≫
    (moduleStalkSkyscraperAdjunction X x).counit.app ((moduleStalk X x).obj M) = _
  exact (moduleStalkSkyscraperAdjunction X x).left_triangle_components M

/-- The original cokernel short exact sequence on the chosen module stalk. -/
def godementStalkShortComplex (X : Scheme.{u}) (x : X) (M : X.Modules) :
    ShortComplex (ModuleCat.{u} (X.presheaf.stalk x)) :=
  (ShortComplex.mk ((godementFirstProductUnit X).app M) ((godementQuotient X).app M)
    (godementUnit_quotient X M)).map (moduleStalk X x)

/-- The actual stalk short exact sequence has a canonical splitting obtained from the
original point projection and the adjunction counit, without an injectivity assumption. -/
def godementStalkSplitting (X : Scheme.{u}) (x : X) (M : X.Modules) :
    (godementStalkShortComplex X x M).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    ((godementUnit_shortExact X M).map_of_exact (moduleStalk X x)).exact
    ((godementStalkRetraction X x).app M) (godementStalkRetraction_unit X x M)
    (((godementUnit_shortExact X M).map_of_exact (moduleStalk X x)).epi_g)

@[reassoc]
theorem godementStalkSplitting_quotient_section (X : Scheme.{u}) (x : X) (M : X.Modules) :
    (moduleStalk X x).map ((godementQuotient X).app M) ≫ (godementStalkSplitting X x M).s =
      𝟙 _ - (godementStalkRetraction X x).app M ≫
        (moduleStalk X x).map ((godementFirstProductUnit X).app M) :=
  (godementStalkSplitting X x M).g_s

/-- The actual quotient section on the stalk, determined by the original retraction. -/
def godementStalkQuotientSection (X : Scheme.{u}) (x : X) :
    godementCokernel X ⋙ moduleStalk X x ⟶ godementFirstProduct X ⋙ moduleStalk X x where
  app M := (godementStalkSplitting X x M).s
  naturality {M N} f := by
    apply (cancel_epi ((moduleStalk X x).map ((godementQuotient X).app M))).mp
    dsimp only [Functor.comp_map]
    rw [← Category.assoc, ← Functor.map_comp, ← (godementQuotient X).naturality,
      Functor.map_comp, Category.assoc]
    rw [← Category.assoc ((moduleStalk X x).map ((godementQuotient X).app M)),
      godementStalkSplitting_quotient_section, godementStalkSplitting_quotient_section]
    dsimp only [Functor.comp_obj]
    rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp]
    congr 1
    have hret := (godementStalkRetraction X x).naturality f
    dsimp only [Functor.comp_map] at hret
    have hunit := (godementFirstProductUnit X).naturality f
    dsimp only [Functor.id_map] at hunit
    rw [← Category.assoc, hret, Category.assoc, ← Functor.map_comp, hunit,
      Functor.map_comp, Category.assoc]

@[reassoc (attr := simp)]
theorem godementStalkQuotientSection_quotient (X : Scheme.{u}) (x : X) (M : X.Modules) :
    (godementStalkQuotientSection X x).app M ≫
      (moduleStalk X x).map ((godementQuotient X).app M) = 𝟙 _ :=
  (godementStalkSplitting X x M).s_g


/-- The actual resolution terms on the chosen module stalk. -/
abbrev godementStalkResolutionTerm (X : Scheme.{u}) (x : X) (n : ℕ) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  godementResolutionTerm X n ⋙ moduleStalk X x

/-- A natural backwards homotopy map supplied by the successive actual stalk splittings. -/
def godementStalkResolutionHomotopy (X : Scheme.{u}) (x : X) (n : ℕ) :
    godementStalkResolutionTerm X x (n + 1) ⟶ godementStalkResolutionTerm X x n where
  app M := (godementStalkRetraction X x).app ((godementIterate X (n + 1)).obj M) ≫
    (godementStalkQuotientSection X x).app ((godementIterate X n).obj M)
  naturality {M N} f := by
    have hret := (godementStalkRetraction X x).naturality ((godementIterate X (n + 1)).map f)
    have hsec := (godementStalkQuotientSection X x).naturality ((godementIterate X n).map f)
    dsimp only [Functor.comp_map] at hret hsec
    change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
    dsimp only [godementStalkResolutionTerm, godementResolutionTerm, Functor.comp_map]
    rw [← Category.assoc, hret, Category.assoc]
    dsimp only [godementIterate, Functor.comp_map] at hsec ⊢
    rw [hsec, Category.assoc]

/-- The contracting identity in resolution degree zero. -/
theorem godementStalkResolutionHomotopy_zero (X : Scheme.{u}) (x : X) (M : X.Modules) :
    ((moduleStalk X x).map ((godementResolutionDifferential X 0).app M) ≫
        (godementStalkResolutionHomotopy X x 0).app M :
          (moduleStalk X x).obj ((godementFirstProduct X).obj M) ⟶
            (moduleStalk X x).obj ((godementFirstProduct X).obj M)) +
      ((godementStalkRetraction X x).app M ≫
        (moduleStalk X x).map ((godementFirstProductUnit X).app M) :
          (moduleStalk X x).obj ((godementFirstProduct X).obj M) ⟶
            (moduleStalk X x).obj ((godementFirstProduct X).obj M)) = 𝟙 _ := by
  change (moduleStalk X x).map
      ((godementQuotient X).app M ≫ (godementFirstProductUnit X).app ((godementCokernel X).obj M)) ≫
        ((godementStalkRetraction X x).app ((godementCokernel X).obj M) ≫
          (godementStalkQuotientSection X x).app M) + _ = _
  rw [Functor.map_comp, Category.assoc,
    ← Category.assoc ((moduleStalk X x).map ((godementFirstProductUnit X).app _)),
    godementStalkRetraction_unit, Category.id_comp]
  have h := (godementStalkSplitting X x M).id
  exact (add_comm _ _).trans h

/-- The contracting identity in every positive resolution degree. -/
theorem godementStalkResolutionHomotopy_succ (X : Scheme.{u}) (x : X) (M : X.Modules) (n : ℕ) :
    ((godementStalkResolutionHomotopy X x n).app M ≫
        (moduleStalk X x).map ((godementResolutionDifferential X n).app M) :
          (godementStalkResolutionTerm X x (n + 1)).obj M ⟶
            (godementStalkResolutionTerm X x (n + 1)).obj M) +
      ((moduleStalk X x).map ((godementResolutionDifferential X (n + 1)).app M) ≫
        (godementStalkResolutionHomotopy X x (n + 1)).app M :
          (godementStalkResolutionTerm X x (n + 1)).obj M ⟶
            (godementStalkResolutionTerm X x (n + 1)).obj M) = 𝟙 _ := by
  dsimp only [godementStalkResolutionHomotopy, godementResolutionDifferential,
    NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app,
    godementStalkResolutionTerm, godementResolutionTerm, Functor.comp_obj]
  rw [Functor.map_comp, Functor.map_comp]
  rw [Category.assoc, godementStalkQuotientSection_quotient_assoc,
    Category.assoc,
    ← Category.assoc ((moduleStalk X x).map ((godementFirstProductUnit X).app _)),
    godementStalkRetraction_unit, Category.id_comp]
  exact (godementStalkSplitting X x ((godementIterate X (n + 1)).obj M)).id

end AlgebraicGeometry.Scheme.Modules.Godement
