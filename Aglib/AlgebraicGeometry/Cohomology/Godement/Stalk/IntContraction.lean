/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Godement.Stalk.Splitting

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementStalkIntContraction.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 192]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # The actual natural stalk contraction in integer resolution degrees -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The actual integer resolution term on the chosen module stalk. -/
abbrev godementStalkIntTerm (X : Scheme.{u}) (x : X) (q : ℤ) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  godementResolutionInt X ⋙ HomologicalComplex.eval _ _ q ⋙ moduleStalk X x

/-- The original zero-extension term is naturally the original nonnegative term. -/
def godementStalkIntTermIso (X : Scheme.{u}) (x : X) (q : ℤ) (k : ℕ) (h : (k : ℤ) = q) :
    godementStalkIntTerm X x q ≅ godementStalkResolutionTerm X x k :=
  CategoryTheory.Functor.isoWhiskerRight
    (CategoryTheory.Functor.isoWhiskerLeft (godementResolution X)
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso X.Modules h)) (moduleStalk X x)

/-- The zero-degree original germ is transported by the canonical zero-extension iso. -/
@[reassoc]
theorem godementIntGerm_XIso (X : Scheme.{u}) (M : X.Modules) :
    godementIntGerm X M ≫ (godementResolutionIntXIso X M 0 0 (by simp)).hom =
      (godementFirstProductUnit X).app M := by
  dsimp only [godementIntGerm, godementResolutionIntUnit, godementResolutionIntXIso,
    godementResolutionInt,
    ComplexShape.Embedding.extendFunctor]
  simp only [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f]
  rw [HomologicalComplex.extendMap_f ((godementResolutionUnit X).app M)
    ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp)]
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    godementResolutionUnit_f_zero]

/-- The actual natural backwards map for an original vertical backstep. -/
def godementStalkIntBack (X : Scheme.{u}) (x : X) (q r : ℤ) (hqr : r + 1 = q) :
    godementStalkIntTerm X x q ⟶ godementStalkIntTerm X x r :=
  if hr : 0 ≤ r then
    (godementStalkIntTermIso X x q (r.toNat + 1) (by omega)).hom ≫
      godementStalkResolutionHomotopy X x r.toNat ≫
        (godementStalkIntTermIso X x r r.toNat (by omega)).inv
  else 0

@[simp]
theorem godementStalkIntBack_negative (X : Scheme.{u}) (x : X) (q r : ℤ)
    (hqr : r + 1 = q) (hr : r < 0) : godementStalkIntBack X x q r hqr = 0 := by
  unfold godementStalkIntBack
  rw [dite_eq_right (by omega)]

@[simp]
theorem godementStalkIntBack_cast (X : Scheme.{u}) (x : X) (k : ℕ) :
    godementStalkIntBack X x (k + 1) k (by omega) =
      (godementStalkIntTermIso X x (k + 1) (k + 1) (by omega)).hom ≫
        godementStalkResolutionHomotopy X x k ≫
          (godementStalkIntTermIso X x k k rfl).inv := by
  unfold godementStalkIntBack
  rw [dite_eq_left (by omega)]
  simp only [Int.toNat_natCast]

/-- The actual natural projection of the zero-resolution term back to the original stalk. -/
def godementStalkIntRetraction (X : Scheme.{u}) (x : X) :
    godementStalkIntTerm X x 0 ⟶ moduleStalk X x :=
  (godementStalkIntTermIso X x 0 0 (by simp)).hom ≫ godementStalkRetraction X x

/-- The original natural germ map after taking the original module stalk. -/
def godementStalkIntGerm (X : Scheme.{u}) (x : X) :
    moduleStalk X x ⟶ godementStalkIntTerm X x 0 where
  app M := (moduleStalk X x).map (godementIntGerm X M)
  naturality {M N} f := by
    dsimp only [godementStalkIntTerm, Functor.comp_map, HomologicalComplex.eval]
    rw [← Functor.map_comp, godementIntGerm_naturality, Functor.map_comp]

@[reassoc (attr := simp)]
theorem godementStalkIntGerm_retraction (X : Scheme.{u}) (x : X) (M : X.Modules) :
    (godementStalkIntGerm X x).app M ≫ (godementStalkIntRetraction X x).app M = 𝟙 _ := by
  change (moduleStalk X x).map (godementIntGerm X M) ≫
    ((moduleStalk X x).map (godementResolutionIntXIso X M 0 0 (by simp)).hom ≫
      (godementStalkRetraction X x).app M) = _
  rw [← Category.assoc, ← Functor.map_comp, godementIntGerm_XIso,
    godementStalkRetraction_unit]
  rfl

/-- The actual integer resolution differential on the module stalk. -/
def godementStalkIntD (X : Scheme.{u}) (x : X) (q r : ℤ) :
    godementStalkIntTerm X x q ⟶ godementStalkIntTerm X x r where
  app M := (moduleStalk X x).map (((godementResolutionInt X).obj M).d q r)
  naturality {M N} f := by
    dsimp only [godementStalkIntTerm, Functor.comp_map, HomologicalComplex.eval]
    rw [← Functor.map_comp, HomologicalComplex.Hom.comm, Functor.map_comp]


/-- The original integer differential is conjugated by the original extension term isos. -/
theorem godementStalkIntD_cast (X : Scheme.{u}) (x : X) (M : X.Modules) (k l : ℕ) :
    (godementStalkIntD X x k l).app M =
      (godementStalkIntTermIso X x k k rfl).hom.app M ≫
        (moduleStalk X x).map (((godementResolution X).obj M).d k l) ≫
          (godementStalkIntTermIso X x l l rfl).inv.app M := by
  change (moduleStalk X x).map
      (((godementResolution X).obj M).extend ComplexShape.embeddingUpNat |>.d k l) = _
  change (moduleStalk X x).map
      (((godementResolution X).obj M).extend ComplexShape.embeddingUpNat |>.d k l) =
    (moduleStalk X x).map (godementResolutionIntXIso X M k k rfl).hom ≫
      (moduleStalk X x).map (((godementResolution X).obj M).d k l) ≫
        (moduleStalk X x).map (godementResolutionIntXIso X M l l rfl).inv
  rw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat
    (i := k) (j := l) (i' := (k : ℤ)) (j' := (l : ℤ)) (by simp) (by simp),
    Functor.map_comp, Functor.map_comp]
  rfl


/-- The adjacent integer differential retains the actual quotient/unit differential. -/
theorem godementStalkIntD_cast_succ (X : Scheme.{u}) (x : X) (M : X.Modules) (k : ℕ) :
    (godementStalkIntD X x k (k + 1)).app M =
      (godementStalkIntTermIso X x k k rfl).hom.app M ≫
        (moduleStalk X x).map ((godementResolutionDifferential X k).app M) ≫
          (godementStalkIntTermIso X x (k + 1) (k + 1) (by omega)).inv.app M := by
  have h := godementStalkIntD_cast X x M k (k + 1)
  simp only [Int.natCast_add, Int.natCast_one] at h
  simpa only [godementResolution_d, godementResolutionDifferential,
    NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app] using h

/-- The strong contraction identity in the original integer degree zero. -/
theorem godementStalkIntContraction_zero (X : Scheme.{u}) (x : X) (M : X.Modules) :
    (godementStalkIntD X x 0 1).app M ≫ (godementStalkIntBack X x 1 0 (by omega)).app M +
      (godementStalkIntRetraction X x).app M ≫ (godementStalkIntGerm X x).app M = 𝟙 _ := by
  let e := godementStalkIntTermIso X x 0 0 (by simp)
  let e₁ := godementStalkIntTermIso X x 1 1 (by simp)
  have hd : (godementStalkIntD X x 0 1).app M = e.hom.app M ≫
      (moduleStalk X x).map ((godementResolutionDifferential X 0).app M) ≫ e₁.inv.app M :=
    godementStalkIntD_cast_succ X x M 0
  have hb : (godementStalkIntBack X x 1 0 (by omega)).app M = e₁.hom.app M ≫
      (godementStalkResolutionHomotopy X x 0).app M ≫ e.inv.app M :=
    congrArg (fun t => t.app M) (godementStalkIntBack_cast X x 0)
  apply (cancel_epi (e.inv.app M)).mp
  apply (cancel_mono (e.hom.app M)).mp
  rw [Preadditive.comp_add, Preadditive.add_comp, hd, hb]
  dsimp only [godementStalkIntRetraction, godementStalkIntGerm, NatTrans.comp_app]
  change (e.inv.app M ≫ (e.hom.app M ≫
        (moduleStalk X x).map ((godementResolutionDifferential X 0).app M) ≫ e₁.inv.app M) ≫
      (e₁.hom.app M ≫ (godementStalkResolutionHomotopy X x 0).app M ≫ e.inv.app M)) ≫
        e.hom.app M +
    (e.inv.app M ≫ (e.hom.app M ≫ (godementStalkRetraction X x).app M) ≫
      (moduleStalk X x).map (godementIntGerm X M)) ≫ e.hom.app M =
        (e.inv.app M ≫ 𝟙 _) ≫ e.hom.app M
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  change ((moduleStalk X x).map ((godementResolutionDifferential X 0).app M) ≫
      (godementStalkResolutionHomotopy X x 0).app M :
        (moduleStalk X x).obj ((godementFirstProduct X).obj M) ⟶
          (moduleStalk X x).obj ((godementFirstProduct X).obj M)) +
    ((godementStalkRetraction X x).app M ≫
      ((moduleStalk X x).map (godementIntGerm X M) ≫
        (moduleStalk X x).map (godementResolutionIntXIso X M 0 0 (by simp)).hom) :
        (moduleStalk X x).obj ((godementFirstProduct X).obj M) ⟶
          (moduleStalk X x).obj ((godementFirstProduct X).obj M)) = 𝟙 _
  rw [← Functor.map_comp, godementIntGerm_XIso]
  exact godementStalkResolutionHomotopy_zero X x M

/-- The strong contraction identity in every original positive integer degree. -/
theorem godementStalkIntContraction_succ (X : Scheme.{u}) (x : X) (M : X.Modules) (k : ℕ) :
    (godementStalkIntBack X x (k + 1) k (by omega)).app M ≫
        (godementStalkIntD X x k (k + 1)).app M +
      (godementStalkIntD X x (k + 1) (k + 1 + 1)).app M ≫
        (godementStalkIntBack X x (k + 1 + 1) (k + 1) (by omega)).app M = 𝟙 _ := by
  let e := godementStalkIntTermIso X x (k + 1) (k + 1) (by omega)
  apply (cancel_epi (e.inv.app M)).mp
  apply (cancel_mono (e.hom.app M)).mp
  rw [Preadditive.comp_add, Preadditive.add_comp]
  rw [godementStalkIntD_cast_succ]
  have hd := godementStalkIntD_cast_succ X x M (k + 1)
  simp only [Int.natCast_add, Int.natCast_one] at hd
  rw [hd]
  have hb₁ := congrArg (fun t => t.app M) (godementStalkIntBack_cast X x k)
  have hb₂ := congrArg (fun t => t.app M) (godementStalkIntBack_cast X x (k + 1))
  simp only [Int.natCast_add, Int.natCast_one] at hb₁ hb₂
  rw [hb₁, hb₂]
  dsimp only [e]
  simp only [NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  exact godementStalkResolutionHomotopy_succ X x M k

end AlgebraicGeometry.Scheme.Modules.Godement
