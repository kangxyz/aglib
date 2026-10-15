/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Stalk.IntContraction
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Exactness
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementStalkTotalMatrix.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 252]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Matrices on the actual module stalk of an original Godement total -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The original lower-bounded complex on the chosen actual module stalk. -/
abbrev godementSourceStalk (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules) :=
  (moduleStalk X x).mapHomologicalComplex (.up ℤ) |>.obj K.obj

/-- The actual Godement total on the chosen original module stalk. -/
abbrev godementTotalStalk (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules) :=
  (moduleStalk X x).mapHomologicalComplex (.up ℤ) |>.obj ((godementTotal X).obj K.obj)

/-- The original signed total's actual diagonal inclusion after taking the module stalk. -/
def godementStalkTotalIn (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (p q n : ℤ) (h : p + q = n) :
    ((godementStalkIntTerm X x q).obj (K.obj.X p)) ⟶ (godementTotalStalk X x K).X n :=
  (moduleStalk X x).map (((godementBicomplex X).obj K.obj).ιTotal (.up ℤ) p q n h)

/-- The actual diagonal of the total, transported by the original left-adjoint stalk. -/
abbrev godementStalkTotalDiagram (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n : ℤ) := (godementDiagonalFunctor X n).obj K.obj ⋙ moduleStalk X x

/-- The actual preserved coproduct cocone, whose point is the original total stalk. -/
def godementStalkTotalCocone (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n : ℤ) : Cocone (godementStalkTotalDiagram X x K n) :=
  (moduleStalk X x).mapCocone (colimit.cocone ((godementDiagonalFunctor X n).obj K.obj))

/-- The actual stalk preserves the diagonal coproduct by its original left adjunction. -/
def godementStalkTotalIsColimit (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n : ℤ) : IsColimit (godementStalkTotalCocone X x K n) :=
  isColimitOfPreserves (moduleStalk X x)
    (colimit.isColimit ((godementDiagonalFunctor X n).obj K.obj))

/-- A matrix constructor on the actual total stalk, via its actual preserved coproduct. -/
def godementStalkTotalDesc (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n : ℤ) {Z : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : ∀ (p q : ℤ) (_ : p + q = n), (godementStalkIntTerm X x q).obj (K.obj.X p) ⟶ Z) :
    (godementTotalStalk X x K).X n ⟶ Z :=
  (godementStalkTotalIsColimit X x K n).desc
    { pt := Z
      ι := Discrete.natTrans (fun i => f i.as.val.1 i.as.val.2 i.as.property) }

@[reassoc (attr := simp)]
theorem godementStalkTotalIn_desc (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n : ℤ) {Z : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : ∀ (p q : ℤ) (_ : p + q = n), (godementStalkIntTerm X x q).obj (K.obj.X p) ⟶ Z)
    (p q : ℤ) (h : p + q = n) :
    godementStalkTotalIn X x K p q n h ≫ godementStalkTotalDesc X x K n f = f p q h := by
  exact (godementStalkTotalIsColimit X x K n).fac _ (Discrete.mk ⟨(p, q), h⟩)

/-- Matrices on all original diagonal summands determine a map on the actual total stalk. -/
theorem godementStalkTotal_hom_ext (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n : ℤ) {Z : ModuleCat.{u} (X.presheaf.stalk x)}
    {f g : (godementTotalStalk X x K).X n ⟶ Z}
    (h : ∀ p q (hpq : p + q = n),
      godementStalkTotalIn X x K p q n hpq ≫ f = godementStalkTotalIn X x K p q n hpq ≫ g) :
    f = g := by
  apply (godementStalkTotalIsColimit X x K n).hom_ext
  intro i
  exact h i.as.val.1 i.as.val.2 i.as.property


/-- The horizontal matrix entry is the actual resolved original differential. -/
def godementStalkHorizontal (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (p q : ℤ) : (godementStalkIntTerm X x q).obj (K.obj.X p) ⟶
      (godementStalkIntTerm X x q).obj (K.obj.X (p + 1)) :=
  (godementStalkIntTerm X x q).map (K.obj.d p (p + 1))

/-- The native signed total differential retains its two original matrix entries on the stalk. -/
@[reassoc]
theorem godementStalkTotalIn_d (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (p q n : ℤ) (hpq : p + q = n) :
    godementStalkTotalIn X x K p q n hpq ≫ (godementTotalStalk X x K).d n (n + 1) =
      godementStalkHorizontal X x K p q ≫
        godementStalkTotalIn X x K (p + 1) q (n + 1) (by omega) +
      (ComplexShape.up ℤ).ε p • ((godementStalkIntD X x q (q + 1)).app (K.obj.X p) ≫
        godementStalkTotalIn X x K p (q + 1) (n + 1) (by omega)) := by
  change (moduleStalk X x).map _ ≫ (moduleStalk X x).map _ = _
  rw [← Functor.map_comp]
  change (moduleStalk X x).map
    (((godementBicomplex X).obj K.obj).ιTotal (.up ℤ) p q n hpq ≫
      (((godementBicomplex X).obj K.obj).total (.up ℤ)).d n (n + 1)) = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  rw [HomologicalComplex₂.d₁_eq _ (.up ℤ)
    (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q (n + 1)
      (by change p + 1 + q = n + 1; omega),
    HomologicalComplex₂.d₂_eq _ (.up ℤ) p
      (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (n + 1)
      (by change p + (q + 1) = n + 1; omega)]
  change (moduleStalk X x).map
    ((1 : ℤˣ) • (_ ≫ _) + (ComplexShape.up ℤ).ε p • (_ ≫ _)) = _
  rw [one_smul, Functor.map_add, Functor.map_units_smul, Functor.map_comp, Functor.map_comp]
  rfl

/-- The backwards and horizontal matrix entries commute by the checked natural contraction. -/
@[reassoc]
theorem godementStalkHorizontal_back (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (p q r : ℤ) (hqr : r + 1 = q) :
    godementStalkHorizontal X x K p q ≫ (godementStalkIntBack X x q r hqr).app (K.obj.X (p + 1)) =
      (godementStalkIntBack X x q r hqr).app (K.obj.X p) ≫
        godementStalkHorizontal X x K p r :=
  (godementStalkIntBack X x q r hqr).naturality (K.obj.d p (p + 1))


/-- The negative original resolution terms are still zero on the module stalk. -/
theorem godementStalkIntTerm_isZero_negative (X : Scheme.{u}) (x : X) (M : X.Modules)
    (q : ℤ) (hq : q < 0) : IsZero ((godementStalkIntTerm X x q).obj M) :=
  (moduleStalk X x).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE ((godementResolutionInt X).obj M) 0 q hq)

/-- The actual total matrix projecting the zero resolution row back to the original complex. -/
def godementStalkTotalProjection (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n : ℤ) : (godementTotalStalk X x K).X n ⟶ (godementSourceStalk X x K).X n :=
  godementStalkTotalDesc X x K n (fun p q hpq => if hq : q = 0 then
    eqToHom (by
      subst hq
      have hp : p = n := by omega
      rw [hp]) ≫
      (godementStalkIntRetraction X x).app (K.obj.X n)
    else 0)

/-- The actual signed vertical-backstep matrix on the total stalk. -/
def godementStalkTotalBack (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n m : ℤ) (hmn : m + 1 = n) :
    (godementTotalStalk X x K).X n ⟶ (godementTotalStalk X x K).X m :=
  godementStalkTotalDesc X x K n (fun p q hpq =>
    (ComplexShape.up ℤ).ε p • ((godementStalkIntBack X x q (q - 1) (by omega)).app (K.obj.X p) ≫
      godementStalkTotalIn X x K p (q - 1) m (by omega)))

/-- The original natural total augmentation on the original module stalk. -/
abbrev godementStalkTotalUnit (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules) :
    godementSourceStalk X x K ⟶ godementTotalStalk X x K :=
  ((moduleStalk X x).mapHomologicalComplex (.up ℤ)).map ((godementTotalUnit X).app K.obj)

/-- The total augmentation component under the actual stalk functor, in complex-map normal form. -/
@[simp]
theorem moduleStalk_map_godementTotalUnit_f (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (moduleStalk X x).map (((godementTotalUnit X).app K.obj).f n) =
      (godementStalkIntGerm X x).app (K.obj.X n) ≫
        godementStalkTotalIn X x K n 0 n (by omega) := by
  change (moduleStalk X x).map (godementIntGerm X (K.obj.X n) ≫ _) = _
  rw [Functor.map_comp]
  rfl

/-- The original stalk-unit component formula, also usable directly by rewriting. -/
theorem godementStalkTotalUnit_f (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (n : ℤ) : (godementStalkTotalUnit X x K).f n =
      (godementStalkIntGerm X x).app (K.obj.X n) ≫
        godementStalkTotalIn X x K n 0 n (by omega) :=
  moduleStalk_map_godementTotalUnit_f X x K n

/-- The projection really retracts the original total augmentation degree by degree. -/
theorem godementStalkTotalUnit_projection (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (godementStalkTotalUnit X x K).f n ≫ godementStalkTotalProjection X x K n = 𝟙 _ := by
  dsimp only [godementStalkTotalProjection]
  rw [godementStalkTotalUnit_f, Category.assoc, godementStalkTotalIn_desc]
  simp only [eqToHom_refl, Category.id_comp]
  exact godementStalkIntGerm_retraction X x (K.obj.X n)


@[reassoc (attr := simp)]
theorem godementStalkTotalIn_projection_zero (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) (h : n + 0 = n) :
    godementStalkTotalIn X x K n 0 n h ≫ godementStalkTotalProjection X x K n =
      (godementStalkIntRetraction X x).app (K.obj.X n) := by
  dsimp only [godementStalkTotalProjection]
  rw [godementStalkTotalIn_desc]
  simp

@[reassoc (attr := simp)]
theorem godementStalkTotalIn_projection_ne (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (p q n : ℤ) (h : p + q = n) (hq : q ≠ 0) :
    godementStalkTotalIn X x K p q n h ≫ godementStalkTotalProjection X x K n = 0 := by
  dsimp only [godementStalkTotalProjection]
  rw [godementStalkTotalIn_desc, dite_eq_right hq]

@[reassoc (attr := simp)]
theorem godementStalkTotalIn_back (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (p q n m : ℤ) (h : p + q = n) (hmn : m + 1 = n) :
    godementStalkTotalIn X x K p q n h ≫ godementStalkTotalBack X x K n m hmn =
      (ComplexShape.up ℤ).ε p • ((godementStalkIntBack X x q (q - 1) (by omega)).app (K.obj.X p) ≫
        godementStalkTotalIn X x K p (q - 1) m (by omega)) := by
  dsimp only [godementStalkTotalBack]
  rw [godementStalkTotalIn_desc]

/-- The actual zero-row projection is a chain map, by the original natural retraction. -/
theorem godementStalkTotalProjection_comm (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    godementStalkTotalProjection X x K n ≫ (godementSourceStalk X x K).d n (n + 1) =
      (godementTotalStalk X x K).d n (n + 1) ≫ godementStalkTotalProjection X x K (n + 1) := by
  apply godementStalkTotal_hom_ext
  intro p q hpq
  by_cases hneg : q < 0
  · exact (godementStalkIntTerm_isZero_negative X x (K.obj.X p) q hneg).eq_of_src _ _
  by_cases hq : q = 0
  · subst hq
    have hp : p = n := by omega
    subst p
    rw [← Category.assoc, godementStalkTotalIn_projection_zero]
    rw [← Category.assoc, godementStalkTotalIn_d, Preadditive.add_comp,
      Linear.units_smul_comp, Category.assoc, godementStalkTotalIn_projection_zero,
      Category.assoc, godementStalkTotalIn_projection_ne _ _ _ _ _ _ _ (by norm_num)]
    rw [comp_zero, smul_zero, add_zero]
    exact ((godementStalkIntRetraction X x).naturality (K.obj.d n (n + 1))).symm
  · have hq' : q + 1 ≠ 0 := by omega
    rw [← Category.assoc, godementStalkTotalIn_projection_ne _ _ _ _ _ _ _ hq, zero_comp]
    rw [← Category.assoc, godementStalkTotalIn_d, Preadditive.add_comp,
      Linear.units_smul_comp, Category.assoc,
      godementStalkTotalIn_projection_ne _ _ _ _ _ _ _ hq,
      Category.assoc, godementStalkTotalIn_projection_ne _ _ _ _ _ _ _ hq']
    rw [comp_zero, comp_zero, smul_zero, add_zero]

/-- The original total projection with its actual chain-map equations. -/
def godementStalkTotalRetraction (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules) :
    godementTotalStalk X x K ⟶ godementSourceStalk X x K where
  f n := godementStalkTotalProjection X x K n
  comm' n m h := by
    obtain rfl : n + 1 = m := h
    exact godementStalkTotalProjection_comm X x K n

@[simp]
theorem godementStalkTotalUnit_retraction (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) :
    godementStalkTotalUnit X x K ≫ godementStalkTotalRetraction X x K = 𝟙 _ := by
  ext1 n
  exact godementStalkTotalUnit_projection X x K n


/-- The native differential matrix with its original adjacent target degree explicit. -/
@[reassoc]
theorem godementStalkTotalIn_d_to (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (p q n m : ℤ) (hpq : p + q = n) (hnm : n + 1 = m) :
    godementStalkTotalIn X x K p q n hpq ≫ (godementTotalStalk X x K).d n m =
      godementStalkHorizontal X x K p q ≫
        godementStalkTotalIn X x K (p + 1) q m (by omega) +
      (ComplexShape.up ℤ).ε p • ((godementStalkIntD X x q (q + 1)).app (K.obj.X p) ≫
        godementStalkTotalIn X x K p (q + 1) m (by omega)) := by
  subst m
  exact godementStalkTotalIn_d X x K p q n hpq

end AlgebraicGeometry.Scheme.Modules.Godement
