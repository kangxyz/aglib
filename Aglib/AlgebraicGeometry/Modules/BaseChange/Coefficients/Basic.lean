/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The joint native scheme and coefficient base-change family

The index consists of an actual scheme over `Spec R`, contravariantly, and an
actual coefficient algebra under `R`. Every fiber is the specified pullback.
Original scheme and coefficient arrows give one actual pullback lift, with
strict identity and composition laws on these fixed endpoints.

An open scheme arrow gives an actual cartesian open inclusion between native
fibers. At the identity algebra the original projection is an isomorphism,
rather than an equality with the original scheme. Quasi-compactness and
quasi-separatedness propagate from the scheme to all coefficient fibers.
No flatness or affineness assumption on the scheme or open is imposed.
-/

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/CoefficientBaseChange.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 169]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients

/-- Joint original scheme-over-base and coefficient-algebra indices. -/
abbrev Index (R : CommRingCat.{u}) := (Over (Spec R))ᵒᵖ × Under R

variable {R : CommRingCat.{u}}

/-- The actual native fiber of the indexed scheme over the indexed coefficient. -/
abbrev space (i : Index R) := pullback i.1.unop.hom (Spec.map i.2.hom)

/-- The original scheme-side projection of the fixed fiber. -/
abbrev projection (i : Index R) : space i ⟶ i.1.unop.left :=
  pullback.fst i.1.unop.hom (Spec.map i.2.hom)

/-- The original coefficient-side projection of the fixed fiber. -/
abbrev coefficientProjection (i : Index R) : space i ⟶ Spec i.2.right :=
  pullback.snd i.1.unop.hom (Spec.map i.2.hom)

/-- One original pullback lift combines the actual scheme and coefficient arrows. -/
def map {i k : Index R} (f : i ⟶ k) : space k ⟶ space i :=
  pullback.lift (projection k ≫ f.1.unop.left)
    (coefficientProjection k ≫ Spec.map f.2.right) (by
      rw [Category.assoc, Over.w, Category.assoc, ← Spec.map_comp, Under.w f.2]
      exact pullback.condition)

/-- The joint map retains its original scheme projection. -/
@[reassoc] theorem map_projection {i k : Index R} (f : i ⟶ k) :
    map f ≫ projection i = projection k ≫ f.1.unop.left :=
  pullback.lift_fst _ _ _

/-- The joint map retains its original coefficient projection. -/
@[reassoc] theorem map_coefficientProjection {i k : Index R} (f : i ⟶ k) :
    map f ≫ coefficientProjection i = coefficientProjection k ≫ Spec.map f.2.right :=
  pullback.lift_snd _ _ _

/-- The fixed native fiber gives a literal identity map at the identity index arrow. -/
theorem map_id (i : Index R) : map (𝟙 i) = 𝟙 (space i) := by
  apply pullback.hom_ext
  · rw [map_projection]
    change projection i ≫ 𝟙 _ = 𝟙 _ ≫ projection i
    simp only [Category.id_comp, Category.comp_id]
  · rw [map_coefficientProjection]
    change coefficientProjection i ≫ Spec.map (𝟙 i.2.right) = 𝟙 _ ≫ coefficientProjection i
    rw [Spec.map_id, Category.comp_id, Category.id_comp]

/-- Both original projection equations prove strict composition on the same fixed fibers. -/
theorem map_comp {i k l : Index R} (f : i ⟶ k) (g : k ⟶ l) :
    map (f ≫ g) = map g ≫ map f := by
  apply pullback.hom_ext
  · simp only [map_projection, Category.assoc, map_projection_assoc]
    rfl
  · simp only [map_coefficientProjection, Category.assoc, map_coefficientProjection_assoc,
      ]
    change coefficientProjection l ≫ Spec.map (f.2.right ≫ g.2.right) =
      coefficientProjection l ≫ Spec.map g.2.right ≫ Spec.map f.2.right
    rw [Spec.map_comp]

/-- The actual joint geometric family, before any category strictification. -/
def functor (R : CommRingCat.{u}) : Index R ⥤ AlgebraicGeometry.Scheme.{u}ᵒᵖ where
  obj i := op (space i)
  map f := (map f).op
  map_id i := congrArg Quiver.Hom.op (map_id i)
  map_comp f g := congrArg Quiver.Hom.op (map_comp f g)

/-- The coefficient row of one specified scheme over the unchanged base. -/
def row (P : Over (Spec R)) : Under R ⥤ Index R where
  obj a := (op P, a)
  map f := (𝟙 _, f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The native row restriction for an original scheme-over-base arrow. -/
def rowTransformation {P Q : Over (Spec R)} (f : P ⟶ Q) : row Q ⟶ row P where
  app a := (f.op, 𝟙 a)
  naturality _a _b g := by
    apply Prod.ext <;> simp [row]

/-- The native base-changed scheme arrow, using the same actual joint map. -/
def schemeMap {P Q : Over (Spec R)} (f : P ⟶ Q) (a : Under R) :
    space (op P, a) ⟶ space (op Q, a) :=
  map (f.op, 𝟙 a)

/-- The native scheme arrow retains its original scheme map. -/
@[reassoc] theorem schemeMap_projection {P Q : Over (Spec R)} (f : P ⟶ Q) (a : Under R) :
    schemeMap f a ≫ projection (op Q, a) = projection (op P, a) ≫ f.left := by
  exact pullback.lift_fst _ _ _

/-- The native scheme arrow keeps the coefficient projection unchanged. -/
@[reassoc] theorem schemeMap_coefficientProjection {P Q : Over (Spec R)}
    (f : P ⟶ Q) (a : Under R) :
    schemeMap f a ≫ coefficientProjection (op Q, a) = coefficientProjection (op P, a) := by
  change pullback.lift _ _ _ ≫ pullback.snd Q.hom (Spec.map a.hom) = _
  rw [pullback.lift_snd]
  change coefficientProjection (op P, a) ≫ Spec.map (𝟙 a.right) = _
  rw [Spec.map_id, Category.comp_id]

/-- The original native scheme map is an actual base change of the original scheme arrow. -/
theorem schemeMap_isPullback {P Q : Over (Spec R)} (f : P ⟶ Q) (a : Under R) :
    IsPullback (schemeMap f a) (projection (op P, a)) (projection (op Q, a)) f.left := by
  apply IsPullback.of_right (h₁₂ := coefficientProjection (op Q, a)) (h₂₂ := Q.hom)
  · simpa only [schemeMap_coefficientProjection, Over.w] using
      (IsPullback.of_hasPullback P.hom (Spec.map a.hom)).flip
  · exact schemeMap_projection f a
  · exact (IsPullback.of_hasPullback Q.hom (Spec.map a.hom)).flip

/-- An original open scheme arrow gives an actual open inclusion of its native fibers. -/
instance schemeMap_isOpenImmersion {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (a : Under R) : IsOpenImmersion (schemeMap f a) :=
  MorphismProperty.of_isPullback (schemeMap_isPullback f a).flip inferInstance

/-- At the identity algebra, the original native projection is an actual isomorphism. -/
def identityProjectionIso (P : Over (Spec R)) :
    space (op P, Under.mk (𝟙 R)) ≅ P.left := by
  have : IsIso (Spec.map (𝟙 R)) := by rw [Spec.map_id]; infer_instance
  have : IsIso (projection (op P, Under.mk (𝟙 R))) := by
    change IsIso (pullback.fst P.hom (Spec.map (𝟙 R)))
    infer_instance
  exact asIso (projection (op P, Under.mk (𝟙 R)))

/-- The identity projection keeps the original scheme-arrow square. -/
theorem identityProjectionIso_schemeMap {P Q : Over (Spec R)} (f : P ⟶ Q) :
    schemeMap f (Under.mk (𝟙 R)) ≫ (identityProjectionIso Q).hom =
      (identityProjectionIso P).hom ≫ f.left :=
  schemeMap_projection f (Under.mk (𝟙 R))

/-- Compactness of the original scheme propagates to every actual coefficient fiber. -/
theorem compactSpace_space (i : Index R) [CompactSpace i.1.unop.left] :
    CompactSpace (space i) := by
  let : QuasiCompact i.1.unop.hom := quasiCompact_of_compactSpace i.1.unop.hom
  exact inferInstanceAs
    (CompactSpace ((pullback i.1.unop.hom (Spec.map i.2.hom)) : AlgebraicGeometry.Scheme.{u}))

/-- Quasi-separatedness propagates along arbitrary actual coefficient base changes. -/
theorem quasiSeparatedSpace_space (i : Index R) [QuasiSeparatedSpace i.1.unop.left] :
    QuasiSeparatedSpace (space i) := by
  let : QuasiSeparated i.1.unop.hom := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (coefficientProjection i)

end AlgebraicGeometry.Scheme.BaseChange.Coefficients
