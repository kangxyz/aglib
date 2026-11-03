/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductBaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange.Higher
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalkRepresentatives
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricFibreTransfer

/-! # The original higher exchange over a common geometric point

An explicit original neighborhood-germ formula implies the common-point
exchange equation. The coefficient rectangle and germ representatives are
the actual passed suppliers. This conditional module has no dependency on
the proof of the neighborhood formula or on a chosen relation between marked models.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u w w' s s' e dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

open Continuity Finite.GeometricNeighborhood

private theorem addHom_square_iff_prepost
    {A : Type*} {B : Type*} {C : Type*} {D : Type*} {E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup E]
    (pre : A →+ E) (post : E →+ B) (m : A →+ B) (hm : m = post.comp pre)
    (b : A →+ C) (b' : B →+ D) (d : C →+ D) :
    b'.comp m = d.comp b ↔ ∀ z, b' (post (pre z)) = d (b z) := by
  subst m
  constructor
  · intro h z
    exact DFunLike.congr_fun h z
  · intro h
    exact AddMonoidHom.ext h

/-- Evaluate a whole equation of the actual raw group maps before any native
cohomology data enters the composition-evaluation proof. -/
private theorem rawGroupSquare_apply {A B C D : Type e}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    (r : AddCommGrpCat.of A ⟶ AddCommGrpCat.of B)
    (v : AddCommGrpCat.of B ⟶ AddCommGrpCat.of D)
    (u : AddCommGrpCat.of A ⟶ AddCommGrpCat.of C)
    (s : AddCommGrpCat.of C ⟶ AddCommGrpCat.of D)
    (h : r ≫ v = u ≫ s) (x : A) : @Eq D (v (r x)) (s (u x)) := by
  have hs := ConcreteCategory.congr_hom (C := AddCommGrpCat.{e}) h x
  simpa only [CategoryTheory.comp_apply] using hs

/-- One complete indexed-germ comparison, with its original maps and rectangle.
The two neighborhood indices remain independent: the target law is required on
all target neighborhoods, not only on those pulled back from the source. -/
structure IndexedGermComparisonData
    {I J : Type*} (P : I → Type*) (Q : J → Type*)
    (V : I → Type e) (W : J → Type e)
    (A B : Type*) (C D : Type e)
    [∀ i, AddCommGroup (V i)] [∀ j, AddCommGroup (W j)]
    [AddCommGroup C] [AddCommGroup D] where
  /-- The source germ represented by a point and a neighborhood value. -/
  sourceGerm : ∀ i, P i → V i → A
  /-- The target germ represented by a point and a neighborhood value. -/
  targetGerm : ∀ j, Q j → W j → B
  /-- The map from source neighborhood indices to target indices. -/
  indexMap : I → J
  /-- The map on points associated with each source index. -/
  pointMap : ∀ i, P i → Q (indexMap i)
  /-- The map from source germs to target germs. -/
  unitMap : A → B
  /-- The map between the source and target comparison groups. -/
  directMap : AddCommGrpCat.of C ⟶ AddCommGrpCat.of D
  /-- The map on values at each source neighborhood. -/
  neighborhoodMap : ∀ i, AddCommGrpCat.of (V i) ⟶ AddCommGrpCat.of (W (indexMap i))
  /-- The source comparison map for a point in a neighborhood. -/
  sourceMap : ∀ i, P i → (AddCommGrpCat.of (V i) ⟶ AddCommGrpCat.of C)
  /-- The target comparison map for a point in a neighborhood. -/
  targetMap : ∀ j, Q j → (AddCommGrpCat.of (W j) ⟶ AddCommGrpCat.of D)
  representatives : ∀ z : A, ∃ i p y, sourceGerm i p y = z
  rectangle : ∀ i p, neighborhoodMap i ≫ targetMap (indexMap i) (pointMap i p) =
    sourceMap i p ≫ directMap

namespace IndexedGermComparisonData

variable {I J : Type*} {P : I → Type*} {Q : J → Type*}
  {V : I → Type e} {W : J → Type e} {A B : Type*} {C D : Type e}
  [∀ i, AddCommGroup (V i)] [∀ j, AddCommGroup (W j)]
  [AddCommGroup C] [AddCommGroup D]
  (data : IndexedGermComparisonData P Q V W A B C D)

/-- Compatibility of the original unit with the complete germ construction. -/
def UnitLaw : Prop := ∀ i p y,
  data.unitMap (data.sourceGerm i p y) =
    data.targetGerm (data.indexMap i) (data.pointMap i p) (data.neighborhoodMap i y)

/-- The comparison map evaluates to the original source restriction. -/
def SourceLaw (b : A → C) : Prop :=
  ∀ i p y, b (data.sourceGerm i p y) = data.sourceMap i p y

/-- The target comparison law retains every original target neighborhood. -/
def TargetLaw (b' : B → D) : Prop :=
  ∀ j p y, b' (data.targetGerm j p y) = data.targetMap j p y

/-- The literal pointwise square of the maps in this same construction. -/
def Square (b : A → C) (b' : B → D) : Prop :=
  ∀ z, b' (data.unitMap z) = data.directMap (b z)

/-- The complete determining germ construction carries its original square law. -/
theorem square_of_laws (hunit : data.UnitLaw) (b : A → C) (b' : B → D)
    (hsource : data.SourceLaw b) (htarget : data.TargetLaw b') : data.Square b b' := by
  intro z
  obtain ⟨i, p, y, rfl⟩ := data.representatives z
  exact (congrArg b' (hunit i p y)).trans
    ((htarget (data.indexMap i) (data.pointMap i p) (data.neighborhoodMap i y)).trans
      ((rawGroupSquare_apply _ _ _ _ (data.rectangle i p) y).trans
        (congrArg data.directMap (hsource i p y)).symm))

end IndexedGermComparisonData

namespace IndexedGermComparisonData

variable {I J : Type*} {P : I → Type*} {Q : J → Type*}
  {V : I → Type e} {W : J → Type e} {A B : Type*} {C D : Type e}
  [∀ i, AddCommGroup (V i)] [∀ j, AddCommGroup (W j)]
  [AddCommGroup C] [AddCommGroup D]
  (γ : ∀ i, P i → V i → A) (γ' : ∀ j, Q j → W j → B)
  (k : I → J) (kp : ∀ i, P i → Q (k i)) (unit : A → B)
  (d : AddCommGrpCat.of C ⟶ AddCommGrpCat.of D)
  (r : ∀ i, AddCommGrpCat.of (V i) ⟶ AddCommGrpCat.of (W (k i)))
  (u : ∀ i, P i → (AddCommGrpCat.of (V i) ⟶ AddCommGrpCat.of C))
  (v : ∀ j, Q j → (AddCommGrpCat.of (W j) ⟶ AddCommGrpCat.of D))
  (hγ : ∀ z : A, ∃ i p y, γ i p y = z)
  (hRect : ∀ i p, r i ≫ v (k i) (kp i p) = u i p ≫ d)

/-- Assemble the same indexed comparison from its actual maps and rectangle,
with all group objects and maps variable. -/
def ofMaps : IndexedGermComparisonData P Q V W A B C D where
  sourceGerm := γ
  targetGerm := γ'
  indexMap := k
  pointMap := kp
  unitMap := unit
  directMap := d
  neighborhoodMap := r
  sourceMap := u
  targetMap := v
  representatives := hγ
  rectangle := hRect

include hγ hRect in
/-- The complete original-map constructor exposes its literal comparison law
before concrete cohomology objects or geometric maps are substituted. -/
theorem ofMaps_square
    (hunit : ∀ i p y, unit (γ i p y) = γ' (k i) (kp i p) (r i y))
    (b : A → C) (b' : B → D)
    (hb : ∀ i p y, b (γ i p y) = u i p y)
    (hb' : ∀ j p y, b' (γ' j p y) = v j p y) :
    ∀ z, b' (unit z) = d (b z) :=
  (ofMaps γ γ' k kp unit d r u v hγ hRect).square_of_laws hunit b b' hb hb'

end IndexedGermComparisonData

/-- Construct the entire indexed comparison over variable relative schemes.
The cohomology maps and their whole rectangle are formed together, before any
concrete neighborhood fibre-product family is substituted. -/
def indexedGermComparisonDataOfSchemeSquares
    {X₀ X₁ : Scheme.{u}} {I J : Type*} (P : I → Type*) (Q : J → Type*)
    (k : I → J) (kp : ∀ i, P i → Q (k i))
    (B : I → Scheme.{u}) (B' : J → Scheme.{u})
    (b : ∀ i, B i ⟶ X₀) (b' : ∀ j, B' j ⟶ X₁)
    (A A' : Scheme.{u}) (a : A ⟶ X₀) (a' : A' ⟶ X₁)
    [hB : ∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (B i))]
    [hB' : ∀ j, HasExt.{e} (AbelianSheaf.{u, u + 1} (B' j))]
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [hA' : HasExt.{e} (AbelianSheaf.{u, u + 1} A')]
    (g₀ : X₁ ⟶ X₀) (r : ∀ i, B' (k i) ⟶ B i)
    (σ : A' ⟶ A)
    (hR : ∀ i, b' (k i) ≫ g₀ = r i ≫ b i)
    (hS : a' ≫ g₀ = σ ≫ a)
    (v : ∀ i, P i → (A ⟶ B i)) (v' : ∀ j, Q j → (A' ⟶ B' j))
    (hv : ∀ i p, v i p ≫ b i = a) (hv' : ∀ j p, v' j p ≫ b' j = a')
    (hRect : ∀ i p, v' (k i) (kp i p) ≫ r i = σ ≫ v i p)
    (F₀ : AbelianSheaf.{u, u + 1} X₀) (q₀ : ℕ) {Z Z' : Type*}
    (γ : ∀ i, P i → Sheaf.H.{e} ((inverseImage (b i)).obj F₀) q₀ → Z)
    (γ' : ∀ j, Q j → Sheaf.H.{e} ((inverseImage (b' j)).obj
      ((inverseImage g₀).obj F₀)) q₀ → Z')
    (unit : Z → Z') (hγ : ∀ z : Z, ∃ i p y, γ i p y = z) :
    IndexedGermComparisonData P Q
      (fun i => Sheaf.H.{e} ((inverseImage (b i)).obj F₀) q₀)
      (fun j => Sheaf.H.{e} ((inverseImage (b' j)).obj ((inverseImage g₀).obj F₀)) q₀)
      Z Z' (Sheaf.H.{e} ((inverseImage a).obj F₀) q₀)
      (Sheaf.H.{e} ((inverseImage a').obj ((inverseImage g₀).obj F₀)) q₀) :=
  IndexedGermComparisonData.ofMaps γ γ' k kp unit
    (cohomologySquareTransfer a a' g₀ σ hS F₀ q₀)
    (fun i => cohomologySquareTransfer (b i) (b' (k i)) g₀ (r i) (hR i) F₀ q₀)
    (fun i p => cohomologyTriangleTransfer a (b i) (v i p) (hv i p) F₀ q₀)
    (fun j p =>
      cohomologyTriangleTransfer a' (b' j) (v' j p) (hv' j p) ((inverseImage g₀).obj F₀) q₀)
    hγ (fun i p =>
      @cohomologySquareTriangleEquation_of_rectangle.{u, e}
        X₀ X₁ A (B i) A' (B' (k i)) hA (hB i) hA' (hB' (k i))
        (b i) (b' (k i)) a a' (v i p) (v' (k i) (kp i p))
        (r i) σ g₀ (hv i p) (hv' (k i) (kp i p))
        (hR i) hS (hRect i p) F₀ q₀)

/-- The complete source triangle law of the existing construction has no
dependence on its unit map or the opposite comparison. -/
theorem indexedGermComparisonDataOfSchemeSquares_sourceLaw_iff
    {X₀ X₁ : Scheme.{u}} {I J : Type*} (P : I → Type*) (Q : J → Type*)
    (k : I → J) (kp : ∀ i, P i → Q (k i))
    (B : I → Scheme.{u}) (B' : J → Scheme.{u})
    (b : ∀ i, B i ⟶ X₀) (b' : ∀ j, B' j ⟶ X₁)
    (A A' : Scheme.{u}) (a : A ⟶ X₀) (a' : A' ⟶ X₁)
    [hB : ∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (B i))]
    [hB' : ∀ j, HasExt.{e} (AbelianSheaf.{u, u + 1} (B' j))]
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [hA' : HasExt.{e} (AbelianSheaf.{u, u + 1} A')]
    (g₀ : X₁ ⟶ X₀) (r : ∀ i, B' (k i) ⟶ B i)
    (σ : A' ⟶ A)
    (hR : ∀ i, b' (k i) ≫ g₀ = r i ≫ b i)
    (hS : a' ≫ g₀ = σ ≫ a)
    (v : ∀ i, P i → (A ⟶ B i)) (v' : ∀ j, Q j → (A' ⟶ B' j))
    (hv : ∀ i p, v i p ≫ b i = a) (hv' : ∀ j p, v' j p ≫ b' j = a')
    (hRect : ∀ i p, v' (k i) (kp i p) ≫ r i = σ ≫ v i p)
    (F₀ : AbelianSheaf.{u, u + 1} X₀) (q₀ : ℕ) {Z Z' : Type*}
    (γ : ∀ i, P i → Sheaf.H.{e} ((inverseImage (b i)).obj F₀) q₀ → Z)
    (γ' : ∀ j, Q j → Sheaf.H.{e} ((inverseImage (b' j)).obj
      ((inverseImage g₀).obj F₀)) q₀ → Z')
    (unit : Z → Z') (hγ : ∀ z : Z, ∃ i p y, γ i p y = z)
    (c : Z → Sheaf.H.{e} ((inverseImage a).obj F₀) q₀) :
    (indexedGermComparisonDataOfSchemeSquares P Q k kp B B' b b' A A' a a'
      g₀ r σ hR hS v v' hv hv' hRect F₀ q₀ γ γ' unit hγ).SourceLaw c ↔
      ∀ i p y, c (γ i p y) =
        cohomologyTriangleTransfer a (b i) (v i p) (hv i p) F₀ q₀ y := Iff.rfl

/-- The complete target triangle law of the existing construction has no
dependence on its unit map or the opposite comparison. -/
theorem indexedGermComparisonDataOfSchemeSquares_targetLaw_iff
    {X₀ X₁ : Scheme.{u}} {I J : Type*} (P : I → Type*) (Q : J → Type*)
    (k : I → J) (kp : ∀ i, P i → Q (k i))
    (B : I → Scheme.{u}) (B' : J → Scheme.{u})
    (b : ∀ i, B i ⟶ X₀) (b' : ∀ j, B' j ⟶ X₁)
    (A A' : Scheme.{u}) (a : A ⟶ X₀) (a' : A' ⟶ X₁)
    [hB : ∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (B i))]
    [hB' : ∀ j, HasExt.{e} (AbelianSheaf.{u, u + 1} (B' j))]
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [hA' : HasExt.{e} (AbelianSheaf.{u, u + 1} A')]
    (g₀ : X₁ ⟶ X₀) (r : ∀ i, B' (k i) ⟶ B i)
    (σ : A' ⟶ A)
    (hR : ∀ i, b' (k i) ≫ g₀ = r i ≫ b i)
    (hS : a' ≫ g₀ = σ ≫ a)
    (v : ∀ i, P i → (A ⟶ B i)) (v' : ∀ j, Q j → (A' ⟶ B' j))
    (hv : ∀ i p, v i p ≫ b i = a) (hv' : ∀ j p, v' j p ≫ b' j = a')
    (hRect : ∀ i p, v' (k i) (kp i p) ≫ r i = σ ≫ v i p)
    (F₀ : AbelianSheaf.{u, u + 1} X₀) (q₀ : ℕ) {Z Z' : Type*}
    (γ : ∀ i, P i → Sheaf.H.{e} ((inverseImage (b i)).obj F₀) q₀ → Z)
    (γ' : ∀ j, Q j → Sheaf.H.{e} ((inverseImage (b' j)).obj
      ((inverseImage g₀).obj F₀)) q₀ → Z')
    (unit : Z → Z') (hγ : ∀ z : Z, ∃ i p y, γ i p y = z)
    (c : Z' → Sheaf.H.{e} ((inverseImage a').obj ((inverseImage g₀).obj F₀)) q₀) :
    (indexedGermComparisonDataOfSchemeSquares P Q k kp B B' b b' A A' a a'
      g₀ r σ hR hS v v' hv hv' hRect F₀ q₀ γ γ' unit hγ).TargetLaw c ↔
      ∀ j p y, c (γ' j p y) =
        cohomologyTriangleTransfer a' (b' j) (v' j p) (hv' j p)
          ((inverseImage g₀).obj F₀) q₀ y := Iff.rfl

/-- The original relative-scheme interface, specializing the same literal-scheme
construction without making a second comparison model. -/
def indexedGermComparisonDataOfRelativeSquares
    {X₀ X₁ : Scheme.{u}} {I J : Type*} (P : I → Type*) (Q : J → Type*)
    (k : I → J) (kp : ∀ i, P i → Q (k i))
    (B : I → Over X₀) (B' : J → Over X₁) (A : Over X₀) (A' : Over X₁)
    [hB : ∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (B i).left)]
    [hB' : ∀ j, HasExt.{e} (AbelianSheaf.{u, u + 1} (B' j).left)]
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)]
    [hA' : HasExt.{e} (AbelianSheaf.{u, u + 1} A'.left)]
    (g₀ : X₁ ⟶ X₀) (r : ∀ i, (B' (k i)).left ⟶ (B i).left)
    (σ : A'.left ⟶ A.left)
    (hR : ∀ i, (B' (k i)).hom ≫ g₀ = r i ≫ (B i).hom)
    (hS : A'.hom ≫ g₀ = σ ≫ A.hom)
    (v : ∀ i, P i → (A ⟶ B i)) (v' : ∀ j, Q j → (A' ⟶ B' j))
    (hRect : ∀ i p, (v' (k i) (kp i p)).left ≫ r i = σ ≫ (v i p).left)
    (F₀ : AbelianSheaf.{u, u + 1} X₀) (q₀ : ℕ) {Z Z' : Type*}
    (γ : ∀ i, P i → Sheaf.H.{e} ((inverseImage (B i).hom).obj F₀) q₀ → Z)
    (γ' : ∀ j, Q j → Sheaf.H.{e} ((inverseImage (B' j).hom).obj
      ((inverseImage g₀).obj F₀)) q₀ → Z')
    (unit : Z → Z') (hγ : ∀ z : Z, ∃ i p y, γ i p y = z) :
    IndexedGermComparisonData P Q
      (fun i => Sheaf.H.{e} ((inverseImage (B i).hom).obj F₀) q₀)
      (fun j => Sheaf.H.{e} ((inverseImage (B' j).hom).obj ((inverseImage g₀).obj F₀)) q₀)
      Z Z' (Sheaf.H.{e} ((inverseImage A.hom).obj F₀) q₀)
      (Sheaf.H.{e} ((inverseImage A'.hom).obj ((inverseImage g₀).obj F₀)) q₀) :=
  indexedGermComparisonDataOfSchemeSquares P Q k kp
    (fun i => (B i).left) (fun j => (B' j).left)
    (fun i => (B i).hom) (fun j => (B' j).hom) A.left A'.left A.hom A'.hom
    (hB := hB) (hB' := hB') (hA := hA) (hA' := hA')
    g₀ r σ hR hS (fun i p => (v i p).left) (fun j p => (v' j p).left)
    (fun i p => Over.w (v i p)) (fun j p => Over.w (v' j p))
    hRect F₀ q₀ γ γ' unit hγ

/-- The complete constructed family gives the literal additive-map square
before the concrete stalks and neighborhood schemes are substituted. -/
theorem indexedGermComparisonDataOfRelativeSquares_addHomSquare
    {X₀ X₁ : Scheme.{u}} {I J : Type*} (P : I → Type*) (Q : J → Type*)
    (k : I → J) (kp : ∀ i, P i → Q (k i))
    (B : I → Over X₀) (B' : J → Over X₁) (A : Over X₀) (A' : Over X₁)
    [hB : ∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (B i).left)]
    [hB' : ∀ j, HasExt.{e} (AbelianSheaf.{u, u + 1} (B' j).left)]
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)]
    [hA' : HasExt.{e} (AbelianSheaf.{u, u + 1} A'.left)]
    (g₀ : X₁ ⟶ X₀) (r : ∀ i, (B' (k i)).left ⟶ (B i).left)
    (σ : A'.left ⟶ A.left)
    (hR : ∀ i, (B' (k i)).hom ≫ g₀ = r i ≫ (B i).hom)
    (hS : A'.hom ≫ g₀ = σ ≫ A.hom)
    (v : ∀ i, P i → (A ⟶ B i)) (v' : ∀ j, Q j → (A' ⟶ B' j))
    (hRect : ∀ i p, (v' (k i) (kp i p)).left ≫ r i = σ ≫ (v i p).left)
    (F₀ : AbelianSheaf.{u, u + 1} X₀) (q₀ : ℕ) {Z Z' : Type*}
    [AddCommGroup Z] [AddCommGroup Z']
    (γ : ∀ i, P i → Sheaf.H.{e} ((inverseImage (B i).hom).obj F₀) q₀ → Z)
    (γ' : ∀ j, Q j → Sheaf.H.{e} ((inverseImage (B' j).hom).obj
      ((inverseImage g₀).obj F₀)) q₀ → Z')
    (unit : Z →+ Z') (hγ : ∀ z : Z, ∃ i p y, γ i p y = z)
    (hunit : (indexedGermComparisonDataOfRelativeSquares P Q k kp B B' A A'
      g₀ r σ hR hS v v' hRect F₀ q₀ γ γ' unit hγ).UnitLaw)
    (b : Z →+ Sheaf.H.{e} ((inverseImage A.hom).obj F₀) q₀)
    (b' : Z' →+ Sheaf.H.{e} ((inverseImage A'.hom).obj ((inverseImage g₀).obj F₀)) q₀)
    (hsource : (indexedGermComparisonDataOfRelativeSquares P Q k kp B B' A A'
      g₀ r σ hR hS v v' hRect F₀ q₀ γ γ' unit hγ).SourceLaw b)
    (htarget : (indexedGermComparisonDataOfRelativeSquares P Q k kp B B' A A'
      g₀ r σ hR hS v v' hRect F₀ q₀ γ γ' unit hγ).TargetLaw b') :
    b'.comp unit = (cohomologySquareTransfer A.hom A'.hom g₀ σ hS F₀ q₀).hom.comp b := by
  apply AddMonoidHom.ext
  exact (indexedGermComparisonDataOfRelativeSquares P Q k kp B B' A A'
      g₀ r σ hR hS v v' hRect F₀ q₀ γ γ' unit hγ).square_of_laws
    hunit b b' hsource htarget

private theorem relativeCohomologyTransfer_mk_value
    {X₀ A₀ B₀ : Scheme.{u}}
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A₀)]
    [hB : HasExt.{e} (AbelianSheaf.{u, u + 1} B₀)]
    (a : A₀ ⟶ X₀) (b : B₀ ⟶ X₀) (v : Over.mk a ⟶ Over.mk b)
    (F₀ : AbelianSheaf.{u, u + 1} X₀) (q₀ : ℕ) :
    @relativeCohomologyTransfer.{u, e} X₀ F₀ q₀
      (Over.mk a) (Over.mk b) hA hB v =
      @cohomologyTriangleTransfer.{u, e} X₀ A₀ B₀ hA hB
        a b v.left (Over.w v) F₀ q₀ := rfl

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) {Ω : Type u} [hΩField : Field Ω] [hΩSep : IsSepClosed Ω]
  (ζ : Spec (.of Ω) ⟶ S')
  [hXExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [hX'Ext : HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  [hSourceSlice : ∀ U : S.Etale, HasExt.{s}
    (Sheaf (@GrothendieckTopology.over.{u, u + 1} X.Etale
      (inferInstance : Category.{u} X.Etale) (Scheme.smallEtaleTopology X)
      ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hTargetSlice : ∀ V : S'.Etale, HasExt.{s'}
    (Sheaf (@GrothendieckTopology.over.{u, u + 1} X'.Etale
      (inferInstance : Category.{u} X'.Etale) (Scheme.smallEtaleTopology X')
      ((siteBaseChange f').obj V)) AddCommGrpCat.{u + 1})]
  [hZU : ∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hZV : ∀ V : S'.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom f'))]
  [hFiber : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f))]
  [hFiber' : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f'))]

local instance geometricEquationSourceFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd (ζ ≫ g) f)).left) :=
  hFiber

local instance geometricEquationTargetFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd ζ f')).left) :=
  hFiber'

local instance geometricEquationSourceNeighborhoodExt
    (d : (pointSmallEtale (ζ ≫ g)).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω (ζ ≫ g) f).obj d).left) :=
  hZU d.obj

local instance geometricEquationTargetNeighborhoodExt
    (d : (pointSmallEtale ζ).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω ζ f').obj d).left) :=
  hZV d.obj

section ActualMap

variable (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The original stalk unit followed by the stalk of the supplied actual
sheaf morphism. This construction uses no derived-category model. -/
def higherDirectImageStalkMapOfHom
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F)) :
    ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
    ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) :=
  (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β).hom.comp
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)).hom

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV hFiber hFiber' in
/-- The actual-morphism constructor has the literal original unit formula. -/
theorem higherDirectImageStalkMapOfHom_apply
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (z : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β z =
      ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
          ((higherDirectImage f q).obj F) z) := rfl

/-- The exact comparison square for an actual sheaf morphism, retaining the
original geometric coefficient transfer and both original comparison maps. -/
def geometricCohomologyComparisonEquationOfHom
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) : Prop :=
  b'.comp (higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β) =
    (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q).hom.comp b

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV in
/-- The whole actual-morphism square is equivalent to its original pointwise formula. -/
theorem geometricCohomologyComparisonEquationOfHom_iff_original
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) :
    geometricCohomologyComparisonEquationOfHom.{u, e} f f' g g' h ζ
      (hFiber := hFiber) (hFiber' := hFiber') F q β b b' ↔
      ∀ z, b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
        geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) :=
  addHom_square_iff_prepost
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)).hom
    (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β).hom
    (higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β) rfl
    b b' (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q).hom

omit hXExt hX'Ext hSourceSlice hTargetSlice in
/-- The exact original raw-map rectangle, before any scalar evaluation. -/
theorem geometricCohomologyComparison_neighborhood_whole
    (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U) :
    (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f')
        g' (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q) ≫
      (relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
        (geometricFibrePointedMap Ω ζ f'
          { obj := (siteBaseChange g).obj U
            val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })) =
      (relativeCohomologyTransfer.{u, e} F q
        (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p })) ≫
        (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q) := by
  let T := cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
    ((inverseImageSquareIso (pullback.snd U.hom f)
      (pullback.snd ((siteBaseChange g).obj U).hom f')
      g' (fibreProductBaseChangeMap f f' g g' h U)
      (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q
  let uRaw := relativeCohomologyTransfer.{u, e} F q
    (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p })
  let vRaw := relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
    (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U,
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })
  let dRaw := geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
  let uTriangle := @cohomologyTriangleTransfer.{u, e} X
    (pullback (ζ ≫ g) f) (pullback U.hom f) hFiber (hZU U)
    (pullback.snd (ζ ≫ g) f) (pullback.snd U.hom f)
    (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left
    (Over.w (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p })) F q
  let vTriangle := @cohomologyTriangleTransfer.{u, e} X'
    (pullback ζ f') (pullback ((siteBaseChange g).obj U).hom f')
    hFiber' (hZV ((siteBaseChange g).obj U))
    (pullback.snd ζ f') (pullback.snd ((siteBaseChange g).obj U).hom f')
    (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U,
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left
    (Over.w (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U,
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }))
    ((inverseImage g').obj F) q
  let dSquare := @cohomologySquareTransfer.{u, e} X X'
    (pullback ζ f') (pullback (ζ ≫ g) f) hFiber' hFiber
    (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
    g' (geometricFibreBaseChangeMap f f' g g' h ζ)
    (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm F q
  change T ≫ vRaw = uRaw ≫ dRaw
  have hu : uRaw = uTriangle :=
    @relativeCohomologyTransfer_mk_value.{u, e} X
      (pullback (ζ ≫ g) f) (pullback U.hom f) hFiber (hZU U)
      (pullback.snd (ζ ≫ g) f) (pullback.snd U.hom f)
      (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) F q
  have hv : vRaw = vTriangle :=
    @relativeCohomologyTransfer_mk_value.{u, e} X'
      (pullback ζ f') (pullback ((siteBaseChange g).obj U).hom f')
      hFiber' (hZV ((siteBaseChange g).obj U))
      (pullback.snd ζ f') (pullback.snd ((siteBaseChange g).obj U).hom f')
      (geometricFibrePointedMap Ω ζ f'
        { obj := (siteBaseChange g).obj U
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })
      ((inverseImage g').obj F) q
  have hd : dRaw = dSquare := rfl
  have hP : T ≫ vTriangle = uTriangle ≫ dSquare :=
    @geometricFibreCohomologyTransfer_neighborhood_triangle.{u, e} X S X' S'
      f f' g g' h Ω hΩField hΩSep ζ hFiber hFiber' F q U
      (hZU U) (hZV ((siteBaseChange g).obj U)) p
      (fibreProductBaseChangeMap f f' g g' h U)
      (fibreProductBaseChangeMap_fst f f' g g' h U)
      (fibreProductBaseChangeMap_snd f f' g g' h U)
  exact (congrArg (fun k => T ≫ k) hv).trans
    (hP.trans (congrArg₂ (fun a b => a ≫ b) hu.symm hd.symm))

/-- Construct the original neighborhood germs, stalk unit followed by the given
morphism, relative transfers, determining family and whole rectangle once.
All comparison hypotheses and the conclusion below use this same construction. -/
def geometricCohomologyComparisonData
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F)) :
    IndexedGermComparisonData
      (fun U : S.Etale => (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (fun V : S'.Etale => (pointSmallEtale ζ).fiber.obj V)
      (fun U : S.Etale => Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q)
      (fun V : S'.Etale => Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q)
      (((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F))
      (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f' q).obj ((inverseImage g').obj F)))
      (Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
      (Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) :=
  indexedGermComparisonDataOfSchemeSquares
    (fun U : S.Etale => (pointSmallEtale (ζ ≫ g)).fiber.obj U)
    (fun V : S'.Etale => (pointSmallEtale ζ).fiber.obj V)
    (siteBaseChange g).obj (CoefficientStalkBaseChange.pulledBackPoint g ζ)
    (fun U : S.Etale => pullback U.hom f)
    (fun V : S'.Etale => pullback V.hom f')
    (fun U : S.Etale => pullback.snd U.hom f)
    (fun V : S'.Etale => pullback.snd V.hom f')
    (pullback (ζ ≫ g) f) (pullback ζ f')
    (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
    (hB := hZU) (hB' := hZV) (hA := hFiber) (hA' := hFiber')
    g' (fun U => fibreProductBaseChangeMap f f' g g' h U)
    (geometricFibreBaseChangeMap f f' g g' h ζ)
    (fun U => (fibreProductBaseChangeMap_snd f f' g g' h U).symm)
    (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm
    (fun U p => (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left)
    (fun V p => (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }).left)
    (fun U p => Over.w (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }))
    (fun V p => Over.w (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }))
    (fun U p => geometricFibrePointedMap_baseChange f f' g g' h ζ U p
      (fibreProductBaseChangeMap f f' g g' h U)
      (fibreProductBaseChangeMap_fst f f' g g' h U)
      (fibreProductBaseChangeMap_snd f f' g g' h U)) F q
    (fun U p y => @fibreProductCohomologyGerm.{u, w, s, e} X S f U
      hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)
    (fun V p y => @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
      hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y)
    (higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β)
    (exists_fibreProductCohomologyGerm.{u, w, s, e} f F q (ζ ≫ g))

/-- Normalize the complete original source triangle law before any derived
exchange is supplied. Every original neighborhood remains in the law. -/
theorem geometricCohomologyComparisonData_sourceLaw_iff
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (c : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q) :
    (geometricCohomologyComparisonData f f' g g' h ζ
      (hXExt := hXExt) (hX'Ext := hX'Ext)
      (hSourceSlice := hSourceSlice) (hTargetSlice := hTargetSlice)
      (hZU := hZU) (hZV := hZV) (hFiber := hFiber) (hFiber' := hFiber') F q β).SourceLaw c ↔
      ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
        (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      c (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y :=
  indexedGermComparisonDataOfSchemeSquares_sourceLaw_iff
    (fun U : S.Etale => (pointSmallEtale (ζ ≫ g)).fiber.obj U)
    (fun V : S'.Etale => (pointSmallEtale ζ).fiber.obj V)
    (siteBaseChange g).obj (CoefficientStalkBaseChange.pulledBackPoint g ζ)
    (fun U : S.Etale => pullback U.hom f)
    (fun V : S'.Etale => pullback V.hom f')
    (fun U : S.Etale => pullback.snd U.hom f)
    (fun V : S'.Etale => pullback.snd V.hom f')
    (pullback (ζ ≫ g) f) (pullback ζ f')
    (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
    (hB := hZU) (hB' := hZV) (hA := hFiber) (hA' := hFiber')
    g' (fun U => fibreProductBaseChangeMap f f' g g' h U)
    (geometricFibreBaseChangeMap f f' g g' h ζ)
    (fun U => (fibreProductBaseChangeMap_snd f f' g g' h U).symm)
    (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm
    (fun U p => (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left)
    (fun V p => (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }).left)
    (fun U p => Over.w (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }))
    (fun V p => Over.w (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }))
    (fun U p => geometricFibrePointedMap_baseChange f f' g g' h ζ U p
      (fibreProductBaseChangeMap f f' g g' h U)
      (fibreProductBaseChangeMap_fst f f' g g' h U)
      (fibreProductBaseChangeMap_snd f f' g g' h U)) F q
    (fun U p y => @fibreProductCohomologyGerm.{u, w, s, e} X S f U
      hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)
    (fun V p y => @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
      hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y)
    (higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β)
    (exists_fibreProductCohomologyGerm.{u, w, s, e} f F q (ζ ≫ g)) c

/-- Normalize the complete original target triangle law before any derived
exchange is supplied. Every original neighborhood remains in the law. -/
theorem geometricCohomologyComparisonData_targetLaw_iff
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (c : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) :
    (geometricCohomologyComparisonData f f' g g' h ζ
      (hXExt := hXExt) (hX'Ext := hX'Ext)
      (hSourceSlice := hSourceSlice) (hTargetSlice := hTargetSlice)
      (hZU := hZU) (hZV := hZV) (hFiber := hFiber) (hFiber' := hFiber') F q β).TargetLaw c ↔
      ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
        (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
          ((inverseImage g').obj F)) q),
      c (fibreProductCohomologyGerm.{u, w', s', e} f' V
        ((inverseImage g').obj F) q ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y :=
  indexedGermComparisonDataOfSchemeSquares_targetLaw_iff
    (fun U : S.Etale => (pointSmallEtale (ζ ≫ g)).fiber.obj U)
    (fun V : S'.Etale => (pointSmallEtale ζ).fiber.obj V)
    (siteBaseChange g).obj (CoefficientStalkBaseChange.pulledBackPoint g ζ)
    (fun U : S.Etale => pullback U.hom f)
    (fun V : S'.Etale => pullback V.hom f')
    (fun U : S.Etale => pullback.snd U.hom f)
    (fun V : S'.Etale => pullback.snd V.hom f')
    (pullback (ζ ≫ g) f) (pullback ζ f')
    (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
    (hB := hZU) (hB' := hZV) (hA := hFiber) (hA' := hFiber')
    g' (fun U => fibreProductBaseChangeMap f f' g g' h U)
    (geometricFibreBaseChangeMap f f' g g' h ζ)
    (fun U => (fibreProductBaseChangeMap_snd f f' g g' h U).symm)
    (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm
    (fun U p => (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left)
    (fun V p => (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }).left)
    (fun U p => Over.w (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }))
    (fun V p => Over.w (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }))
    (fun U p => geometricFibrePointedMap_baseChange f f' g g' h ζ U p
      (fibreProductBaseChangeMap f f' g g' h U)
      (fibreProductBaseChangeMap_fst f f' g g' h U)
      (fibreProductBaseChangeMap_snd f f' g g' h U)) F q
    (fun U p y => @fibreProductCohomologyGerm.{u, w, s, e} X S f U
      hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)
    (fun V p y => @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
      hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y)
    (higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β)
    (exists_fibreProductCohomologyGerm.{u, w, s, e} f F q (ζ ≫ g)) c



end ActualMap

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
