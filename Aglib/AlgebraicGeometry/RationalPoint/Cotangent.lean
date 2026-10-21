/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.SmoothCurve
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual cotangent maps at rational points

The cotangent space is the maximal ideal of the original structure-sheaf stalk
modulo its square. Its scalar action uses the structural constants of the
rational point. Maps are induced by the original scheme stalk map, with only
the point equality transported by the native stalk comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

/-- The native stalk pullback with its target point explicitly identified. -/
def stalkMapAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  (Y.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ f.stalkMap x

@[simp] theorem stalkMapAt_self {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    stalkMapAt f x (f x) rfl = f.stalkMap x := by
  simp [stalkMapAt, TopCat.Presheaf.stalkCongr]

instance stalkMapAt_isLocal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y) : IsLocalHom (stalkMapAt f x y h).hom := by
  subst y
  simp only [stalkMapAt_self]
  infer_instance

@[simp] theorem stalkMapAt_id {X : Scheme.{u}} (x : X) :
    stalkMapAt (𝟙 X) x x rfl = 𝟙 _ := by
  simp [stalkMapAt, TopCat.Presheaf.stalkCongr]

theorem stalkMapAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z) (hf : f x = y) (hg : g y = z) :
    stalkMapAt (f ≫ g) x z ((congrArg g hf).trans hg) =
      stalkMapAt g y z hg ≫ stalkMapAt f x y hf := by
  subst y
  subst z
  simpa [stalkMapAt, TopCat.Presheaf.stalkCongr] using Scheme.Hom.stalkMap_comp f g x

/-- Structural constants, as a categorical map into the actual stalk. -/
def stalkConstants {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (x : X) : CommRingCat.of k ⟶ X.presheaf.stalk x :=
  (RationalPoint.fieldStalkIso k (p x)).inv ≫ p.stalkMap x

theorem stalkConstants_congr {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (x y : X) (h : x = y) :
    stalkConstants p x ≫ (X.presheaf.stalkCongr (.of_eq h)).hom =
      stalkConstants p y := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

theorem stalkConstants_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (p : Y ⟶ Spec (.of k)) (x : X) :
    stalkConstants (f ≫ p) x = stalkConstants p (f x) ≫ f.stalkMap x := by
  simp [stalkConstants, Scheme.Hom.stalkMap_comp]

theorem stalkMapAt_constants {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (p : X ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of k))
    (hp : f ≫ q = p) (x : X) (y : Y) (h : f x = y) :
    stalkConstants q y ≫ stalkMapAt f x y h = stalkConstants p x := by
  rw [stalkMapAt, ← Category.assoc, stalkConstants_congr q y (f x) h.symm,
    ← stalkConstants_comp, hp]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.OverField.Cotangent

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The original rational section, as the existing native rational-point data. -/
def pointData {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X) : RationalPoint k X.left where
  structureMap := X.hom
  sectionMap := x.left
  section_comp := x.w

/-- The actual maximal-ideal cotangent quotient at the rational point. -/
def Space {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X) : Type u :=
  IsLocalRing.CotangentSpace (pointData x).localRing

instance {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X) : AddCommGroup (Space x) :=
  inferInstanceAs (AddCommGroup (IsLocalRing.CotangentSpace (pointData x).localRing))

instance spaceModule {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X) : Module k (Space x) := by
  let := (pointData x).constants.toAlgebra
  exact inferInstanceAs (Module k (IsLocalRing.CotangentSpace (pointData x).localRing))

theorem point_eq {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (f : X ⟶ Y) (h : x ≫ f = y) :
    f.left (pointData x).point = (pointData y).point :=
  congrArg (fun a : 𝟙_ (FScheme k) ⟶ Y => a.left (IsLocalRing.closedPoint k)) h

/-- The actual local pullback of a morphism carrying one rational point to another. -/
def localMap {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (f : X ⟶ Y) (h : x ≫ f = y) :
    (pointData y).localRing →+* (pointData x).localRing :=
  (Scheme.stalkMapAt f.left (pointData x).point (pointData y).point
    (point_eq x y f h)).hom

instance localMap_isLocal {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (f : X ⟶ Y) (h : x ≫ f = y) :
    IsLocalHom (localMap x y f h) := inferInstanceAs (IsLocalHom (Scheme.stalkMapAt
      f.left (pointData x).point (pointData y).point (point_eq x y f h)).hom)

theorem localMap_constants {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (f : X ⟶ Y) (h : x ≫ f = y) :
    (localMap x y f h).comp (pointData y).constants = (pointData x).constants := by
  exact congrArg CommRingCat.Hom.hom
    (Scheme.stalkMapAt_constants f.left X.hom Y.hom f.w
      (pointData x).point (pointData y).point (point_eq x y f h))

@[simp] theorem localMap_id {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X) :
    localMap x x (𝟙 X) (by simp) = RingHom.id _ := by
  simp [localMap, Scheme.stalkMapAt, TopCat.Presheaf.stalkCongr]

theorem localMap_comp {X Y Z : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (z : 𝟙_ (FScheme k) ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : x ≫ f = y) (hg : y ≫ g = z) :
    localMap x z (f ≫ g) (by rw [← Category.assoc, hf, hg]) =
      (localMap x y f hf).comp (localMap y z g hg) := by
  exact congrArg CommRingCat.Hom.hom (Scheme.stalkMapAt_comp f.left g.left
    (pointData x).point (pointData y).point (pointData z).point
    (point_eq x y f hf) (point_eq y z g hg))

/-- Cotangent pullback on the original maximal-ideal quotients. -/
def map {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (f : X ⟶ Y) (h : x ≫ f = y) :
    Space y →ₗ[k] Space x := by
  let := (pointData x).constants.toAlgebra
  let := (pointData y).constants.toAlgebra
  let φ : (pointData y).localRing →ₐ[k] (pointData x).localRing :=
    { localMap x y f h with
      commutes' := fun a => DFunLike.congr_fun (localMap_constants x y f h) a }
  exact Ideal.mapCotangent (IsLocalRing.maximalIdeal (pointData y).localRing)
    (IsLocalRing.maximalIdeal (pointData x).localRing) φ
    (fun a ha => _root_.map_nonunit (localMap x y f h) a ha)

/-- Equality of the original morphisms preserves their cotangent pullbacks;
the proofs of the rational-point equation carry no extra data. -/
theorem map_congr {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) {f g : X ⟶ Y} (hfg : f = g)
    (hf : x ≫ f = y) (hg : x ≫ g = y) : map x y f hf = map x y g hg := by
  subst g
  rfl

@[simp] theorem map_toCotangent {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (f : X ⟶ Y) (h : x ≫ f = y)
    (a : IsLocalRing.maximalIdeal (pointData y).localRing) :
    map x y f h ((IsLocalRing.maximalIdeal _).toCotangent a) =
      (IsLocalRing.maximalIdeal _).toCotangent
        ⟨localMap x y f h a, _root_.map_nonunit (localMap x y f h) a a.property⟩ := rfl

@[simp] theorem map_id {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X) :
    map x x (𝟙 X) (by simp) = LinearMap.id := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal _) a
  simp only [map_toCotangent, localMap_id, RingHom.id_apply, LinearMap.id_apply]

theorem map_comp {X Y Z : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (z : 𝟙_ (FScheme k) ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : x ≫ f = y) (hg : y ≫ g = z) :
    map x z (f ≫ g) (by rw [← Category.assoc, hf, hg]) =
      (map x y f hf).comp (map y z g hg) := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal _) a
  simp only [map_toCotangent, LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  exact DFunLike.congr_fun (localMap_comp x y z f g hf hg)
    (a : (pointData z).localRing)

/-- The actual rational-point cotangent space is finite dimensional over the
original base field for every locally finite type field scheme. -/
instance finiteDimensional {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    [LocallyOfFiniteType X.hom] : FiniteDimensional k (Space x) := by
  let q := pointData x
  let R := q.localRing
  let K := IsLocalRing.ResidueField R
  let := q.constants.toAlgebra
  let : Algebra k K := Ideal.Quotient.algebra k (I := IsLocalRing.maximalIdeal R)
  let : IsScalarTower k R K := Ideal.Quotient.isScalarTower k R (IsLocalRing.maximalIdeal R)
  let : IsScalarTower k K (IsLocalRing.CotangentSpace R) :=
    IsScalarTower.of_algebraMap_smul fun a v =>
      (IsScalarTower.algebraMap_smul K (algebraMap k R a) v).trans
        (IsScalarTower.algebraMap_smul R a v)
  let : LocallyOfFiniteType q.structureMap := ‹LocallyOfFiniteType X.hom›
  let : IsNoetherianRing R := q.localRing_isNoetherianRing
  let e : K ≃ₐ[k] k :=
    { q.residueEquiv with commutes' := fun a => q.residueEquiv_constants a }
  let : Module.Finite k K := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.trans K (IsLocalRing.CotangentSpace R)

/-- Smooth relative dimension computes the cotangent dimension over the same
original base field, using the actual section-induced residue equivalence. -/
theorem finrank {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] : Module.finrank k (Space x) = n := by
  let q := pointData x
  let R := q.localRing
  let K := IsLocalRing.ResidueField R
  let := q.constants.toAlgebra
  let : Algebra k K := Ideal.Quotient.algebra k (I := IsLocalRing.maximalIdeal R)
  let : IsScalarTower k R K := Ideal.Quotient.isScalarTower k R (IsLocalRing.maximalIdeal R)
  let : IsScalarTower k K (IsLocalRing.CotangentSpace R) :=
    IsScalarTower.of_algebraMap_smul fun a v =>
      (IsScalarTower.algebraMap_smul K (algebraMap k R a) v).trans
        (IsScalarTower.algebraMap_smul R a v)
  let : SmoothOfRelativeDimension n q.structureMap := ‹SmoothOfRelativeDimension n X.hom›
  let e : K ≃ₐ[k] k :=
    { q.residueEquiv with commutes' := fun a => q.residueEquiv_constants a }
  have hK : Module.finrank k K = 1 := by
    rw [e.toLinearEquiv.finrank_eq]
    exact Module.finrank_self k
  change Module.finrank k (IsLocalRing.CotangentSpace R) = n
  rw [← Module.finrank_mul_finrank k K _, hK, one_mul]
  exact q.localRing_finrank_cotangentSpace n

/-- The actual constant morphism to a rational point induces the zero map on
the maximal-ideal cotangent quotient. -/
@[simp] theorem map_constant {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) :
    map x y (toUnit X ≫ y) (by simp) = 0 := by
  let t : 𝟙_ (FScheme k) ⟶ 𝟙_ (FScheme k) := 𝟙 _
  let : SmoothOfRelativeDimension 0 (𝟙_ (FScheme k)).hom := by
    change SmoothOfRelativeDimension 0 (𝟙 (Base k))
    infer_instance
  let : LocallyOfFiniteType (𝟙_ (FScheme k)).hom := by
    change LocallyOfFiniteType (𝟙 (Base k))
    infer_instance
  let : Subsingleton (Space t) := (Module.finrank_zero_iff).mp (finrank t 0)
  rw [map_comp x t y (toUnit X) y (by simp [t]) (by simp [t])]
  ext a
  change map x t (toUnit X) _ (map t y y _ a) = 0
  rw [Subsingleton.elim (map t y y _ a) 0, map_zero]

/-- The actual first axis through the selected pair of rational points. -/
def axisLeft {X Y : FScheme k} (_x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) : X ⟶ X ⊗ Y := lift (𝟙 X) (toUnit X ≫ y)

/-- The actual second axis through the selected pair of rational points. -/
def axisRight {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (_y : 𝟙_ (FScheme k) ⟶ Y) : Y ⟶ X ⊗ Y := lift (toUnit Y ≫ x) (𝟙 Y)

@[simp] theorem axisLeft_point {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) : x ≫ axisLeft x y = lift x y := by
  simp [axisLeft]

@[simp] theorem axisRight_point {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) : y ≫ axisRight x y = lift x y := by
  simp [axisRight]

/-- Restrictions along the two literal axes. -/
def axes {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) : Space (lift x y) →ₗ[k] Space x × Space y :=
  (map x (lift x y) (axisLeft x y) (axisLeft_point x y)).prod
    (map y (lift x y) (axisRight x y) (axisRight_point x y))

/-- The sum of pullback along the two original product projections. -/
def projections {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) : Space x × Space y →ₗ[k] Space (lift x y) :=
  (map (lift x y) x (fst X Y) (by simp)).coprod
    (map (lift x y) y (snd X Y) (by simp))

/-- Axis restriction is a left inverse to the sum of projection pullbacks.
Both diagonal and both zero cross terms follow from the actual scheme maps. -/
theorem axes_projections {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) :
    (axes x y).comp (projections x y) = LinearMap.id := by
  have h₁₁ : (map x (lift x y) (axisLeft x y) (axisLeft_point x y)).comp
      (map (lift x y) x (fst X Y) (by simp)) = LinearMap.id := by
    rw [← map_comp]
    simp [axisLeft]
  have h₁₂ : (map x (lift x y) (axisLeft x y) (axisLeft_point x y)).comp
      (map (lift x y) y (snd X Y) (by simp)) = 0 := by
    rw [← map_comp]
    simp [axisLeft]
  have h₂₁ : (map y (lift x y) (axisRight x y) (axisRight_point x y)).comp
      (map (lift x y) x (fst X Y) (by simp)) = 0 := by
    rw [← map_comp]
    simp [axisRight]
  have h₂₂ : (map y (lift x y) (axisRight x y) (axisRight_point x y)).comp
      (map (lift x y) y (snd X Y) (by simp)) = LinearMap.id := by
    rw [← map_comp]
    simp [axisRight]
  apply LinearMap.ext
  intro a
  apply Prod.ext
  · simpa [axes, projections] using
      congrArg₂ (· + ·) (LinearMap.congr_fun h₁₁ a.1) (LinearMap.congr_fun h₁₂ a.2)
  · simpa [axes, projections] using
      congrArg₂ (· + ·) (LinearMap.congr_fun h₂₁ a.1) (LinearMap.congr_fun h₂₂ a.2)

/-- Smooth dimensions add for the original fiber product over the field. -/
theorem tensor_smooth {X Y : FScheme k} (n m : ℕ)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension m Y.hom] :
    SmoothOfRelativeDimension (n + m) (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom, Nat.add_comm n m]
  let : SmoothOfRelativeDimension m (Limits.pullback.fst X.hom Y.hom) :=
    MorphismProperty.pullback_fst X.hom Y.hom ‹SmoothOfRelativeDimension m Y.hom›
  exact smoothOfRelativeDimension_comp m n (Limits.pullback.fst X.hom Y.hom) X.hom

/-- For smooth field schemes, the actual axis restriction map on cotangent
spaces is injective. Smooth dimensions and the proved split maps supply this. -/
theorem axes_injective {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (n m : ℕ)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension m Y.hom] :
    Function.Injective (axes x y) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth n X.hom
  let : Smooth Y.hom := SmoothOfRelativeDimension.smooth m Y.hom
  let : SmoothOfRelativeDimension (n + m) (X ⊗ Y).hom := tensor_smooth n m
  let : Smooth (X ⊗ Y).hom := SmoothOfRelativeDimension.smooth (n + m) (X ⊗ Y).hom
  have hs : Function.Surjective (axes x y) := by
    intro v
    exact ⟨projections x y v, LinearMap.congr_fun (axes_projections x y) v⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hs
  rw [Module.finrank_prod, finrank x n, finrank y m, finrank (lift x y) (n + m)]

end AlgebraicGeometry.Scheme.OverField.Cotangent
