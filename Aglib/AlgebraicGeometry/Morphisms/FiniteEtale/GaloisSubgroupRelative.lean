/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSubgroupQuotient

/-!
# The original Galois cover relative to its subgroup quotient

For an actual Galois cover `Y` and `H ≤ Aut Y`, the original quotient map
makes the unchanged scheme `Y` a Galois cover of the actual quotient scheme.
Its relative deck group is `H`, with unchanged underlying scheme maps. The
fiber comparison retains the literal geometric lifts and the original
quotient map. No normality hypothesis or Galois assertion for the quotient
itself over the original base is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable {X : Scheme.{u}} [ConnectedSpace X]
variable (Y : Scheme.FiniteEtale X) [IsGalois Y] (H : Subgroup (Aut Y))

/-- The unchanged source scheme, regarded as a finite etale cover of its
actual subgroup quotient using the original quotient arrow. -/
def galoisSubgroupRelative : Scheme.FiniteEtale (galoisSubgroupQuotient Y H).obj.left :=
  mk (galoisSubgroupQuotientπ Y H).hom.left

@[simp]
theorem galoisSubgroupRelative_structure :
    (galoisSubgroupRelative Y H).obj.hom = (galoisSubgroupQuotientπ Y H).hom.left := rfl

instance galoisSubgroupRelative_surjective :
    Surjective (galoisSubgroupRelative Y H).obj.hom :=
  galoisSubgroupQuotientπ_surjective Y H

instance galoisSubgroupRelative_connectedSpace :
    ConnectedSpace (galoisSubgroupRelative Y H).obj.left :=
  Connectedness.connectedSpace_of_categoricalConnected Y

instance galoisSubgroupRelative_isConnected : IsConnected (galoisSubgroupRelative Y H) :=
  Connectedness.categoricalConnected_of_connectedSpace (galoisSubgroupRelative Y H)

/-- An original subgroup automorphism, with the same scheme hom and inverse,
regarded over the actual subgroup quotient. -/
def galoisSubgroupRelativeAut (h : H) : Aut (galoisSubgroupRelative Y H) where
  hom := ObjectProperty.homMk (Over.homMk h.val.hom.hom.left
    (congrArg (fun f : Y ⟶ galoisSubgroupQuotient Y H => f.hom.left)
      (galoisSubgroupQuotientπ_invariant Y H h)))
  inv := ObjectProperty.homMk (Over.homMk h.val.inv.hom.left
    (congrArg (fun f : Y ⟶ galoisSubgroupQuotient Y H => f.hom.left)
      (galoisSubgroupQuotientπ_invariant Y H h⁻¹)))
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change h.val.hom.hom.left ≫ h.val.inv.hom.left = 𝟙 Y.obj.left
    have he := congrArg (fun f : Y ⟶ Y => f.hom.left) h.val.hom_inv_id
    exact he
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change h.val.inv.hom.left ≫ h.val.hom.hom.left = 𝟙 Y.obj.left
    have he := congrArg (fun f : Y ⟶ Y => f.hom.left) h.val.inv_hom_id
    exact he

/-- The original subgroup acts on the relative cover by its unchanged
scheme automorphisms. -/
def galoisSubgroupRelativeAutHom : H →* Aut (galoisSubgroupRelative Y H) where
  toFun := galoisSubgroupRelativeAut Y H
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_mul' h k := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

@[simp]
theorem galoisSubgroupRelativeAutHom_hom_left (h : H) :
    (galoisSubgroupRelativeAutHom Y H h).hom.hom.left = h.val.hom.hom.left := rfl

@[simp]
theorem galoisSubgroupRelativeAutHom_inv_left (h : H) :
    (galoisSubgroupRelativeAutHom Y H h).inv.hom.left = h.val.inv.hom.left := rfl

/-- Forgetting to the original scheme proves injectivity of the subgroup's
relative deck action. -/
theorem galoisSubgroupRelativeAutHom_injective :
    Function.Injective (galoisSubgroupRelativeAutHom Y H) := by
  intro h k hhk
  apply Subtype.ext
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact congrArg (fun σ : Aut (galoisSubgroupRelative Y H) => σ.hom.hom.left) hhk

section Fiber

variable {K : Type u} [Field K]
variable (t : Spec (CommRingCat.of K) ⟶ (galoisSubgroupQuotient Y H).obj.left)

/-- The relative fiber consists of exactly those original lifts whose image
under the original quotient map is the given quotient lift. Both directions
retain the same morphism from `Spec K` to the unchanged source scheme. -/
def galoisSubgroupRelativeFiberEquiv :
    Fiber t (galoisSubgroupRelative Y H) ≃
      {a : Fiber (t ≫ (galoisSubgroupQuotient Y H).obj.hom) Y //
        (fiberToFinite (t ≫ (galoisSubgroupQuotient Y H).obj.hom)).map
          (galoisSubgroupQuotientπ Y H) a = Over.homMk t rfl} where
  toFun a := ⟨Over.homMk a.left (by
    change a.left ≫ Y.obj.hom = t ≫ (galoisSubgroupQuotient Y H).obj.hom
    rw [← galoisSubgroupQuotientπ_structure Y H, ← Category.assoc]
    exact congrArg (fun f => f ≫ (galoisSubgroupQuotient Y H).obj.hom) (Over.w a)), by
      apply Over.OverMorphism.ext
      exact Over.w a⟩
  invFun a := Over.homMk a.val.left
    (congrArg (fun b : Fiber (t ≫ (galoisSubgroupQuotient Y H).obj.hom)
      (galoisSubgroupQuotient Y H) => b.left) a.property)
  left_inv a := by
    apply Over.OverMorphism.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    rfl

theorem galoisSubgroupRelativeFiberEquiv_apply_left (a : Fiber t (galoisSubgroupRelative Y H)) :
    (galoisSubgroupRelativeFiberEquiv Y H t a).val.left = a.left := rfl

theorem galoisSubgroupRelativeFiberEquiv_map (h : H)
    (a : Fiber t (galoisSubgroupRelative Y H)) :
    (galoisSubgroupRelativeFiberEquiv Y H t
      ((fiberToFinite t).map (galoisSubgroupRelativeAutHom Y H h).hom a)).val =
        (fiberToFinite (t ≫ (galoisSubgroupQuotient Y H).obj.hom)).map h.val.hom
          (galoisSubgroupRelativeFiberEquiv Y H t a).val := by
  apply Over.OverMorphism.ext
  rfl

variable [IsSepClosed K]

/-- The original subgroup acts transitively on every relative geometric
fiber, by the accepted original quotient-fiber equation. -/
theorem galoisSubgroupRelative_fiber_transitive (a b : Fiber t (galoisSubgroupRelative Y H)) :
    ∃ h : H, (fiberToFinite t).map (galoisSubgroupRelativeAutHom Y H h).hom a = b := by
  let e := galoisSubgroupRelativeFiberEquiv Y H t
  obtain ⟨h, hh⟩ := (galoisSubgroupQuotient_fiber_map_eq_iff Y H
    (t ≫ (galoisSubgroupQuotient Y H).obj.hom) (e a).val (e b).val).mp
      ((e a).property.trans (e b).property.symm)
  refine ⟨h, ?_⟩
  apply Over.OverMorphism.ext
  exact congrArg (fun c : Fiber (t ≫ (galoisSubgroupQuotient Y H).obj.hom) Y => c.left) hh

include t in
/-- Native Galois evaluation at the specified actual geometric point proves
that the original quotient arrow is a Galois cover. -/
theorem galoisSubgroupRelative_isGalois_at : IsGalois (galoisSubgroupRelative Y H) := by
  have : MulAction.IsPretransitive (Aut (galoisSubgroupRelative Y H))
      ((fiberToFinite t).obj (galoisSubgroupRelative Y H)) := ⟨fun a b => by
    obtain ⟨h, hh⟩ := galoisSubgroupRelative_fiber_transitive Y H t a b
    exact ⟨galoisSubgroupRelativeAutHom Y H h, hh⟩⟩
  exact (isGalois_iff_pretransitive (fiberToFinite t) (galoisSubgroupRelative Y H)).mpr
    inferInstance

end Fiber

instance galoisSubgroupRelative_isGalois : IsGalois (galoisSubgroupRelative Y H) :=
  galoisSubgroupRelative_isGalois_at Y H
    (algebraicClosureResiduePoint (galoisSubgroupQuotient Y H).obj.left
      (Classical.choice (inferInstance : Nonempty (galoisSubgroupQuotient Y H).obj.left)))

/-- Every relative deck transformation agrees at one geometric point with
an original subgroup element, hence is that element by native evaluation. -/
theorem galoisSubgroupRelativeAutHom_surjective :
    Function.Surjective (galoisSubgroupRelativeAutHom Y H) := by
  let t := algebraicClosureResiduePoint (galoisSubgroupQuotient Y H).obj.left
    (Classical.choice (inferInstance : Nonempty (galoisSubgroupQuotient Y H).obj.left))
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected (fiberToFinite t) (galoisSubgroupRelative Y H)
  intro σ
  obtain ⟨h, hh⟩ := galoisSubgroupRelative_fiber_transitive Y H t a
    ((fiberToFinite t).map σ.hom a)
  exact ⟨h, evaluation_aut_injective_of_isConnected (fiberToFinite t)
    (galoisSubgroupRelative Y H) a hh⟩

/-- The relative deck group is the original subgroup, not a replacement
abstract group, and no normality is needed. -/
def galoisSubgroupDeckEquiv : H ≃* Aut (galoisSubgroupRelative Y H) :=
  MulEquiv.ofBijective (galoisSubgroupRelativeAutHom Y H)
    ⟨galoisSubgroupRelativeAutHom_injective Y H, galoisSubgroupRelativeAutHom_surjective Y H⟩

@[simp]
theorem galoisSubgroupDeckEquiv_hom_left (h : H) :
    (galoisSubgroupDeckEquiv Y H h).hom.hom.left = h.val.hom.hom.left := rfl

@[simp]
theorem galoisSubgroupDeckEquiv_inv_left (h : H) :
    (galoisSubgroupDeckEquiv Y H h).inv.hom.left = h.val.inv.hom.left := rfl

end AlgebraicGeometry.Scheme.FiniteEtale
