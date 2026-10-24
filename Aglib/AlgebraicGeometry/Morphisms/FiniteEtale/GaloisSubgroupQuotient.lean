/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Mathlib.CategoryTheory.Galois.GaloisObjects

/-!
# Actual subgroup quotients of finite etale Galois covers

For a native Galois cover `Y` of a connected scheme, the quotient by a subgroup
`H ≤ Aut Y` is the categorical colimit of the original automorphism action.
Its quotient arrow is the literal colimit inclusion, is finite etale and
surjective, and has connected target surjecting onto the original base.

The explicit geometric-fiber comparison sends the original quotient arrow to
the orbit-class map. Consequently two original lifts have the same image if
and only if one is carried to the other by an element of `H`. The orientation
in that equation is `h • a = b`. No normality hypothesis is imposed on `H`.
This file does not yet identify the relative deck group or the quotient rank.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)

/-- The action of the original subgroup of deck transformations on the
original finite etale cover, with no change of the automorphism universe. -/
def galoisSubgroupDiagram (H : Subgroup (Aut Y)) : SingleObj H ⥤ Scheme.FiniteEtale X :=
  SingleObj.functor ((Aut.toEnd Y).comp H.subtype)

@[simp]
theorem galoisSubgroupDiagram_obj (H : Subgroup (Aut Y)) (j : SingleObj H) :
    (galoisSubgroupDiagram Y H).obj j = Y := rfl

@[simp]
theorem galoisSubgroupDiagram_map (H : Subgroup (Aut Y)) (h : H) :
    (galoisSubgroupDiagram Y H).map (X := SingleObj.star H) (Y := SingleObj.star H) h =
      h.val.hom := rfl

variable [ConnectedSpace X] [IsGalois Y] (H : Subgroup (Aut Y))

/-- The actual subgroup quotient, defined by the original action colimit. -/
def galoisSubgroupQuotient : Scheme.FiniteEtale X :=
  colimit (galoisSubgroupDiagram Y H)

/-- The original quotient arrow is the colimit inclusion. -/
def galoisSubgroupQuotientπ : Y ⟶ galoisSubgroupQuotient Y H :=
  colimit.ι (galoisSubgroupDiagram Y H) (SingleObj.star H)

/-- The quotient arrow retains the original structural triangle over `X`. -/
@[reassoc]
theorem galoisSubgroupQuotientπ_structure :
    (galoisSubgroupQuotientπ Y H).hom.left ≫ (galoisSubgroupQuotient Y H).obj.hom =
      Y.obj.hom :=
  Over.w (galoisSubgroupQuotientπ Y H).hom

/-- Every original element of the subgroup acts trivially after quotienting. -/
@[reassoc (attr := simp)]
theorem galoisSubgroupQuotientπ_invariant (h : H) :
    h.val.hom ≫ galoisSubgroupQuotientπ Y H = galoisSubgroupQuotientπ Y H :=
  colimit.w (galoisSubgroupDiagram Y H) h

instance galoisSubgroupQuotientπ_epi : Epi (galoisSubgroupQuotientπ Y H) where
  left_cancellation a b hab := by
    apply colimit.hom_ext
    intro j
    cases j
    exact hab

instance galoisSubgroupQuotientπ_isFinite :
    IsFinite (galoisSubgroupQuotientπ Y H).hom.left :=
  Connectedness.hom_isFinite (galoisSubgroupQuotientπ Y H)

instance galoisSubgroupQuotientπ_etale :
    Etale (galoisSubgroupQuotientπ Y H).hom.left :=
  Connectedness.hom_etale (galoisSubgroupQuotientπ Y H)

/-- The literal quotient map is surjective on scheme points. -/
instance galoisSubgroupQuotientπ_surjective :
    Surjective (galoisSubgroupQuotientπ Y H).hom.left :=
  coverHom_surjective_of_epi (galoisSubgroupQuotientπ Y H)

/-- The quotient scheme is connected because it is the surjective image of
its original connected Galois cover. -/
instance galoisSubgroupQuotient_connectedSpace :
    ConnectedSpace (galoisSubgroupQuotient Y H).obj.left := by
  let : ConnectedSpace Y.obj.left := Connectedness.connectedSpace_of_categoricalConnected Y
  exact (galoisSubgroupQuotientπ Y H).hom.left.surjective.connectedSpace
    (galoisSubgroupQuotientπ Y H).hom.left.continuous

/-- The quotient is also connected in the native finite-etale category. -/
instance galoisSubgroupQuotient_isConnected : IsConnected (galoisSubgroupQuotient Y H) :=
  Connectedness.categoricalConnected_of_connectedSpace (galoisSubgroupQuotient Y H)

/-- The quotient's original structural morphism is surjective over the
connected base; it is not asserted to be a Galois morphism. -/
instance galoisSubgroupQuotient_structure_surjective :
    Surjective (galoisSubgroupQuotient Y H).obj.hom :=
  ⟨Set.range_eq_univ.mp
    ((structural_range_isClopen (galoisSubgroupQuotient Y H)).eq_univ (Set.range_nonempty _))⟩

section Fiber

variable {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X)

/-- The actual geometric fiber of the original quotient is the orbit set of
the original subgroup action on the original geometric fiber. -/
def galoisSubgroupQuotientFiberEquiv :
    Fiber s (galoisSubgroupQuotient Y H) ≃
      MulAction.orbitRel.Quotient H ((fiberToFinite s).obj Y) :=
  (preservesColimitIso ((fiberToFinite s) ⋙ FintypeCat.incl)
    (galoisSubgroupDiagram Y H)).toEquiv.trans
      (SingleObj.Types.colimitEquivQuotient
        (galoisSubgroupDiagram Y H ⋙ fiberToFinite s ⋙ FintypeCat.incl))

/-- The comparison sends the image under the original quotient arrow to the
orbit class of the same original lift. -/
theorem galoisSubgroupQuotientFiberEquiv_map (a : Fiber s Y) :
    galoisSubgroupQuotientFiberEquiv Y H s
        ((fiberToFinite s).map (galoisSubgroupQuotientπ Y H) a) = Quotient.mk _ a := by
  change (SingleObj.Types.colimitEquivQuotient
    (galoisSubgroupDiagram Y H ⋙ fiberToFinite s ⋙ FintypeCat.incl))
      ((preservesColimitIso ((fiberToFinite s) ⋙ FintypeCat.incl)
        (galoisSubgroupDiagram Y H)).hom
          (((fiberToFinite s) ⋙ FintypeCat.incl).map
            (colimit.ι (galoisSubgroupDiagram Y H) (SingleObj.star H)) a)) = _
  have h := ConcreteCategory.congr_hom
    (ι_preservesColimitIso_hom ((fiberToFinite s) ⋙ FintypeCat.incl)
      (galoisSubgroupDiagram Y H) (SingleObj.star H)) a
  change (preservesColimitIso ((fiberToFinite s) ⋙ FintypeCat.incl)
    (galoisSubgroupDiagram Y H)).hom
      (((fiberToFinite s) ⋙ FintypeCat.incl).map
        (colimit.ι (galoisSubgroupDiagram Y H) (SingleObj.star H)) a) =
      colimit.ι (galoisSubgroupDiagram Y H ⋙ fiberToFinite s ⋙ FintypeCat.incl)
        (SingleObj.star H) a at h
  rw [h]
  change (SingleObj.colimitTypeRelEquivOrbitRelQuotient
    (galoisSubgroupDiagram Y H ⋙ fiberToFinite s ⋙ FintypeCat.incl))
      ((Types.colimitEquivColimitType
        (galoisSubgroupDiagram Y H ⋙ fiberToFinite s ⋙ FintypeCat.incl))
          (colimit.ι (galoisSubgroupDiagram Y H ⋙ fiberToFinite s ⋙ FintypeCat.incl)
            (SingleObj.star H) a)) = _
  rw [Types.colimitEquivColimitType_apply]
  rfl

/-- Two original fiber points have the same quotient image exactly when an
original subgroup automorphism carries the first to the second. -/
theorem galoisSubgroupQuotient_fiber_map_eq_iff (a b : Fiber s Y) :
    (fiberToFinite s).map (galoisSubgroupQuotientπ Y H) a =
        (fiberToFinite s).map (galoisSubgroupQuotientπ Y H) b ↔
      ∃ h : H, (fiberToFinite s).map h.val.hom a = b := by
  constructor
  · intro hab
    have h := congrArg (galoisSubgroupQuotientFiberEquiv Y H s) hab
    rw [galoisSubgroupQuotientFiberEquiv_map, galoisSubgroupQuotientFiberEquiv_map] at h
    exact MulAction.mem_orbit_iff.mp
      ((MulAction.orbitRel H ((fiberToFinite s).obj Y)).symm (Quotient.exact h))
  · rintro ⟨h, hh⟩
    apply (galoisSubgroupQuotientFiberEquiv Y H s).injective
    rw [galoisSubgroupQuotientFiberEquiv_map, galoisSubgroupQuotientFiberEquiv_map]
    exact Quotient.sound
      ((MulAction.orbitRel H ((fiberToFinite s).obj Y)).symm ⟨h, hh⟩)

/-- The original quotient arrow is surjective on every geometric fiber. -/
theorem galoisSubgroupQuotient_fiber_surjective :
    Function.Surjective ((fiberToFinite s).map (galoisSubgroupQuotientπ Y H)) :=
  fiberToFinite_surjective_of_epi s (galoisSubgroupQuotientπ Y H)

end Fiber

end AlgebraicGeometry.Scheme.FiniteEtale
