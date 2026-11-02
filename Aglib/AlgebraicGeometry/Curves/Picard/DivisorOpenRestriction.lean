/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Divisors.OpenPrincipal
public import Aglib.AlgebraicGeometry.Curves.Picard.LocalTrivialization
public import Aglib.AlgebraicGeometry.FunctionField.OpenRestriction

/-! # Original divisor sheaves under open restriction

Open restriction preserves the actual fractional-section conditions through
the actual map of function fields. The comparison uses the original
closed-point divisors, not a replacement Picard model.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

variable {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
  [IsNoetherian U] [IsNoetherian X] [JacobsonSpace X]
  [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  (j : U ⟶ X) [IsOpenImmersion j]

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j

/-- The original fractional-section inequalities are equivalent on an open
and its actual open image, under the original function-field pullback. -/
theorem isFractionalSection_openRestriction_iff (D : Divisor X) (V : U.Opens)
    (f : X.functionField) :
    IsFractionalSection U (openRestriction j D) V (Scheme.functionFieldMap j f) ↔
      IsFractionalSection X D (j ''ᵁ V) f := by
  constructor
  · rintro (hf | hf)
    · left
      exact (Scheme.FunctionField.fieldEquiv j).injective (by simpa using hf)
    · right
      intro x hx
      obtain ⟨y, hy⟩ := (ClosedPoint.mem_range_openEmbedding_iff j x).mpr
        (by obtain ⟨z, _, hz⟩ := hx; exact ⟨z, hz⟩)
      have hv : y.val ∈ V := by
        obtain ⟨z, hz, hzx⟩ := hx
        have hzy : z = y.val := j.isOpenEmbedding.injective
          (hzx.trans (congrArg Subtype.val hy).symm)
        exact hzy ▸ hz
      have h := hf y hv
      let : IsDiscreteValuationRing (X.presheaf.stalk (j y.val)) :=
        inferInstanceAs (IsDiscreteValuationRing
          (X.presheaf.stalk (ClosedPoint.openEmbedding j y).val))
      rw [order_functionFieldMap_openImmersion, openRestriction_apply] at h
      simpa only [← hy, ClosedPoint.openEmbedding_apply_val] using h
  · rintro (rfl | hf)
    · exact Or.inl (map_zero _)
    · right
      intro y hy
      let : IsDiscreteValuationRing (X.presheaf.stalk (j y.val)) :=
        inferInstanceAs (IsDiscreteValuationRing
          (X.presheaf.stalk (ClosedPoint.openEmbedding j y).val))
      rw [order_functionFieldMap_openImmersion, openRestriction_apply]
      exact hf (ClosedPoint.openEmbedding j y) ⟨y.val, hy, rfl⟩


local instance (V : U.Opens) [hV : Nonempty V] : Nonempty (j ''ᵁ V) :=
  ⟨⟨j hV.some.val, hV.some.val, hV.some.property, rfl⟩⟩

/-- On a nonempty open, actual restricted sections map linearly to the
fractional sections of the restricted divisor by their original rational values. -/
def openSectionValueMap (D : Divisor X) (V : U.Opens) [Nonempty V] :
    Γ((Modules.restrictFunctor j).obj (divisorSheaf X D), V) →ₗ[Γ(U, V)]
      fractionalSections U (openRestriction j D) V where
  toFun s := ⟨Scheme.functionFieldMap j ((rationalValue X (j ''ᵁ V)).toFun s.val),
    (isFractionalSection_openRestriction_iff j D V _).mpr
      ((explicitSheafSectionsEquiv X D (j ''ᵁ V)).toFun s).property⟩
  map_add' s t := by
    let : Module Γ(X, j ''ᵁ V) ((rationalFunctions X).val.obj (op (j ''ᵁ V))) :=
      ((rationalFunctions X).val.obj (op (j ''ᵁ V))).isModule
    apply Subtype.ext
    exact (congrArg (Scheme.functionFieldMap j)
      ((rationalValue X (j ''ᵁ V)).map_add s.val t.val)).trans
        ((Scheme.functionFieldMap j).map_add _ _)
  map_smul' a s := by
    let : Module Γ(X, j ''ᵁ V) ((rationalFunctions X).val.obj (op (j ''ᵁ V))) :=
      ((rationalFunctions X).val.obj (op (j ''ᵁ V))).isModule
    apply Subtype.ext
    have hs := (rationalValue X (j ''ᵁ V)).map_smul ((j.appIso V).inv a) s.val
    refine (congrArg (Scheme.functionFieldMap j) hs).trans ?_
    change Scheme.functionFieldMap j
      (X.germToFunctionField (j ''ᵁ V) ((j.appIso V).inv a) * _) =
        U.germToFunctionField V a * _
    rw [map_mul, Scheme.FunctionField.map_germ_appIso_inv]
    rfl

/-- The original nonempty-open rational-value map is bijective. -/
theorem openSectionValueMap_bijective (D : Divisor X) (V : U.Opens) [Nonempty V] :
    Function.Bijective (openSectionValueMap j D V) := by
  constructor
  · intro s t h
    apply Subtype.ext
    apply (rationalValueEquiv X (j ''ᵁ V)).injective
    apply (Scheme.FunctionField.fieldEquiv j).injective
    exact congrArg Subtype.val h
  · intro t
    let e := Scheme.FunctionField.fieldEquiv j
    have ht : IsFractionalSection X D (j ''ᵁ V) (e.symm t.val) :=
      (isFractionalSection_openRestriction_iff j D V _).mp (by
        change IsFractionalSection U (openRestriction j D) V (e (e.symm t.val))
        rw [e.apply_symm_apply]
        exact t.property)
    let z : fractionalSections X D (j ''ᵁ V) := ⟨e.symm t.val, ht⟩
    refine ⟨(explicitSheafSectionsEquiv X D (j ''ᵁ V)).symm.toFun z, ?_⟩
    apply Subtype.ext
    change e ((explicitSheafSectionsEquiv X D (j ''ᵁ V)).toFun
      ((explicitSheafSectionsEquiv X D (j ''ᵁ V)).symm.toFun z)).val = t.val
    exact (congrArg (fun w : fractionalSections X D (j ''ᵁ V) => e w.val)
      ((explicitSheafSectionsEquiv X D (j ''ᵁ V)).apply_symm_apply z)).trans
        (e.apply_symm_apply t.val)

/-- The section equivalence on nonempty opens, with the original scalar action. -/
def nonemptyOpenSectionEquiv (D : Divisor X) (V : U.Opens) [Nonempty V] :
    Γ((Modules.restrictFunctor j).obj (divisorSheaf X D), V) ≃ₗ[Γ(U, V)]
      Γ((show U.Modules from divisorSheaf U (openRestriction j D)), V) :=
  (LinearEquiv.ofBijective (openSectionValueMap j D V)
    (openSectionValueMap_bijective j D V)).trans
      (explicitSheafSectionsEquiv U (openRestriction j D) V).symm

/-- The nonempty-open comparison is the original function-field map on values. -/
theorem nonemptyOpenSectionEquiv_value (D : Divisor X) (V : U.Opens) [Nonempty V]
    (s : Γ((Modules.restrictFunctor j).obj (divisorSheaf X D), V)) :
    (rationalValue U V).toFun (nonemptyOpenSectionEquiv j D V s).val =
      Scheme.functionFieldMap j ((rationalValue X (j ''ᵁ V)).toFun s.val) := by
  exact congrArg Subtype.val
    ((explicitSheafSectionsEquiv U (openRestriction j D) V).apply_symm_apply
      (openSectionValueMap j D V s))


/-- The original section equivalence on every open; empty opens use their
actual subsingleton modules rather than a function-field identification. -/
def openSectionEquiv (D : Divisor X) (V : U.Opens) :
    Γ((Modules.restrictFunctor j).obj (divisorSheaf X D), V) ≃ₗ[Γ(U, V)]
      Γ((show U.Modules from divisorSheaf U (openRestriction j D)), V) := by
  classical
  by_cases hV : Nonempty V
  · let := hV
    exact nonemptyOpenSectionEquiv j D V
  · have hV0 : V = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hV ⟨⟨x, hx⟩⟩).elim
      · simp
    subst V
    have hi : j ''ᵁ (⊥ : U.Opens) = ⊥ := by ext x; simp
    let : Subsingleton
        (Γ((Modules.restrictFunctor j).obj (divisorSheaf X D), ⊥)) := by
      change Subsingleton ((divisorSheaf X D).val.obj (op (j ''ᵁ ⊥)))
      rw [hi]
      exact divisorSheaf_empty_subsingleton X D
    let : Subsingleton Γ((show U.Modules from divisorSheaf U (openRestriction j D)), ⊥) :=
      divisorSheaf_empty_subsingleton U (openRestriction j D)
    exact LinearEquiv.ofSubsingleton _ _

/-- The all-open equivalence retains the actual rational-value formula. -/
theorem openSectionEquiv_value (D : Divisor X) (V : U.Opens) [hV : Nonempty V]
    (s : Γ((Modules.restrictFunctor j).obj (divisorSheaf X D), V)) :
    (rationalValue U V).toFun (openSectionEquiv j D V s).val =
      Scheme.functionFieldMap j ((rationalValue X (j ''ᵁ V)).toFun s.val) := by
  simpa only [openSectionEquiv, dite_eq_left hV] using
    nonemptyOpenSectionEquiv_value j D V s

/-- Original section restriction commutes with the constructed open comparison. -/
theorem openSectionEquiv_naturality (D : Divisor X) {V W : U.Opens} (i : V ⟶ W)
    (s : Γ((Modules.restrictFunctor j).obj (divisorSheaf X D), W)) :
    (divisorSheaf U (openRestriction j D)).val.map i.op (openSectionEquiv j D W s) =
      openSectionEquiv j D V
        (((Modules.restrictFunctor j).obj (divisorSheaf X D)).val.map i.op s) := by
  classical
  by_cases hV : Nonempty V
  · let := hV
    let : Nonempty W := ⟨⟨hV.some.val, i.le hV.some.property⟩⟩
    apply Subtype.ext
    apply (rationalValueEquiv U V).injective
    change (rationalValue U V).toFun ((rationalFunctions U).val.map i.op
      (openSectionEquiv j D W s).val) = _
    exact (rationalValue_restrict U i (openSectionEquiv j D W s).val).trans
      ((openSectionEquiv_value j D W s).trans
        ((congrArg (Scheme.functionFieldMap j)
          (rationalValue_restrict X (j.opensFunctor.map i) s.val)).symm.trans
          (openSectionEquiv_value j D V
            (((Modules.restrictFunctor j).obj (divisorSheaf X D)).val.map i.op s)).symm))
  · have hV0 : V = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hV ⟨⟨x, hx⟩⟩).elim
      · simp
    subst V
    exact @Subsingleton.elim
      (Γ((show U.Modules from divisorSheaf U (openRestriction j D)), ⊥))
      (divisorSheaf_empty_subsingleton U (openRestriction j D)) _ _

/-- The actual restriction of the divisor module is the module of the
restricted original divisor. -/
def divisorSheafOpenRestrictionIso (D : Divisor X) :
    (Modules.restrictFunctor j).obj (divisorSheaf X D) ≅
      divisorSheaf U (openRestriction j D) :=
  (SheafOfModules.fullyFaithfulForget U.ringCatSheaf).preimageIso <|
    PresheafOfModules.isoMk
      (fun V => (openSectionEquiv j D V.unop).toModuleIso)
      (by
        intro V W i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact (openSectionEquiv_naturality j D i.unop s).symm)

/-- The original module pullback of a divisor sheaf along an open immersion
is the divisor sheaf of its original divisor restriction. -/
def divisorSheafOpenPullbackIso (D : Divisor X) :
    (Modules.pullback j).obj (divisorSheaf X D) ≅
      divisorSheaf U (openRestriction j D) :=
  (Modules.restrictFunctorIsoPullback j).symm.app (divisorSheaf X D) ≪≫
    divisorSheafOpenRestrictionIso j D


/-- The assembled restriction isomorphism retains the original rational-value map. -/
theorem divisorSheafOpenRestrictionIso_value (D : Divisor X) (V : U.Opens)
    [Nonempty V]
    (s : Γ((Modules.restrictFunctor j).obj (divisorSheaf X D), V)) :
    (rationalValue U V).toFun
      (((divisorSheafOpenRestrictionIso j D).hom.val.app (op V)) s).val =
      Scheme.functionFieldMap j ((rationalValue X (j ''ᵁ V)).toFun s.val) := by
  change (rationalValue U V).toFun (openSectionEquiv j D V s).val = _
  exact openSectionEquiv_value j D V s

/-- Under the original pullback adjunction, the pullback comparison is the
same arrow as the constructed restriction comparison under its original
restriction adjunction. This pins down the actual map, not just its objects. -/
theorem divisorSheafOpenPullbackIso_adjoint (D : Divisor X) :
    (Modules.pullbackPushforwardAdjunction j).homEquiv _ _
      (divisorSheafOpenPullbackIso j D).hom =
    (Modules.restrictAdjunction j).homEquiv _ _
      (divisorSheafOpenRestrictionIso j D).hom := by
  have hcomp (M : X.Modules) (N : U.Modules)
      (f : (Modules.restrictFunctor j).obj M ⟶ N) :
      (Modules.pullbackPushforwardAdjunction j).homEquiv M N
        ((Modules.restrictFunctorIsoPullback j).inv.app M ≫ f) =
      (Modules.restrictAdjunction j).homEquiv M N f := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app
      (Modules.restrictAdjunction j) (Modules.pullbackPushforwardAdjunction j) M
    change (Modules.restrictAdjunction j).unit.app M ≫
      (Modules.pushforward j).map ((Modules.restrictFunctorIsoPullback j).hom.app M) =
      (Modules.pullbackPushforwardAdjunction j).unit.app M at h
    have hi : (Modules.pullbackPushforwardAdjunction j).unit.app M ≫
        (Modules.pushforward j).map ((Modules.restrictFunctorIsoPullback j).inv.app M) =
        (Modules.restrictAdjunction j).unit.app M := by
      rw [← h, Category.assoc, ← Functor.map_comp]
      rw [Iso.hom_inv_id_app]
      rw [(Modules.pushforward j).map_id ((Modules.restrictFunctor j).obj M)]
      exact Category.comp_id _
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_comp, ← Category.assoc, hi]
  exact hcomp (divisorSheaf X D) (divisorSheaf U (openRestriction j D))
    (divisorSheafOpenRestrictionIso j D).hom

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
