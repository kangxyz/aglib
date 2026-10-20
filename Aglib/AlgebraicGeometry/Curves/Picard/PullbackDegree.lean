/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Divisors.Pullback
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/

open AlgebraicGeometry.Scheme.Modules.Invertible
  (classOf pullbackClass)
open _root_.AlgebraicGeometry.Scheme.Modules
  (overUnitIso pullbackUnitIso)

/-!
# Actual divisor-sheaf pullback comparison

C2 finite-map functoriality, K2-018 `lem:k2018-geometric-exact-order`, frozen
basis `7f86e4a`. For an actual finite dominant map between integral Noetherian
schemes of dimension at most one with closed DVR stalks, the canonical map
`f* O(D) → O(f*D)` is constructed by applying the actual function-field map
to rational sections and taking the module-sheaf pullback adjoint. Its local
uniformizer-chart squares are proved on sections, and establish that it is
an isomorphism. Empty-open sections are handled separately.

The actual divisor/Picard equivalence commutes with this pullback. No
Picard-pullback comparison, tensor-pullback theorem, norm formula, numerical
degree formula, or standard theorem family is assumed here. Numerical degree
scaling is a separate consumer of this premise-free comparison and the
explicit norm/order boundary in `NormDegree`.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme.Modules.Invertible.RationalTrivialization
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.PullbackDegree
open DivisorClass RationalTrivialization
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f]

theorem preimage_nonempty (U : Y.Opens) [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U
  rw [AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant]
  exact generic_mem_open Y U

theorem fieldMap_germ_open (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (a : Γ(Y, U)) :
    Scheme.functionFieldMap f (Y.germToFunctionField U a) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) := by
  have he : Y.germToFunctionField U ≫ CommRingCat.ofHom (Scheme.functionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
    change Y.presheaf.germ U _ _ ≫ (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) = _
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]
  exact congrArg (fun h : Γ(Y, U) ⟶ X.functionField => h a) he

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
variable [IsFinite f]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable [∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]

theorem fieldMap_fractional (D : Divisor Y) (U : Y.Opens) {g : Y.functionField}
    (hg : IsFractionalSection Y D U g) :
    IsFractionalSection X (Divisors.Pullback.divisorPullback f D) (f ⁻¹ᵁ U)
      (Scheme.functionFieldMap f g) := by
  rcases hg with rfl | hg
  · exact Or.inl (map_zero _)
  by_cases h0 : g = 0
  · exact Or.inl (by rw [h0, map_zero])
  right
  intro x hx
  let g' := Units.mk0 g h0
  have ho := Divisors.Pullback.order_fieldMap f x g'
  change X.ord (Scheme.functionFieldMap f g) x.val =
    Divisors.Pullback.ramification f x * Y.ord g (AlgebraicGeometry.Scheme.closedPointMap f x).val
      at ho
  rw [ho, Divisors.Pullback.divisorPullback_apply, ← mul_add]
  exact mul_nonneg (Divisors.Pullback.ramification_nonneg f x) (hg _ hx)

/-- Pull back a divisor-sheaf section on a nonempty open by applying the actual function-field
map to its rational value. -/
def nonemptyPullbackSection (D : Divisor Y) (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (s : (divisorSheaf Y D).val.obj (op U)) :
    (divisorSheaf X (Divisors.Pullback.divisorPullback f D)).val.obj (op (f ⁻¹ᵁ U)) :=
  (explicitSheafSectionsEquiv X _ _).symm
    ⟨Scheme.functionFieldMap f (rationalValue Y U s.val),
      fieldMap_fractional f D U (explicitSheafSectionsEquiv Y D U s).property⟩

theorem nonemptyPullbackSection_value (D : Divisor Y) (U : Y.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : (divisorSheaf Y D).val.obj (op U)) :
    rationalValue X (f ⁻¹ᵁ U) (nonemptyPullbackSection f D U s).val =
      Scheme.functionFieldMap f (rationalValue Y U s.val) :=
  congrArg Subtype.val ((explicitSheafSectionsEquiv X _ _).apply_symm_apply _)

/-- The divisor-sheaf section pullback on every open, with the unique zero section on the
empty open. -/
def pullbackSection (D : Divisor Y) (U : Y.Opens) :
    (divisorSheaf Y D).val.obj (op U) →
      (divisorSheaf X (Divisors.Pullback.divisorPullback f D)).val.obj (op (f ⁻¹ᵁ U)) := by
  classical
  exact if hU : Nonempty U then letI := hU; letI := preimage_nonempty f U; nonemptyPullbackSection
    f D U else fun _ => 0

theorem pullbackSection_value (D : Divisor Y) (U : Y.Opens)
    [hU : Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : (divisorSheaf Y D).val.obj (op U)) :
    rationalValue X (f ⁻¹ᵁ U) (pullbackSection f D U s).val =
      Scheme.functionFieldMap f (rationalValue Y U s.val) := by
  simp only [pullbackSection, dite_eq_left hU]
  exact nonemptyPullbackSection_value f D U s

/-- The linear section map from the divisor sheaf to the pushforward of its
ramification-weighted pullback. -/
def pullbackSectionLinear (D : Divisor Y) (U : Y.Opens) :
    (divisorSheaf Y D).val.obj (op U) →ₗ[Γ(Y, U)]
      ((Scheme.Modules.pushforward f).obj (divisorSheaf X (Divisors.Pullback.divisorPullback f
        D))).val.obj (op U) where
  toFun := pullbackSection f D U
  map_add' s t := by
    by_cases hU : Nonempty U
    · let := hU
      let := preimage_nonempty f U
      apply Subtype.ext
      apply (rationalValueEquiv X (f ⁻¹ᵁ U)).injective
      change rationalValue X (f ⁻¹ᵁ U) _ = rationalValue X (f ⁻¹ᵁ U) (_ + _)
      rw [map_add, pullbackSection_value, pullbackSection_value, pullbackSection_value]
      change Scheme.functionFieldMap f (rationalValue Y U (s.val + t.val)) = _
      rw [map_add, map_add]
    · have h0 := eq_bot_of_not_nonempty Y U hU
      subst U
      exact (divisorSheaf_empty_subsingleton X _).elim _ _
  map_smul' a s := by
    by_cases hU : Nonempty U
    · let := hU
      let := preimage_nonempty f U
      apply Subtype.ext
      apply (rationalValueEquiv X (f ⁻¹ᵁ U)).injective
      change rationalValue X (f ⁻¹ᵁ U) (pullbackSection f D U (a • s)).val =
        rationalValue X (f ⁻¹ᵁ U) (f.app U a • (pullbackSection f D U s).val)
      rw [_root_.map_smul, pullbackSection_value, pullbackSection_value]
      change Scheme.functionFieldMap f (rationalValue Y U (a • s.val)) =
        X.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) * _
      rw [_root_.map_smul]
      change Scheme.functionFieldMap f (Y.germToFunctionField U a * _) = _
      rw [map_mul, fieldMap_germ_open]
    · have h0 := eq_bot_of_not_nonempty Y U hU
      subst U
      exact (divisorSheaf_empty_subsingleton X _).elim _ _

/-- The sheaf morphism assembled from the compatible rational-value pullbacks on all target
opens. -/
def divisorPushforwardMap (D : Divisor Y) :
    (show Y.Modules from divisorSheaf Y D) ⟶ (Scheme.Modules.pushforward f).obj
      (divisorSheaf X (Divisors.Pullback.divisorPullback f D)) where
  val := PresheafOfModulesOfCommRing.homMk (R := Y.presheaf)
    (fun U => ConcreteCategory.ofHom (C := ModuleCat Γ(Y, U.unop)) (pullbackSectionLinear f D
      U.unop)) (by
      intro U V i
      ext s
      apply Subtype.ext
      by_cases hV : Nonempty V.unop
      · let := hV
        let := preimage_nonempty f V.unop
        let : Nonempty U.unop := ⟨⟨hV.some.val, i.unop.le hV.some.property⟩⟩
        let := preimage_nonempty f U.unop
        apply (rationalValueEquiv X (f ⁻¹ᵁ V.unop)).injective
        change rationalValue X (f ⁻¹ᵁ V.unop)
          (pullbackSection f D V.unop ((divisorSheaf Y D).val.map i s)).val =
            rationalValue X (f ⁻¹ᵁ V.unop)
              ((rationalFunctions X).val.map ((Opens.map f.base).map i.unop).op (pullbackSection f
                D U.unop s).val)
        rw [pullbackSection_value, rationalValue_restrict, pullbackSection_value]
        congr 1
        exact rationalValue_restrict Y i.unop s.val
      · have h0 := eq_bot_of_not_nonempty Y V.unop hV
        have : Subsingleton ((rationalFunctions X).val.obj (op (f ⁻¹ᵁ V.unop))) := by
          rw [h0, Scheme.Hom.preimage_bot]
          exact rational_empty_subsingleton X
        exact this.elim _ _)

/-- Canonical map from actual module pullback to the ramification divisor sheaf. -/
def divisorPullbackMap (D : Divisor Y) :
    (Scheme.Modules.pullback f).obj (divisorSheaf Y D) ⟶
      divisorSheaf X (Divisors.Pullback.divisorPullback f D) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (divisorPushforwardMap f D)

/-- The sheaf trivialization on the actual open subscheme U induced by the specified rational
unit g. -/
def restrictedDivisorIso (S : Scheme.{u}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S]
    [∀ x : ClosedPoint S, IsDiscreteValuationRing (S.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim S ≤ 1) (D : Divisor S) (U : S.Opens) (g : S.functionFieldˣ)
    (hg : ∀ x : ClosedPoint S, x.val ∈ U → S.ord (g : S.functionField) x.val + D x = 0) :
    (show U.toScheme.Modules from SheafOfModules.unit U.toScheme.ringCatSheaf) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (divisorSheaf S D) :=
  (overUnitIso U).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso (divisorSheafLocalIso S hdim D U g hg) ≪≫
      (Scheme.Modules.overFunctorEquiv U).app (divisorSheaf S D)

theorem restrictedDivisorIso_value (S : Scheme.{u}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian
  S]
    [∀ x : ClosedPoint S, IsDiscreteValuationRing (S.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim S ≤ 1) (D : Divisor S) (U : S.Opens) (g : S.functionFieldˣ)
    (hg : ∀ x : ClosedPoint S, x.val ∈ U → S.ord (g : S.functionField) x.val + D x = 0)
    (V : U.toScheme.Opens) [Nonempty (U.ι ''ᵁ V)] (a : Γ(U.toScheme, V)) :
    rationalValue S (U.ι ''ᵁ V) (((restrictedDivisorIso S hdim D U g hg).hom.val.app (op V))
      a).val =
      (g : S.functionField) * S.germToFunctionField (U.ι ''ᵁ V) ((U.ι.appIso V).inv a) := by
  change rationalValue S (U.ι ''ᵁ V)
    (sectionTrivialization S hdim D (U.ι ''ᵁ V) g _ ((U.ι.appIso V).inv a)).val = _
  exact sectionTrivialization_value S hdim D (U.ι ''ᵁ V) g _ _

theorem pulled_local_order (D : Divisor Y) (U : Y.Opens) (g : Y.functionFieldˣ)
    (hg : ∀ y : ClosedPoint Y, y.val ∈ U → Y.ord (g : Y.functionField) y.val + D y = 0) :
    ∀ x : ClosedPoint X, x.val ∈ f ⁻¹ᵁ U →
      X.ord (Scheme.functionFieldUnitMap f g : X.functionField) x.val +
        Divisors.Pullback.divisorPullback f D x = 0 := by
  intro x hx
  rw [Divisors.Pullback.order_fieldMap, Divisors.Pullback.divisorPullback_apply, ← mul_add,
    hg (AlgebraicGeometry.Scheme.closedPointMap f x) hx, mul_zero]

theorem divisorPushforwardMap_local_square (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (D : Divisor Y) (U : Y.Opens) (g : Y.functionFieldˣ)
    (hg : ∀ y : ClosedPoint Y, y.val ∈ U → Y.ord (g : Y.functionField) y.val + D y = 0) :
    (restrictedDivisorIso Y hdimY D U g hg).hom ≫
        (Scheme.Modules.restrictFunctor U.ι).map (divisorPushforwardMap f D) ≫
        Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap f U (divisorSheaf X
          (Divisors.Pullback.divisorPullback f D)) =
      SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom ≫
        (Scheme.Modules.pushforward (f ∣_ U)).map
          (restrictedDivisorIso X hdimX (Divisors.Pullback.divisorPullback f D) (f ⁻¹ᵁ U)
            (Scheme.functionFieldUnitMap f g) (pulled_local_order f D U g
              hg)).hom := by
  apply Scheme.Modules.hom_ext
  intro V
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap_app]
  ext a
  apply Subtype.ext
  let A := (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)
  let B := f ⁻¹ᵁ (U.ι ''ᵁ V)
  let i : A ⟶ B := eqToHom (image_morphismRestrict_preimage f U V)
  by_cases hA : Nonempty A
  · let := hA
    let : Nonempty B := ⟨⟨hA.some.val, i.le hA.some.property⟩⟩
    let : Nonempty (U.ι ''ᵁ V) := ⟨⟨f hA.some.val, i.le hA.some.property⟩⟩
    apply (rationalValueEquiv X A).injective
    change rationalValue X A ((rationalFunctions X).val.map i.op
      (pullbackSection f D (U.ι ''ᵁ V)
        ((restrictedDivisorIso Y hdimY D U g hg).hom.val.app (op V) a)).val) =
      rationalValue X A
        ((restrictedDivisorIso X hdimX (Divisors.Pullback.divisorPullback f D) (f ⁻¹ᵁ U)
          (Scheme.functionFieldUnitMap f g) (pulled_local_order f D U g
            hg)).hom.val.app
            (op ((f ∣_ U) ⁻¹ᵁ V)) ((f ∣_ U).app V a)).val
    rw [rationalValue_restrict, pullbackSection_value, restrictedDivisorIso_value,
      restrictedDivisorIso_value, map_mul]
    congr 1
    rw [fieldMap_germ_open]
    have hu : (U.ι.appIso V).inv = 𝟙 _ :=
      congrArg Iso.inv (Scheme.Opens.ι_appIso U V)
    have hx : ((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ V)).inv = 𝟙 _ :=
      congrArg Iso.inv (Scheme.Opens.ι_appIso (f ⁻¹ᵁ U) ((f ∣_ U) ⁻¹ᵁ V))
    rw [hu, hx]
    change X.germToFunctionField B (f.app (U.ι ''ᵁ V) a) =
      X.germToFunctionField A ((f ∣_ U).app V a)
    rw [morphismRestrict_app]
    exact (germ_restrict X i (f.app (U.ι ''ᵁ V) a)).symm
  · have h0 := eq_bot_of_not_nonempty X A hA
    have : Subsingleton ((rationalFunctions X).val.obj (op A)) := by
      rw [h0]
      exact rational_empty_subsingleton X
    exact this.elim _ _
theorem divisorPullbackMap_isIso (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (D : Divisor Y) : IsIso (divisorPullbackMap f D) := by
  apply Scheme.Modules.Pullback.OpenRestriction.isIso_of_local_restrict
  intro x
  obtain ⟨U, hxU, g, hg⟩ := exists_local_principal_function Y D (f x)
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  let a := restrictedDivisorIso Y hdimY D U g hg
  let b := restrictedDivisorIso X hdimX (Divisors.Pullback.divisorPullback f D) (f ⁻¹ᵁ U)
    (Scheme.functionFieldUnitMap f g) (pulled_local_order f D U g hg)
  let φ := (Scheme.Modules.restrictFunctor U.ι).map (divisorPushforwardMap f D) ≫
    Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap f U (divisorSheaf X
      (Divisors.Pullback.divisorPullback f D))
  let ψ := ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).symm φ
  have hh : (Scheme.Modules.pullback (f ∣_ U)).map a.hom ≫ ψ = (pullbackUnitIso (f ∣_ U)).hom ≫
    b.hom := by
    apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right]
    have hu : (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
        (pullbackUnitIso (f ∣_ U)).hom =
          SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom :=
      SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
    rw [hu]
    exact divisorPushforwardMap_local_square f hdimX hdimY D U g hg
  let : IsIso ψ := IsIso.of_isIso_fac_left hh
  change IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (divisorPushforwardMap f
      D)))
  rw [Scheme.Modules.Pullback.OpenRestriction.restrictedAdjoint_eq]
  infer_instance

/-- Actual pullback of O(D) is the ramification-weighted divisor sheaf. -/
def divisorPullbackIso (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (D : Divisor Y) :
    (Scheme.Modules.pullback f).obj (divisorSheaf Y D) ≅
      divisorSheaf X (Divisors.Pullback.divisorPullback f D) :=
  letI := divisorPullbackMap_isIso f hdimX hdimY D
  asIso (divisorPullbackMap f D)

theorem pullbackClass_divisor (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (D : Divisor Y) :
    pullbackClass f (classOf Y (divisorLineBundle Y hdimY D)) =
      classOf X (divisorLineBundle X hdimX (Divisors.Pullback.divisorPullback f D)) :=
  Quotient.sound ⟨divisorPullbackIso f hdimX hdimY D⟩

theorem divisorPicardEquiv_pullback (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (a : Divisor Y ⧸ (principal Y).range) :
    pullbackClass f (divisorPicardEquiv Y hdimY a) =
      divisorPicardEquiv X hdimX (Divisors.Pullback.classPullback f a) := by
  induction a using Quotient.inductionOn with
  | h D => exact pullbackClass_divisor f hdimX hdimY D

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.PullbackDegree
