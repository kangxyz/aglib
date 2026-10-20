/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GenericExtension
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic

/-!
# Generic field maps extend on the same normal proper curve

Source: ordinary R5 Curves.GenericExtension, lines 111–195 and 271–346.
The exact extension family is supplied from native smooth-stalk dimension
and the proved proper valuation-stalk extension, over every field.
Field maps, structure maps and common-chart arrows are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FunctionField
namespace AlgebraicGeometry.Scheme.FunctionField.GenericExtension

/-- Retained general normal-curve extension theorem, a precise corollary of
Stacks 0BXZ. The generic-morphism/rational-map correspondence uses spreading out
over the field, since the proper target is finitely presented. No Tate curve,
group structure, pointedness, degree, or prescribed power morphism is present. -/
def NormalProperCurveGenericExtension : Prop :=
  ∀ (k : Type u) [Field k] (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    (sx : X ⟶ Spec (.of k)) (sy : Y ⟶ Spec (.of k)),
    IsProper sx → SmoothOfRelativeDimension 1 sx → NormalStalks X → IsProper sy →
    ∀ (g : Spec X.functionField ⟶ Y),
      g ≫ sy = X.fromSpecStalk (genericPoint X) ≫ sx →
      ∃ f : X ⟶ Y, f ≫ sy = sx ∧ X.fromSpecStalk (genericPoint X) ≫ f = g

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (sx : X ⟶ Spec (.of k)) (sy : Y ⟶ Spec (.of k))
  (φ : Y.functionField →+* X.functionField)

def extend (H : NormalProperCurveGenericExtension.{u})
    (hx : IsProper sx) (hs : SmoothOfRelativeDimension 1 sx)
    (hn : NormalStalks X) (hy : IsProper sy)
    (hφ : φ.comp (functionFieldConstants _ sy) = functionFieldConstants _ sx) : X ⟶ Y :=
  (H k X Y sx sy hx hs hn hy (genericMap φ) (genericMap_over sx sy φ hφ)).choose

theorem extend_over (H : NormalProperCurveGenericExtension.{u})
    (hx : IsProper sx) (hs : SmoothOfRelativeDimension 1 sx)
    (hn : NormalStalks X) (hy : IsProper sy)
    (hφ : φ.comp (functionFieldConstants _ sy) = functionFieldConstants _ sx) :
    extend sx sy φ H hx hs hn hy hφ ≫ sy = sx :=
  (H k X Y sx sy hx hs hn hy (genericMap φ) (genericMap_over sx sy φ hφ)).choose_spec.1

theorem extend_generic (H : NormalProperCurveGenericExtension.{u})
    (hx : IsProper sx) (hs : SmoothOfRelativeDimension 1 sx)
    (hn : NormalStalks X) (hy : IsProper sy)
    (hφ : φ.comp (functionFieldConstants _ sy) = functionFieldConstants _ sx) :
    X.fromSpecStalk (genericPoint X) ≫ extend sx sy φ H hx hs hn hy hφ = genericMap φ :=
  (H k X Y sx sy hx hs hn hy (genericMap φ) (genericMap_over sx sy φ hφ)).choose_spec.2

theorem extend_genericPoint (H : NormalProperCurveGenericExtension.{u})
    (hx : IsProper sx) (hs : SmoothOfRelativeDimension 1 sx)
    (hn : NormalStalks X) (hy : IsProper sy)
    (hφ : φ.comp (functionFieldConstants _ sy) = functionFieldConstants _ sx) :
    extend sx sy φ H hx hs hn hy hφ (genericPoint X) = genericPoint Y := by
  let z := IsLocalRing.closedPoint X.functionField
  have he := congrArg (fun g : Spec X.functionField ⟶ Y => g z)
    (extend_generic sx sy φ H hx hs hn hy hφ)
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at he
  rw [he]
  change Y.fromSpecStalk (genericPoint Y) ((Spec.map (CommRingCat.ofHom φ)) z) = _
  have hz : (Spec.map (CommRingCat.ofHom φ)) z = IsLocalRing.closedPoint Y.functionField :=
    Subsingleton.elim _ _
  rw [hz, Scheme.fromSpecStalk_closedPoint]

theorem extend_dominant (H : NormalProperCurveGenericExtension.{u})
    (hx : IsProper sx) (hs : SmoothOfRelativeDimension 1 sx)
    (hn : NormalStalks X) (hy : IsProper sy)
    (hφ : φ.comp (functionFieldConstants _ sy) = functionFieldConstants _ sx) :
    IsDominant (extend sx sy φ H hx hs hn hy hφ) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure Y, ← extend_genericPoint sx sy φ H hx hs hn hy hφ]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint X, rfl⟩)

theorem extend_fieldMap (H : NormalProperCurveGenericExtension.{u})
    (hx : IsProper sx) (hs : SmoothOfRelativeDimension 1 sx)
    (hn : NormalStalks X) (hy : IsProper sy)
    (hφ : φ.comp (functionFieldConstants _ sy) = functionFieldConstants _ sx) :
    let := extend_dominant sx sy φ H hx hs hn hy hφ
    Scheme.functionFieldMap (extend sx sy φ H hx hs hn hy hφ) = φ := by
  let := extend_dominant sx sy φ H hx hs hn hy hφ
  let f := extend sx sy φ H hx hs hn hy hφ
  have hd : X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫
        Y.fromSpecStalk (genericPoint Y) := by
    change X.fromSpecStalk _ ≫ f =
      Spec.map (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) ≫
        Y.fromSpecStalk _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
  exact hd.symm.trans (extend_generic sx sy φ H hx hs hn hy hφ)

def extendOver (H : NormalProperCurveGenericExtension.{u})
    (hx : IsProper sx) (hs : SmoothOfRelativeDimension 1 sx)
    (hn : NormalStalks X) (hy : IsProper sy)
    (hφ : φ.comp (functionFieldConstants _ sy) = functionFieldConstants _ sx) :
    Over.mk sx ⟶ Over.mk sy :=
  Over.homMk (extend (X := X) (Y := Y) sx sy φ H hx hs hn hy hφ)
    (extend_over (X := X) (Y := Y) sx sy φ H hx hs hn hy hφ)

end AlgebraicGeometry.Scheme.FunctionField.GenericExtension


namespace AlgebraicGeometry.Scheme.FunctionField.GenericExtension

/-- Every actual stalk of a normal smooth curve is a valuation ring. -/
theorem normalSmoothCurve_stalk_valuationRing
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) (hs : SmoothOfRelativeDimension 1 sX)
    (hn : NormalStalks X) (x : X) : ValuationRing (X.presheaf.stalk x) := by
  let : SmoothOfRelativeDimension 1 sX := hs
  let : Smooth sX := SmoothOfRelativeDimension.smooth 1 sX
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsIntegrallyClosed (X.presheaf.stalk x) := (hn x).2
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr
    (Scheme.smoothOfRelativeDimension_stalk_dimension_le k X sX 1 x)
  have hnormal : IsIntegrallyClosed (X.presheaf.stalk x) ∧
      ∀ P : Ideal (X.presheaf.stalk x), P ≠ ⊥ → P.IsPrime →
        P = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    refine ⟨inferInstance, ?_⟩
    intro P hP hprime
    exact IsLocalRing.eq_maximalIdeal (hprime.isMaximal_of_ne_bot hP)
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (X.presheaf.stalk x)).out 4 2).mp hnormal

/-- The exact arbitrary-field normal proper curve extension family is proved
using actual valuation stalks, spreading out and gluing. -/
theorem normalProperCurveGenericExtension : NormalProperCurveGenericExtension.{u} := by
  intro k _ X Y _ _ sx sy _ hs hn hy g hg
  let : IsProper sy := hy
  let : ∀ x : X, ValuationRing (X.presheaf.stalk x) :=
    fun x => normalSmoothCurve_stalk_valuationRing sx hs hn x
  exact Scheme.exists_generic_extension sx sy g hg

end AlgebraicGeometry.Scheme.FunctionField.GenericExtension

namespace AlgebraicGeometry.Scheme.FunctionField.CommonChart
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FunctionField
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
variable {k : Type u} [Field k] {A X Y : Scheme.{u}}
  [IsIntegral A] [IsIntegral X] [IsIntegral Y]
  (sx : X ⟶ Spec (.of k)) (sy : Y ⟶ Spec (.of k))
  (jX : A ⟶ X) (jY : A ⟶ Y) [IsOpenImmersion jX] [IsOpenImmersion jY]

variable (H : NormalProperCurveGenericExtension.{u})
  (hx : IsProper sx) (hsx : SmoothOfRelativeDimension 1 sx) (hnx : NormalStalks X)
  (hy : IsProper sy) (hsy : SmoothOfRelativeDimension 1 sy) (hny : NormalStalks Y)
  (hc : jX ≫ sx = jY ≫ sy)

def chartExtension : X ⟶ Y :=
  extend sx sy (chartFieldEquiv jX jY).toRingHom H hx hsx hnx hy
    (chartFieldEquiv_constants sx sy jX jY hc)

theorem chartExtension_over : chartExtension sx sy jX jY H hx hsx hnx hy hc ≫ sy = sx :=
  extend_over _ _ _ _ _ _ _ _ _

theorem chartExtension_dominant : IsDominant (chartExtension sx sy jX jY H hx hsx hnx hy hc) :=
  extend_dominant _ _ _ _ _ _ _ _ _

theorem chartExtension_fieldMap :
    let := chartExtension_dominant sx sy jX jY H hx hsx hnx hy hc
    Scheme.functionFieldMap (chartExtension sx sy jX jY H hx hsx hnx hy hc) =
      (chartFieldEquiv jX jY).toRingHom :=
  extend_fieldMap _ _ _ _ _ _ _ _ _

theorem chartExtension_chart : jX ≫ chartExtension sx sy jX jY H hx hsx hnx hy hc = jY := by
  let f := chartExtension sx sy jX jY H hx hsx hnx hy hc
  let := hx
  let := hy
  let : IsDominant f := chartExtension_dominant sx sy jX jY H hx hsx hnx hy hc
  let : IsDominant jX := Scheme.isDominant_of_isOpenImmersion jX
  let : IsDominant jY := Scheme.isDominant_of_isOpenImmersion jY
  have hfield : Scheme.functionFieldMap (jX ≫ f) =
      Scheme.functionFieldMap jY := by
    rw [Scheme.functionFieldMap_comp,
      chartExtension_fieldMap sx sy jX jY H hx hsx hnx hy hc]
    ext a
    change fieldEquiv jX ((fieldEquiv jX).symm (fieldEquiv jY a)) = fieldEquiv jY a
    exact RingEquiv.apply_symm_apply _ _
  have hgeneric : A.fromSpecStalk (genericPoint A) ≫ (jX ≫ f) =
      A.fromSpecStalk (genericPoint A) ≫ jY := by
    rw [Scheme.fromSpecStalk_genericPoint_naturality (jX ≫ f),
      Scheme.fromSpecStalk_genericPoint_naturality jY, hfield]
  exact ext_of_isDominant_of_isSeparated sy
    (by rw [Category.assoc, chartExtension_over]; exact hc)
    (A.fromSpecStalk (genericPoint A)) hgeneric

def chartIso : Over.mk sx ≅ Over.mk sy where
  hom := Over.homMk (chartExtension (X := X) (Y := Y) sx sy jX jY H hx hsx hnx hy hc)
    (chartExtension_over sx sy jX jY H hx hsx hnx hy hc)
  inv := Over.homMk (chartExtension (X := Y) (Y := X) sy sx jY jX H hy hsy hny hx hc.symm)
    (chartExtension_over sy sx jY jX H hy hsy hny hx hc.symm)
  hom_inv_id := by
    apply Over.OverMorphism.ext
    change chartExtension sx sy jX jY H hx hsx hnx hy hc ≫
      chartExtension sy sx jY jX H hy hsy hny hx hc.symm = 𝟙 X
    let := hx
    let : IsDominant jX := Scheme.isDominant_of_isOpenImmersion jX
    refine ext_of_isDominant_of_isSeparated sx ?_ jX ?_
    · simp only [Category.assoc, chartExtension_over, Category.id_comp]
    · rw [← Category.assoc, chartExtension_chart, chartExtension_chart, Category.comp_id]
  inv_hom_id := by
    apply Over.OverMorphism.ext
    change chartExtension sy sx jY jX H hy hsy hny hx hc.symm ≫
      chartExtension sx sy jX jY H hx hsx hnx hy hc = 𝟙 Y
    let := hy
    let : IsDominant jY := Scheme.isDominant_of_isOpenImmersion jY
    refine ext_of_isDominant_of_isSeparated sy ?_ jY ?_
    · simp only [Category.assoc, chartExtension_over, Category.id_comp]
    · rw [← Category.assoc, chartExtension_chart, chartExtension_chart, Category.comp_id]


end AlgebraicGeometry.Scheme.FunctionField.CommonChart
