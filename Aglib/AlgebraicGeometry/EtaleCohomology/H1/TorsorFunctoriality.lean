/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorBaseChange

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorFunctoriality` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d0853a4a2a67b449baec7974bdaa570ef8aba0ccf50d08ee010823f81f687335`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology

/-!
# Functoriality of actual sheaf-torsor classes

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Coefficient change is the
constructed augmentation pushout, and scheme pullback has the actual
set-sheaf inverse-image carrier and coefficient-equivariant unit. Stacks03AJ
is used only for injectivity of the canonical extension-class map when
proving well-definedness and laws on actual isomorphism classes.
-/
noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u w w' w''
attribute [local instance] hasSheafifyLarge

section Coefficients
variable {X : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (h : Stacks03AJ.{u, w} X)
variable {L M N : AbelianSheaf.{u, u + 1} X}

/-- Covariant coefficient change uses the constructed geometric pushout. -/
def torsorClassCoefficient (q : L ⟶ M) : TorsorClass L → TorsorClass M :=
  Quotient.lift (fun P => Quotient.mk
      (Scheme.EtaleCohomology.Torsor.isomorphicSetoid M) (torsorPushout P q)) (by
    intro P Q he
    apply (h.bijective M).injective
    change torsorExtClass (torsorPushout P q) = torsorExtClass (torsorPushout Q q)
    rw [torsorExtClass_pushout, torsorExtClass_pushout, torsorExtClass_iso (Classical.choice he)])

@[simp] theorem torsorClassCoefficient_mk (q : L ⟶ M) (P : Torsor L) :
    torsorClassCoefficient h q (Quotient.mk _ P) = Quotient.mk _ (torsorPushout P q) := rfl

/-- The canonical Ext class intertwines actual coefficient pushout. -/
theorem torsorClassToH1_coefficient (q : L ⟶ M) (a : TorsorClass L) :
    torsorClassToH1 M (torsorClassCoefficient h q a) = coefficientMap q (torsorClassToH1 L a) := by
  refine Quotient.inductionOn a ?_
  exact fun P => torsorExtClass_pushout P q

/-- The proved contracted-sum group law makes geometric coefficient change additive. -/
def torsorClassCoefficientMap (q : L ⟶ M) :
    letI := torsorClassAddCommGroup h L
    letI := torsorClassAddCommGroup h M
    TorsorClass L →+ TorsorClass M := by
  letI := torsorClassAddCommGroup h L
  letI := torsorClassAddCommGroup h M
  exact {
    toFun := torsorClassCoefficient h q
    map_zero' := by
      apply (h.bijective M).injective
      rw [torsorClassToH1_coefficient]
      change coefficientMap q (torsorExtClass (trivialTorsor L)) = torsorExtClass (trivialTorsor M)
      rw [torsorExtClass_trivial, torsorExtClass_trivial, map_zero]
    map_add' a b := by
      apply (h.bijective M).injective
      change torsorClassToH1 M (torsorClassCoefficient h q (torsorClassSum h a b)) =
        torsorClassToH1 M (torsorClassSum h (torsorClassCoefficient h q a)
            (torsorClassCoefficient h q b))
      rw [torsorClassToH1_coefficient, torsorClassToH1_sum, torsorClassToH1_sum,
        torsorClassToH1_coefficient, torsorClassToH1_coefficient, map_add] }

@[simp] theorem torsorClassCoefficient_id (a : TorsorClass L) :
    torsorClassCoefficient h (𝟙 L) a = a := by
  apply (h.bijective L).injective
  rw [torsorClassToH1_coefficient, coefficientMap_id, AddMonoidHom.id_apply]

/-- Coefficient pushout composes in the covariant direction. -/
theorem torsorClassCoefficient_comp (q : L ⟶ M) (r : M ⟶ N) (a : TorsorClass L) :
    torsorClassCoefficient h (q ≫ r) a =
      torsorClassCoefficient h r (torsorClassCoefficient h q a) := by
  apply (h.bijective N).injective
  rw [torsorClassToH1_coefficient, torsorClassToH1_coefficient,
    torsorClassToH1_coefficient, coefficientMap_comp, AddMonoidHom.comp_apply]

end Coefficients

section Pullbacks
variable {X S : Scheme.{u}}
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
variable (hS : Stacks03AJ.{u, w'} S) (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X)

/-- Contravariant scheme pullback uses the actual set-sheaf inverse image of each torsor. -/
def torsorClassPullback : TorsorClass L → TorsorClass ((inverseImage f).obj L) :=
  Quotient.lift (fun P => Quotient.mk
      (Scheme.EtaleCohomology.Torsor.isomorphicSetoid ((inverseImage f).obj L))
      (torsorInverseImage f P)) (by
    intro P Q he
    apply (hS.bijective ((inverseImage f).obj L)).injective
    change torsorExtClass (torsorInverseImage f P) = torsorExtClass (torsorInverseImage f Q)
    rw [torsorExtClass_inverseImage, torsorExtClass_inverseImage,
      torsorExtClass_iso (Classical.choice he)])

@[simp] theorem torsorClassPullback_mk (P : Torsor L) :
    torsorClassPullback hS f L (Quotient.mk _ P) = Quotient.mk _ (torsorInverseImage f P) := rfl

/-- The actual scheme pullback square for the canonical torsor-to-Ext class. -/
theorem torsorClassToH1_pullback (a : TorsorClass L) :
    torsorClassToH1 ((inverseImage f).obj L) (torsorClassPullback hS f L a) =
      h1Pullback f L (torsorClassToH1 L a) := by
  refine Quotient.inductionOn a ?_
  exact fun P => torsorExtClass_inverseImage f P

/-- Actual torsor inverse image preserves the constructed contracted-sum group law. -/
def torsorClassPullbackMap (hX : Stacks03AJ.{u, w} X) :
    letI := torsorClassAddCommGroup hX L
    letI := torsorClassAddCommGroup hS ((inverseImage f).obj L)
    TorsorClass L →+ TorsorClass ((inverseImage f).obj L) := by
  letI := torsorClassAddCommGroup hX L
  letI := torsorClassAddCommGroup hS ((inverseImage f).obj L)
  exact {
    toFun := torsorClassPullback hS f L
    map_zero' := by
      apply (hS.bijective ((inverseImage f).obj L)).injective
      rw [torsorClassToH1_pullback]
      change h1Pullback f L (torsorExtClass (trivialTorsor L)) =
        torsorExtClass (trivialTorsor ((inverseImage f).obj L))
      rw [torsorExtClass_trivial, torsorExtClass_trivial, map_zero]
    map_add' a b := by
      apply (hS.bijective ((inverseImage f).obj L)).injective
      change torsorClassToH1 _ (torsorClassPullback hS f L (torsorClassSum hX a b)) =
        torsorClassToH1 _ (torsorClassSum hS (torsorClassPullback hS f L a)
            (torsorClassPullback hS f L b))
      rw [torsorClassToH1_pullback, torsorClassToH1_sum, torsorClassToH1_sum,
        torsorClassToH1_pullback, torsorClassToH1_pullback, map_add] }

/-- Coefficient pushout commutes with actual scheme inverse image. -/
theorem torsorClassPullback_coefficient (hX : Stacks03AJ.{u, w} X)
    {M : AbelianSheaf.{u, u + 1} X} (q : L ⟶ M) (a : TorsorClass L) :
    torsorClassPullback hS f M (torsorClassCoefficient hX q a) =
      torsorClassCoefficient hS ((inverseImage f).map q) (torsorClassPullback hS f L a) := by
  apply (hS.bijective ((inverseImage f).obj M)).injective
  rw [torsorClassToH1_pullback, torsorClassToH1_coefficient,
    torsorClassToH1_coefficient, torsorClassToH1_pullback, h1Pullback_coefficientMap]

end Pullbacks

section Coherence
variable {X S T : Scheme.{u}}
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
variable [HasExt.{w''} (AbelianSheaf.{u, u + 1} T)]

/-- Identity scheme pullback is identity after the actual coefficient coherence. -/
theorem torsorClassPullback_id (hX : Stacks03AJ.{u, w} X)
    (L : AbelianSheaf.{u, u + 1} X) (a : TorsorClass L) :
    torsorClassCoefficient hX ((inverseImageId X).hom.app L)
      (torsorClassPullback hX (𝟙 X) L a) = a := by
  apply (hX.bijective L).injective
  rw [torsorClassToH1_coefficient, torsorClassToH1_pullback]
  exact h1Pullback_id X L (torsorClassToH1 L a)

/-- Composition uses the proved, correctly oriented actual inverse-image isomorphism. -/
theorem torsorClassPullback_comp (hS : Stacks03AJ.{u, w'} S) (hT : Stacks03AJ.{u, w''} T)
    (f : S ⟶ X) (g : T ⟶ S) (L : AbelianSheaf.{u, u + 1} X) (a : TorsorClass L) :
    torsorClassCoefficient hT ((inverseImageComp f g).hom.app L)
      (torsorClassPullback hT (g ≫ f) L a) =
    torsorClassPullback hT g ((inverseImage f).obj L) (torsorClassPullback hS f L a) := by
  apply (hT.bijective ((inverseImage g).obj ((inverseImage f).obj L))).injective
  rw [torsorClassToH1_coefficient, torsorClassToH1_pullback,
    torsorClassToH1_pullback, torsorClassToH1_pullback]
  exact h1Pullback_comp f g L (torsorClassToH1 L a)

end Coherence
end AlgebraicGeometry.Scheme.EtaleCohomology
