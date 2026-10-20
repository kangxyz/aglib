/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Aglib.AlgebraicGeometry.Group.Translation
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricDegree
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.SectionRigidity
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Deck maps and exact-order points in the actual group kernel

A deck map of the displayed finite-etale morphism is translation when
the source is geometrically connected. The corresponding actual kernel
point has the exact deck-automorphism order. The final cyclicity theorem
also retains positive degree and every algebraically closed field-valued fibre.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.Kernel.DeckTranslation`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`33acd4de918213b1df6ea400e2e24fe427c09a62920a493b838706a77be2a337`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open AlgebraicGeometry.Scheme.OverField (Base FScheme)
open AlgebraicGeometry.Scheme.Group.Translation
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers

namespace AlgebraicGeometry.Scheme.Group.Kernel.DeckTranslation

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {F : Type u} [Field F] {G E : Grp (FScheme F)} (p : G ⟶ E)

/-- Any actual deck morphism of a geometrically connected finite-etale group
cover is translation by its value at the origin. No translation, rigidity,
genus or group-homomorphism conclusion is supplied as an input. -/
theorem deck_eq_translation [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]
    (hG : GeometricallyConnected G.X.hom) (g : G.X ⟶ G.X)
    (hover : g ≫ p.hom.hom = p.hom.hom) :
    g = translation (η[G.X] ≫ g) := by
  let := hG
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.Scheme.Hom.eq_of_comp_eq_of_section
    p.hom.hom.left G.X.hom
    (η[G.X]).left (Over.w (η[G.X]))
  · have ht : translation (η[G.X] ≫ g) ≫ p.hom.hom = p.hom.hom := by
      simp only [translation, MonObj.mul_comp, Category.assoc, hover,
        IsMonHom.one_hom, Category.id_comp]
      exact one_mul _
    exact congrArg (fun f : G.X ⟶ E.X => f.left) (hover.trans ht.symm)
  · exact congrArg (fun f : 𝟙_ (FScheme F) ⟶ G.X => f.left)
      (origin_translation (η[G.X] ≫ g)).symm

/-- The actual kernel point cut out by the deck map's origin image. -/
def kernelPoint (g : G.X ⟶ G.X) (hover : g ≫ p.hom.hom = p.hom.hom) :
    𝟙_ (FScheme F) ⟶ (Scheme.Group.Kernel.group p).X :=
  (Scheme.Group.Kernel.square p).lift (η[G.X] ≫ g) (toUnit _) (by
    rw [Category.assoc, hover, IsMonHom.one_hom]
    simp only [toUnit_unit, Category.id_comp])

@[simp] theorem kernelPoint_inclusion (g : G.X ⟶ G.X)
    (hover : g ≫ p.hom.hom = p.hom.hom) :
    kernelPoint p g hover ≫ (Scheme.Group.Kernel.inclusion p).hom.hom = η[G.X] ≫ g :=
  (Scheme.Group.Kernel.square p).lift_fst _ _ _

/-- All-test-scheme injectivity of the actual kernel inclusion. -/
theorem inclusion_points_injective (T : FScheme F) :
    Function.Injective (fun a : T ⟶ (Scheme.Group.Kernel.group p).X =>
      a ≫ (Scheme.Group.Kernel.inclusion p).hom.hom) := by
  intro a b h
  apply (Scheme.Group.Kernel.square p).hom_ext h
  exact toUnit_unique _ _

/-- Exact order of the actual kernel point is the exact order of the ordinary
scheme deck automorphism. -/
theorem kernelPoint_order [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]
    (hG : GeometricallyConnected G.X.hom) (g : Aut G.X)
    (hover : g.hom ≫ p.hom.hom = p.hom.hom) :
    orderOf (kernelPoint p g.hom hover) = orderOf g := by
  rw [← orderOf_injective (IsMonHom.monoidHom (Scheme.Group.Kernel.inclusion p).hom.hom _)
    (inclusion_points_injective p _) (kernelPoint p g.hom hover)]
  change orderOf (kernelPoint p g.hom hover ≫ (Scheme.Group.Kernel.inclusion p).hom.hom) = _
  rw [kernelPoint_inclusion]
  rw [← orderOf_injective (translationHom (G := G)) translationHom_injective (η[G.X] ≫ g.hom)]
  have ht := deck_eq_translation p hG g.hom hover
  change orderOf (translation (η[G.X] ≫ g.hom)) = orderOf g
  rw [← ht]
  exact orderOf_injective (Aut.toEnd G.X) (fun a b h => Aut.ext h) g

/-- Every actual field extension is epimorphic as a morphism of schemes. -/
theorem fieldMap_epi (K : Type u) [Field K] (s : Spec (.of K) ⟶ Base F) : Epi s := by
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  exact Flat.epi_of_flat_of_surjective s

/-- Rational points inject into points over any actual field map. -/
def fieldPointsHom (A : Grp (FScheme F)) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Base F) :
    (𝟙_ (FScheme F) ⟶ A.X) →* (Over.mk s ⟶ A.X) where
  toFun a := toUnit (Over.mk s) ≫ a
  map_one' := MonObj.comp_one _
  map_mul' a b := MonObj.comp_mul _ a b

theorem fieldPointsHom_injective (A : Grp (FScheme F)) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Base F) : Function.Injective (fieldPointsHom A K s) := by
  let := fieldMap_epi K s
  intro a b h
  apply Over.OverMorphism.ext
  apply (cancel_epi s).mp
  exact congrArg (fun f : Over.mk s ⟶ A.X => f.left) h

/-- An ordinary actual deck generator of order n forces geometric cyclicity
of the constructed categorical kernel in every algebraically closed field.
Neither a cyclic coefficient nor a kernel marking is an input. -/
theorem cyclicCoefficient {n : ℕ} (hn : 0 < n)
    [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]
    (hG : GeometricallyConnected G.X.hom) (hd : HasGeometricDegree p.hom.hom n)
    (g : Aut G.X) (hover : g.hom ≫ p.hom.hom = p.hom.hom) (horder : orderOf g = n) :
    CyclicCoefficient (Scheme.Group.Kernel.group p) n where
  positive := hn
  finite := inferInstance
  etale := inferInstance
  geometric_cyclic K _ _ s := by
    have hc : Nat.card (Over.mk s ⟶ (Scheme.Group.Kernel.group p).X) = n :=
      (Nat.card_congr (Scheme.Group.Kernel.pointsEquiv p (Over.mk s))).trans (hd K s 1)
    let a := fieldPointsHom (Scheme.Group.Kernel.group p) K s (kernelPoint p g.hom hover)
    have ha : orderOf a = n := by
      dsimp only [a]
      rw [orderOf_injective _ (fieldPointsHom_injective _ K s),
        kernelPoint_order p hG g hover, horder]
    let : Finite (Over.mk s ⟶ (Scheme.Group.Kernel.group p).X) :=
      Nat.finite_of_card_ne_zero (hc.trans_ne (Nat.ne_of_gt hn))
    have hcyc := isCyclic_of_orderOf_eq_card a (ha.trans hc.symm)
    have eqv := (zmodCyclicMulEquiv hcyc).symm
    rw [hc] at eqv
    exact ⟨eqv⟩

end AlgebraicGeometry.Scheme.Group.Kernel.DeckTranslation
