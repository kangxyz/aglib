/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Translation.LocalProperty
public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Aglib.AlgebraicGeometry.Morphisms.Flat.Generic
public import Aglib.AlgebraicGeometry.Morphisms.Flat.Descent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Flatness of finite surjective group homomorphisms

Generic flatness and the actual translation cover prove flatness of a
surjective quasi-compact finite-type group homomorphism with geometrically
integral target over a field. The arbitrary-field statement descends the
same original map from the algebraic closure. Finite homomorphisms are then
finite locally free.

The multiplication consequence retains finiteness and surjectivity as
explicit inputs. It works in every characteristic, with no invertibility
or differential assumption. The separate ample-line-bundle argument must
supply those inputs for positive levels, and this file makes no rank claim.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- A surjective quasi-compact group homomorphism locally of finite type
over an algebraically closed field is flat when its target is integral.
The flat open is constructed by generic flatness of the structure module. -/
theorem hom_flat_of_surjective_of_isAlgClosed [IsAlgClosed k]
    (G H : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [IsIntegral H.X.left] (f : G ⟶ H)
    [LocallyOfFiniteType f.hom.hom.left] [QuasiCompact f.hom.hom.left]
    [Surjective f.hom.hom.left] : Flat f.hom.hom.left := by
  let : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  let : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  obtain ⟨W, hW, hflat⟩ := exists_nonempty_source_open_flat_of_isIntegral f.hom.hom.left
  exact Translation.property_of_nonempty_open @Flat G H f W hW hflat

-- The canonical group pullback projects to the original scheme fibre
-- product; its base-change dictionaries use those definitionally equal types.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original surjective quasi-compact finite-type group homomorphism
is flat over any field if its target is geometrically integral. No
smoothness or separability hypothesis is required. -/
theorem hom_flat_of_surjective
    (G H : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [GeometricallyIntegral H.X.hom] (f : G ⟶ H)
    [LocallyOfFiniteType f.hom.hom.left] [QuasiCompact f.hom.hom.left]
    [Surjective f.hom.hom.left] : Flat f.hom.hom.left := by
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.algebraMap k K
  let B := BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let H' := B.functor.obj H
  let f' := B.functor.map f
  let : LocallyOfFiniteType G'.X.hom :=
    MorphismProperty.pullback_snd G.X.hom s inferInstance
  let : LocallyOfFiniteType H'.X.hom :=
    MorphismProperty.pullback_snd H.X.hom s inferInstance
  let : GeometricallyIntegral H'.X.hom :=
    MorphismProperty.pullback_snd H.X.hom s inferInstance
  let : IsIntegral H'.X.left := GeometricallyIntegral.isIntegral_of_subsingleton H'.X.hom
  have hSquare : IsPullback (pullback.fst G.X.hom s) f'.hom.hom.left
      f.hom.hom.left (pullback.fst H.X.hom s) := by
    apply IsPullback.flip
    apply IsPullback.of_right (h₁₂ := pullback.snd H.X.hom s)
      (h₂₂ := H.X.hom) (v₁₃ := s)
      _ (BaseChange.groupSchemeBaseChange_map_left_fst s f)
      (IsPullback.of_hasPullback H.X.hom s).flip
    have hsnd : f'.hom.hom.left ≫ pullback.snd H.X.hom s = pullback.snd G.X.hom s :=
      BaseChange.groupSchemeBaseChange_map_left_snd s f
    rw [hsnd, Over.w]
    exact (IsPullback.of_hasPullback G.X.hom s).flip
  let : LocallyOfFiniteType f'.hom.hom.left :=
    MorphismProperty.of_isPullback hSquare inferInstance
  let : QuasiCompact f'.hom.hom.left :=
    MorphismProperty.of_isPullback hSquare inferInstance
  let : Surjective f'.hom.hom.left :=
    MorphismProperty.of_isPullback hSquare inferInstance
  have hflat := hom_flat_of_surjective_of_isAlgClosed G' H' f'
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Flat) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hSquare.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hflat

/-- A finite surjective homomorphism with geometrically integral target
over a field is flat on the original schemes. -/
theorem finite_surjective_hom_flat
    (G H : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [GeometricallyIntegral H.X.hom] (f : G ⟶ H)
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left] : Flat f.hom.hom.left :=
  hom_flat_of_surjective G H f

/-- Finite surjective homomorphisms to a geometrically integral group
scheme locally of finite type over a field are finite locally free. -/
theorem finite_surjective_hom_finiteLocallyFree
    (G H : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [GeometricallyIntegral H.X.hom] (f : G ⟶ H)
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left] :
    Hom.FiniteLocallyFree f.hom.hom.left := by
  let : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  let : Flat f.hom.hom.left := finite_surjective_hom_flat G H f
  exact Hom.finiteFlatPresentationLocallyFree _ _ f.hom.hom.left
    inferInstance inferInstance inferInstance

namespace Multiplication

/-- Finiteness and surjectivity of actual multiplication on a
geometrically integral commutative group imply flatness in every
characteristic. Positive-level finiteness is a separate supplier. -/
theorem multiplication_flat_of_finite_surjective
    (G : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom]
    [GeometricallyIntegral G.X.hom] [IsCommMonObj G.X]
    (n : ℕ) [IsFinite ((𝟙 G.X) ^ n).left] [Surjective ((𝟙 G.X) ^ n).left] :
    Flat ((𝟙 G.X) ^ n).left := by
  let f : G ⟶ G := Grp.homMk' ((𝟙 G.toMon) ^ n)
  have hf : f.hom.hom = (𝟙 G.X) ^ n := by
    simp only [f, Grp.homMk', Mon.Hom.hom_pow, Mon.id_hom']
  let : IsFinite f.hom.hom.left := by rw [hf]; infer_instance
  let : Surjective f.hom.hom.left := by rw [hf]; infer_instance
  have h := finite_surjective_hom_flat G G f
  rwa [hf] at h

end Multiplication

end AlgebraicGeometry.Scheme.Group
