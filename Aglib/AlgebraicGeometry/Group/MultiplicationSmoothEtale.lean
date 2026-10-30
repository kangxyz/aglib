/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Dimension
public import Aglib.AlgebraicGeometry.Group.MultiplicationCotangent
public import Aglib.AlgebraicGeometry.RationalPoint.Etale
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# Invertible multiplication on smooth commutative group schemes

The original differential of multiplication is the scalar `n` at the identity.
The smooth differential criterion gives an etale identity neighborhood;
translations and faithfully flat field descent give etaleness of the original
power morphism over any field. No properness, finiteness or degree premise is
used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- Over an algebraically closed field, invertible multiplication on any
smooth commutative group scheme is etale, including disconnected groups. -/
theorem multiplication_etale_of_smooth_of_isAlgClosed [IsAlgClosed k]
    (G : Grp (FScheme k)) [Smooth G.X.hom] [IsCommMonObj G.X]
    (n : ℕ) (hn : IsUnit (n : k)) : Etale ((𝟙 G.X) ^ n).left := by
  let d := Module.finrank k (Cotangent.Space η[G.X])
  let : SmoothOfRelativeDimension d G.X.hom :=
    smoothOfRelativeDimension_finrank_identityCotangent_of_isAlgClosed G.X
  have hc : Function.Surjective (multiplicationCotangent G n) := by
    rw [multiplicationCotangent_eq_scalar G d n]
    intro a
    refine ⟨(n : k)⁻¹ • a, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      mul_inv_cancel₀ hn.ne_zero, one_smul]
  obtain ⟨U, hu, he⟩ := Cotangent.exists_etale_neighborhood_of_surjective
    η[G.X] ((𝟙 G.X) ^ n) (multiplication_pointed G n) d hc
  let f : G ⟶ G := Grp.homMk' ((𝟙 G.toMon) ^ n)
  have hf : f.hom.hom = (𝟙 G.X) ^ n := by
    simp only [f, Grp.homMk', Mon.Hom.hom_pow, Mon.id_hom']
  have : Etale (U.ι ≫ f.hom.hom.left) := by rwa [hf]
  have h := Curve.etale_of_nonempty_etale_open G G f U
    ⟨⟨(Cotangent.pointData η[G.X]).point, hu⟩⟩
  rwa [hf] at h

-- Canonical pullback group objects are definitionally the field-scheme pullbacks used by descent.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over every field, multiplication by an invertible natural scalar on a
smooth commutative group scheme is etale. The conclusion uses the literal
original power morphism. -/
theorem multiplication_etale_of_smooth_of_isUnit
    (G : Grp (FScheme k)) [Smooth G.X.hom] [IsCommMonObj G.X]
    (n : ℕ) (hn : IsUnit (n : k)) : Etale ((𝟙 G.X) ^ n).left := by
  let f : G ⟶ G := Grp.homMk' ((𝟙 G.toMon) ^ n)
  have hf : f.hom.hom = (𝟙 G.X) ^ n := by
    simp only [f, Grp.homMk', Mon.Hom.hom_pow, Mon.id_hom']
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Base k := Spec.algebraMap k K
  let P := Over.pullback s
  let B := Scheme.Group.BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let f' := B.functor.map f
  let : GrpObj (P.obj G.X) := Functor.grpObjObj
  let : IsCommMonObj G'.X := inferInstanceAs (IsCommMonObj (P.obj G.X))
  let : Smooth G'.X.hom := MorphismProperty.pullback_snd G.X.hom s inferInstance
  have hSquare : IsPullback (pullback.fst G.X.hom s) f'.hom.hom.left
      f.hom.hom.left (pullback.fst G.X.hom s) := by
    apply IsPullback.flip
    apply IsPullback.of_right (h₁₂ := pullback.snd G.X.hom s)
      (h₂₂ := G.X.hom) (v₁₃ := s)
      _ (Scheme.Group.BaseChange.groupSchemeBaseChange_map_left_fst s f)
      (IsPullback.of_hasPullback G.X.hom s).flip
    simpa only [Scheme.Group.BaseChange.groupSchemeBaseChange_map_left_snd, Over.w] using
      (IsPullback.of_hasPullback G.X.hom s).flip
  have hpow : f'.hom.hom = (𝟙 G'.X) ^ n := by
    change P.map f.hom.hom = (𝟙 (P.obj G.X)) ^ n
    rw [hf]
    calc
      _ = (P.map (𝟙 G.X)) ^ n :=
        (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
      _ = _ := by rw [CategoryTheory.Functor.map_id]
  have hn' : IsUnit (n : K) := by
    simpa only [map_natCast] using hn.map (algebraMap k K)
  have he : Etale f'.hom.hom.left := by
    rw [hpow]
    exact multiplication_etale_of_smooth_of_isAlgClosed G' n hn'
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  have h := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hSquare.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ he
  rwa [hf] at h

end AlgebraicGeometry.Scheme.Group.Multiplication
