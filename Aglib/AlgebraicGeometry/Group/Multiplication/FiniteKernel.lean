/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Multiplication.FiniteFlat
public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel
public import Aglib.AlgebraicGeometry.Group.MultiplicationSurjective
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel

/-!
# Multiplication finiteness from the existing native kernel

The existing universal kernel marking identifies all nonempty point fibres
with kernel points. A finite native kernel therefore gives finite geometric
fibres. The actual pullback point-surjection descends finiteness of these
fibres over an arbitrary field, and properness gives a finite map.
Geometric integrality supplies surjectivity of the endomorphism, since it
fixes the identity; the general group flatness theorem then applies.

The positive-level ample argument is a separate consumer, which discharges
the finite-kernel hypothesis without assuming a degree or cardinality.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- A finite actual kernel marking gives finite rational point fibres of
the original group homomorphism. The proof uses its native torsor action. -/
theorem finite_setOf_comp_eq_of_finite_kernelMarking
    {A G H : Grp (Over (Spec (.of k)))} {f : G ⟶ H}
    (m : KernelMarking A G H f) [IsFinite A.X.hom]
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ H.X) :
    {p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X | p ≫ f.hom.hom = y}.Finite := by
  let : Finite (𝟙_ (Over (Spec (.of k))) ⟶ A.X) :=
    Scheme.Finite.finite_hom_over_field A.X.hom
  rcases Set.eq_empty_or_nonempty
      {p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X | p ≫ f.hom.hom = y} with h | ⟨p₀, hp₀⟩
  · rw [h]
    exact Set.finite_empty
  have hfinite : {p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X |
      p ≫ f.hom.hom = p₀ ≫ f.hom.hom}.Finite := by
    let : Finite {p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X |
        p ≫ f.hom.hom = p₀ ≫ f.hom.hom} :=
      Finite.of_equiv _ (m.toTorsorAction.fiberEquiv p₀)
    exact Set.toFinite _
  have hp₀' : p₀ ≫ f.hom.hom = y := hp₀
  rwa [hp₀'] at hfinite

/-- Finite native multiplication kernel gives finite rational point fibres. -/
theorem finite_setOf_pow_eq_of_finite_kernelGroup
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X] (n : ℕ)
    [IsFinite (MultiplicationKernel.kernelGroup G n).X.hom]
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : {p | p ^ n = y}.Finite := by
  simpa only [MultiplicationKernel.multiplicationHom_hom,
    MultiplicationKernel.point_multiplication] using
    finite_setOf_comp_eq_of_finite_kernelMarking
      (Kernel.marking (MultiplicationKernel.multiplicationHom G n)) y

-- The base-changed native group and kernel are the canonical fibre
-- products; their proper/finite dictionaries use those projected types.
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite native multiplication kernel on a proper commutative group
over any field makes the original multiplication morphism finite. The
actual pullback point-surjection descends its finite geometric fibres. -/
theorem multiplication_isFinite_of_finite_kernelGroup
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsProper G.X.hom] (n : ℕ)
    [IsFinite (MultiplicationKernel.kernelGroup G n).X.hom] :
    IsFinite ((𝟙 G.X) ^ n).left := by
  let f := MultiplicationKernel.multiplicationHom G n
  have hmap : f.hom.hom = (𝟙 G.X) ^ n := by
    simpa only [MultiplicationKernel.multiplication] using
      MultiplicationKernel.multiplicationHom_hom G n
  let A := MultiplicationKernel.kernelGroup G n
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.algebraMap k K
  let P := Over.pullback s
  let B := BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let A' := B.functor.obj A
  let f' := B.functor.map f
  let : GrpObj (P.obj G.X) := Functor.grpObjObj
  let : IsCommMonObj G'.X := inferInstanceAs (IsCommMonObj (P.obj G.X))
  let : IsProper G'.X.hom := MorphismProperty.pullback_snd G.X.hom s inferInstance
  let : IsFinite A'.X.hom := MorphismProperty.pullback_snd A.X.hom s inferInstance
  have hpow : f'.hom.hom = (𝟙 G'.X) ^ n := by
    change P.map f.hom.hom = (𝟙 (P.obj G.X)) ^ n
    rw [hmap]
    calc
      _ = (P.map (𝟙 G.X)) ^ n :=
        (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
      _ = _ := by rw [CategoryTheory.Functor.map_id]
  let m := BaseChange.kernelMarking s (Kernel.marking f)
  have hpoints (y : 𝟙_ (Over (Spec (.of K))) ⟶ G'.X) : {p | p ^ n = y}.Finite := by
    have h : {p : 𝟙_ (Over (Spec (.of K))) ⟶ G'.X | p ≫ f'.hom.hom = y}.Finite :=
      finite_setOf_comp_eq_of_finite_kernelMarking m y
    simpa only [hpow, MonObj.comp_pow, Category.comp_id] using h
  have hf' : IsFinite f'.hom.hom.left := by
    rw [hpow]
    exact multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed G'.X n hpoints
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  let : IsFinite f'.hom.hom.left := hf'
  let : IsProper f.hom.hom.left := by
    rw [hmap]
    exact multiplication_isProper G.X n
  have hSquare : IsPullback (pullback.fst G.X.hom s) f'.hom.hom.left
      f.hom.hom.left (pullback.fst G.X.hom s) := BaseChange.map_isPullback s f
  let : LocallyQuasiFinite f.hom.hom.left := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    obtain ⟨y', hy'⟩ := (pullback.fst G.X.hom s).surjective y
    have h := (f'.hom.hom.left.finite_preimage_singleton y').image
      (pullback.fst G.X.hom s)
    apply h.subset
    intro x hx
    have hxy : f.hom.hom.left x = (pullback.fst G.X.hom s) y' :=
      (show f.hom.hom.left x = y from hx).trans hy'.symm
    obtain ⟨z, hzx, hzy⟩ := Scheme.exists_preimage_of_isPullback hSquare x y' hxy
    exact ⟨z, hzy, hzx⟩
  have hf : IsFinite f.hom.hom.left := IsFinite.of_isProper_of_locallyQuasiFinite _
  simpa only [hmap] using hf

/-- A finite native multiplication kernel on a proper geometrically
integral commutative group gives finite, flat, surjective multiplication
over the original field. No cardinality or numerical rank is asserted. -/
theorem multiplication_finite_flat_surjective_of_finite_kernelGroup
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsProper G.X.hom] [GeometricallyIntegral G.X.hom]
    (n : ℕ) [IsFinite (MultiplicationKernel.kernelGroup G n).X.hom] :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Flat ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left := by
  let : IsIntegral G.X.left := GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let hf := multiplication_isFinite_of_finite_kernelGroup G n
  let hs : Surjective ((𝟙 G.X) ^ n).left :=
    Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq _
      ((𝟙 G.X) ^ n).left.isClosedMap.isClosed_range
      (multiplication_left_apply_unitPoint G.X n)
  exact ⟨hf, multiplication_flat_of_finite_surjective G n, hs⟩

end AlgebraicGeometry.Scheme.Group.Multiplication
