/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.GenericFrame
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.CartierRegularity
public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum.GenericEmbedding
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteType
public import Aglib.RingTheory.FractionalIdeal.FiniteEmbeddedModule

/-!
# The original canonical stalk inside the original function field

The ONE chosen frame of the own canonical generic stalk supplies the actual
stalk embedding. Finiteness comes from the original finite presentation and
local-spectrum sections; torsion-freeness comes from proved canonical scalar
regularity. The native fractional image and numerator retain their original
denominator equation. No singular Gorenstein or rank-one premise is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

section Finite

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
  {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- The own canonical stalk is finite, via its actual local-spectrum pullback.
No extra normality, integrality, dimension or local-base premise is needed. -/
theorem normalSurfaceCanonicalStalk_finite (x : X) :
    Module.Finite (X.presheaf.stalk x)
      ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) := by
  let W := normalSurfaceCanonicalModule R ι i n
  let : W.IsFinitePresentation := normalSurfaceHomology_finitePresentation R ι i n e n
  let N := (pullback (X.fromSpecStalk x)).obj W
  let : Module.Finite (X.presheaf.stalk x) (moduleSpecΓFunctor.obj N) :=
    finite_globalSections_of_finitePresentation (X.presheaf.stalk x) N
  let α := (stalkFromSpecStalkSectionsIso X x W).toLinearEquiv
  exact Module.Finite.of_surjective α.symm.toLinearMap α.symm.surjective

end Finite

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  [IsDominant (i ≫ toSpec R ι)]
  (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι i).Finite)

include hX hXdim e hfin in
/-- Proved canonical scalar regularity packages torsion-freeness of the OWN stalk. -/
theorem normalSurfaceCanonicalStalk_isTorsionFree (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x)
      ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) where
  isSMulRegular b hb := normalSurfaceCanonical_stalk_regular
    R ι i hX hXdim n e hfin x b (isRegular_iff_ne_zero.mp hb)

/-- The actual own canonical stalk maps into the ORIGINAL function field,
using the same chosen generic frame at every point. -/
def normalSurfaceCanonicalStalkEmbedding (x : X) :
    ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) →ₗ[X.presheaf.stalk x]
      X.functionField :=
  stalkToFunctionField X x (normalSurfaceCanonicalModule R ι i n)
    (normalSurfaceCanonicalGenericFrame R ι i hX hXdim n e hfin)

/-- Original neighbourhood germs retain their values in that single original frame. -/
theorem normalSurfaceCanonicalStalkEmbedding_germ (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(normalSurfaceCanonicalModule R ι i n, U)) :
    normalSurfaceCanonicalStalkEmbedding R ι i hX hXdim n e hfin x
      ((normalSurfaceCanonicalModule R ι i n).presheaf.germ U x hx s) =
      normalSurfaceCanonicalGenericFrame R ι i hX hXdim n e hfin
        ((normalSurfaceCanonicalModule R ι i n).presheaf.germ U (genericPoint X)
          ((genericPoint_specializes x).mem_open U.isOpen hx) s) :=
  stalkToFunctionField_germ X x (normalSurfaceCanonicalModule R ι i n)
    (normalSurfaceCanonicalGenericFrame R ι i hX hXdim n e hfin) U hx s

/-- Injectivity is derived from genuine quasicoherence and canonical torsion-freeness. -/
theorem normalSurfaceCanonicalStalkEmbedding_injective (x : X) :
    Function.Injective (normalSurfaceCanonicalStalkEmbedding R ι i hX hXdim n e hfin x) := by
  let W := normalSurfaceCanonicalModule R ι i n
  let : W.IsFinitePresentation := normalSurfaceHomology_finitePresentation R ι i n e n
  let : Module.IsTorsionFree (X.presheaf.stalk x) ((moduleStalk X x).obj W) :=
    normalSurfaceCanonicalStalk_isTorsionFree R ι i hX hXdim n e hfin x
  exact stalkToFunctionField_injective X x W
    (normalSurfaceCanonicalGenericFrame R ι i hX hXdim n e hfin)

include e hfin in
/-- Full support makes the own canonical stalk nontrivial, including at singular points. -/
theorem normalSurfaceCanonicalStalk_nontrivial (x : X) :
    Nontrivial ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) := by
  have hx : x ∈ support (normalSurfaceCanonicalModule R ι i n) := by
    rw [normalSurfaceCanonicalModule_support R ι i n e hfin]
    trivial
  apply not_subsingleton_iff_nontrivial.mp
  intro h
  exact hx (AddCommGrpCat.isZero_iff_subsingleton.mpr h)

/-- The native fractional image of that same original finite embedding. -/
def normalSurfaceCanonicalStalkFractionalImage (x : X) :
    FractionalIdeal (X.presheaf.stalk x)⁰ X.functionField := by
  let : Module.Finite (X.presheaf.stalk x)
      ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) :=
    normalSurfaceCanonicalStalk_finite R ι i n e x
  exact FractionalIdeal.finiteEmbeddedImage
    (normalSurfaceCanonicalStalkEmbedding R ι i hX hXdim n e hfin x)

/-- The native numerator equivalence; no new ideal or denominator construction. -/
def normalSurfaceCanonicalStalkEquivNum (x : X) :
    ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) ≃ₗ[X.presheaf.stalk x]
      (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).num := by
  let : Module.Finite (X.presheaf.stalk x)
      ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) :=
    normalSurfaceCanonicalStalk_finite R ι i n e x
  exact FractionalIdeal.finiteEmbeddedModuleEquivNum
    (normalSurfaceCanonicalStalkEmbedding R ι i hX hXdim n e hfin x)
    (normalSurfaceCanonicalStalkEmbedding_injective R ι i hX hXdim n e hfin x)

/-- The exact original denominator scales the SAME canonical field value. -/
theorem normalSurfaceCanonicalStalkEquivNum_algebraMap (x : X)
    (m : (moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) :
    algebraMap (X.presheaf.stalk x) X.functionField
      (normalSurfaceCanonicalStalkEquivNum R ι i hX hXdim n e hfin x m :
        X.presheaf.stalk x) =
      (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).den •
        normalSurfaceCanonicalStalkEmbedding R ι i hX hXdim n e hfin x m := by
  let : Module.Finite (X.presheaf.stalk x)
      ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) :=
    normalSurfaceCanonicalStalk_finite R ι i n e x
  exact FractionalIdeal.algebraMap_finiteEmbeddedModuleEquivNum
    (normalSurfaceCanonicalStalkEmbedding R ι i hX hXdim n e hfin x)
    (normalSurfaceCanonicalStalkEmbedding_injective R ι i hX hXdim n e hfin x) m

/-- The same scaling equation on every original neighbourhood germ. -/
theorem normalSurfaceCanonicalStalkEquivNum_germ (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(normalSurfaceCanonicalModule R ι i n, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField
      (normalSurfaceCanonicalStalkEquivNum R ι i hX hXdim n e hfin x
        ((normalSurfaceCanonicalModule R ι i n).presheaf.germ U x hx s) :
          X.presheaf.stalk x) =
      (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).den •
        normalSurfaceCanonicalGenericFrame R ι i hX hXdim n e hfin
          ((normalSurfaceCanonicalModule R ι i n).presheaf.germ U (genericPoint X)
            ((genericPoint_specializes x).mem_open U.isOpen hx) s) := by
  exact (normalSurfaceCanonicalStalkEquivNum_algebraMap R ι i hX hXdim n e hfin x
    ((normalSurfaceCanonicalModule R ι i n).presheaf.germ U x hx s)).trans
      (congrArg (fun z : X.functionField =>
        (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).den • z)
        (normalSurfaceCanonicalStalkEmbedding_germ R ι i hX hXdim n e hfin x U hx s))

/-- Full support and the proved injection give a nonzero native numerator. -/
theorem normalSurfaceCanonicalStalkFractionalImage_num_ne_bot (x : X) :
    (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).num ≠ ⊥ := by
  let : Module.Finite (X.presheaf.stalk x)
      ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) :=
    normalSurfaceCanonicalStalk_finite R ι i n e x
  let : Nontrivial ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) :=
    normalSurfaceCanonicalStalk_nontrivial R ι i n e hfin x
  exact FractionalIdeal.finiteEmbeddedImage_num_ne_bot
    (normalSurfaceCanonicalStalkEmbedding R ι i hX hXdim n e hfin x)
    (normalSurfaceCanonicalStalkEmbedding_injective R ι i hX hXdim n e hfin x)

end AlgebraicGeometry.Scheme.Cohomology
