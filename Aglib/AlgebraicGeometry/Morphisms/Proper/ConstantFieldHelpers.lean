/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections

/-!
# Finite-H0 helpers for the actual structural constants map

Only broader finite-H0 helpers. Final proper geometrically integral constants theorem138+ is an
existing native theorem; do not duplicate it or add properness to the source helpers that lack it.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Proper.ConstantField`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0dbcec2d9d3efdbecf34d9977712b0d636ed4f90647ad6eda3effc99083181d3`. Selected lines: [[58, 137]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme
universe u
attribute [local instance] globalSectionsModule
variable {F : Type u} [Field F]

/-- The F-linear version of the existing structural constants ring homomorphism. -/
def constantsLinearMap (X : FScheme F) : F →ₗ[F] Γ(X.left, ⊤) where
  toFun := constants X
  map_add' := (constants X).map_add
  map_smul' a b := (constants X).map_mul a b

@[simp] theorem constantsLinearMap_apply (X : FScheme F) (a : F) :
    constantsLinearMap X a = constants X a := rfl

/-- Integral schemes have nontrivial global sections, so the actual constants map is injective. -/
theorem constants_injective (X : FScheme F) [IsIntegral X.left] :
    Function.Injective (constants X) := RingHom.injective _

/-- Over an algebraically closed field, finite actual H⁰ and integrality force every global
function to be a structural constant. No properness or constants theorem is assumed. -/
theorem constants_bijective_of_isAlgClosed_of_finite_h0 [IsAlgClosed F]
    (X : FScheme F) [IsIntegral X.left]
    (hfinite : Module.Finite F (structureCohomology F X 0)) :
    Function.Bijective (constants X) := by
  let := hfinite
  let : Algebra F Γ(X.left, ⊤) := (constants X).toAlgebra
  let : Module.Finite F Γ(X.left, ⊤) :=
    Module.Finite.of_surjective (structureH0Equiv X).toLinearMap (structureH0Equiv X).surjective
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The finite-H⁰ algebraically closed slice has actual coherent H⁰ dimension one. -/
theorem h0_finrank_eq_one_of_isAlgClosed_of_finite_h0 [IsAlgClosed F]
    (X : FScheme F) [IsIntegral X.left]
    (hfinite : Module.Finite F (structureCohomology F X 0)) :
    Module.finrank F (structureCohomology F X 0) = 1 := by
  let e := LinearEquiv.ofBijective (constantsLinearMap X)
    (constants_bijective_of_isAlgClosed_of_finite_h0 X hfinite)
  calc
    Module.finrank F (structureCohomology F X 0) = Module.finrank F Γ(X.left, ⊤) :=
      (structureH0Equiv X).finrank_eq
    _ = Module.finrank F F := e.finrank_eq.symm
    _ = 1 := Module.finrank_self F

/-- Actual coherent H⁰ dimension one is sufficient for constants bijectivity on an integral
field scheme. The positive dimension supplies finite dimensionality. -/
theorem constants_bijective_of_h0_finrank_eq_one
    (X : FScheme F) [IsIntegral X.left]
    (hdim : Module.finrank F (structureCohomology F X 0) = 1) :
    Function.Bijective (constants X) := by
  have hdim' : Module.finrank F Γ(X.left, ⊤) = 1 :=
    (structureH0Equiv X).finrank_eq.symm.trans hdim
  let : Module.Finite F Γ(X.left, ⊤) := Module.finite_of_finrank_eq_succ hdim'
  refine ⟨constants_injective X, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdim'.symm) (f := constantsLinearMap X)).mp (constants_injective X)

/-- Descend constants along the exact existing geometric H⁰ tensor comparison. The only
cohomology premises are finite H⁰ over the algebraically closed extension and bijectivity
of that constructed map in degree zero, not the full proper-constants conclusion. -/
theorem constants_bijective_of_geometric_h0
    (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K]
    (X : FScheme F) (hgeom : GeometricallyIntegral X.hom)
    (hfinite : Module.Finite K (structureCohomology K (fieldBaseChange K X) 0))
    (hbase : Function.Bijective (structureCohomologyBaseChangeMap K X 0)) :
    Function.Bijective (constants X) := by
  let := hgeom
  let : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  let : GeometricallyIntegral (fieldBaseChange K X).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap F K)))))
  let : IsIntegral (fieldBaseChange K X).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (fieldBaseChange K X).hom
  let e := LinearEquiv.ofBijective (structureCohomologyBaseChangeMap K X 0) hbase
  have hdim : Module.finrank F (structureCohomology F X 0) = 1 := by
    calc
      Module.finrank F (structureCohomology F X 0) =
          Module.finrank K (K ⊗[F] structureCohomology F X 0) :=
        (Module.finrank_baseChange (R := K) (S := F)).symm
      _ = Module.finrank K (structureCohomology K (fieldBaseChange K X) 0) := e.finrank_eq
      _ = 1 := h0_finrank_eq_one_of_isAlgClosed_of_finite_h0 (fieldBaseChange K X) hfinite
  exact constants_bijective_of_h0_finrank_eq_one X hdim

end AlgebraicGeometry.Scheme
