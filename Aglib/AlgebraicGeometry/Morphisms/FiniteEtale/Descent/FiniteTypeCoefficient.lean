/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeBaseChangeLimit
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitObjects
public import Aglib.AlgebraicGeometry.Spec.CompletionSpecialization

/-!
# Descent of actual finite-etale covers to finite coefficient algebras

The descended cover lives on the native pullback over a finite-generated
subalgebra. Its comparison uses the original subalgebra inclusion, rather
than an unspecified isomorphism with a limit object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

open Algebra.FiniteTypeSubalgebraLimit

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [QuasiCompact p] [QuasiSeparated p]

/-- A cover of the original coefficient base change descends to a native
finite-generated subalgebra, with its original coefficient-map comparison. -/
theorem exists_cover_over_finiteTypeSubalgebra
    (Y : FiniteEtale (pullback p (Spec.algebraMap R A))) :
    ∃ s : Finset A, ∃ Yi : FiniteEtale (pullback (Spec.algebraMap R (stage R A s)) p),
      Nonempty ((baseChange (LocalRing.coefficientBaseChangeMap p
        (stage R A s).val)).obj Yi ≅ Y) := by
  let D := Scheme.FiniteTypeSubalgebraLimit.schemeDiagram R A p
  let c := Scheme.FiniteTypeSubalgebraLimit.schemeCone R A p
  let e : pullback p (Spec.algebraMap R A) ≅ c.pt :=
    pullbackSymmetry p (Spec.algebraMap R A)
  obtain ⟨s, Yi, ⟨d⟩⟩ := exists_cover_of_isLimit D c
    (Scheme.FiniteTypeSubalgebraLimit.schemeConeIsLimit R A p)
      ((baseChange e.inv).obj Y)
  have he : LocalRing.coefficientBaseChangeMap p (stage R A s.unop).val =
      e.hom ≫ c.π.app s := by
    apply pullback.hom_ext
    · exact (LocalRing.coefficientBaseChangeMap_fst p _).trans
        (Scheme.FiniteTypeSubalgebraLimit.projection_fst R A p s).symm
    · exact (LocalRing.coefficientBaseChangeMap_snd p _).trans
        (Scheme.FiniteTypeSubalgebraLimit.projection_snd R A p s).symm
  refine ⟨s.unop, Yi, ⟨?_⟩⟩
  rw [he]
  exact (baseChangeComp (c.π.app s) e.hom).app Yi ≪≫
    (baseChange e.hom).mapIso d ≪≫
      ((baseChangeComp e.inv e.hom).symm ≪≫
        eqToIso (congrArg baseChange e.hom_inv_id) ≪≫ baseChangeId _).app Y

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
