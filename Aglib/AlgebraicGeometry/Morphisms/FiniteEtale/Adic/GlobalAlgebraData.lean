/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.AlgebraStructure
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CompletionComparison

/-!
# The original algebra of a global finite-etale cover

The completion comparison of a given global cover carries its existing native
algebra structure. No newly chosen multiplication replaces it. The whole family
of reduction maps is the original family of geometric restriction projections.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped MonObj AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

open Modules Modules.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (K : X.IdealSheafData) (C : FiniteEtale X)

/-- The actual global cover algebra with its original completion comparison. -/
def globalAlgebraizationData :
    AdicAlgebraizationData (restrictionCoverSystem K C).adicSystem where
  coherent := globalStructureCoherent C
  beta := restrictionCompletionIso K C
  operations :=
    { mon := Modules.Algebra.pushforwardStructureSheafMonObj C.obj.hom
      comm := Modules.Algebra.pushforwardStructureSheafIsCommMonObj C.obj.hom
      map := by
        intro n
        rcases n with ⟨n⟩
        let : MonObj ((𝟭 X.Modules).obj (globalStructureCoherent C).obj) :=
          Modules.Algebra.pushforwardStructureSheafMonObj C.obj.hom
        change IsMonHom ((idealSheafQuotientUnit X (K ^ n)).app
          (globalStructureCoherent C).obj ≫
            (restrictionCompletionIso K C).hom.hom.app (op n))
        rw [unit_restrictionCompletionIso_hom, restrictionModuleUnit_app]
        exact Modules.Algebra.instIsMonHomStructurePullbackMap
          (p := C.obj.hom) (q := (restrictionCoverSystem K C).ambientMap n)
          (Limits.pullback.fst C.obj.hom (K ^ n).subschemeι) Limits.pullback.condition }

/-- The algebra is literally the native direct-image structure algebra. -/
theorem globalAlgebraizationData_algebra :
    (globalAlgebraizationData K C).algebra =
      Modules.Algebra.pushforwardStructureAlgebra C.obj.hom := rfl

/-- The complete original geometric restriction family is retained. -/
theorem globalAlgebraizationData_quotientMaps :
    (globalAlgebraizationData K C).quotientMaps = restrictionModuleUnit K C := by
  apply NatTrans.ext
  funext n
  rcases n with ⟨n⟩
  exact unit_restrictionCompletionIso_hom K C n

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
