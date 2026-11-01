/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Composition

/-! # Literal proper compactifications and composition unit towers

These towers retain identity ambient maps. Their intermediate compactifications
are still the actual open pullbacks, not replacements by isomorphic schemes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u
namespace AlgebraicGeometry.Scheme.Hom

namespace DenseCompactification

/-- A proper morphism has its literal compactification with identity open source. -/
def ofProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    DenseCompactification f where
  Xbar := X
  j := 𝟙 X
  p := f
  isOpenImmersion_j := inferInstance
  isProper_p := inferInstance
  fac := Category.id_comp f
  isSchemeTheoreticallyDominant_j := inferInstance

end DenseCompactification

namespace CompactifiedComposition

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The right unit tower retains the supplied compactification of the first map. -/
def rightUnit (C : DenseCompactification f) : CompactifiedComposition f (𝟙 Y) where
  targetCompactification := DenseCompactification.ofProper (𝟙 Y)
  sourceCompactification :=
    { Xbar := C.Xbar
      j := C.j
      p := C.p
      isOpenImmersion_j := inferInstance
      isProper_p := C.toCompactification.isProper_p
      fac := by
        change C.j ≫ C.p = f ≫ 𝟙 Y
        rw [Category.comp_id]
        exact C.fac
      isSchemeTheoreticallyDominant_j := inferInstance }

/-- The left unit tower uses the identity proper map on the supplied ambient. -/
def leftUnit (C : DenseCompactification f) : CompactifiedComposition (𝟙 X) f where
  targetCompactification := C
  sourceCompactification :=
    { Xbar := C.Xbar
      j := C.j
      p := 𝟙 C.Xbar
      isOpenImmersion_j := inferInstance
      isProper_p := inferInstance
      fac := by simp
      isSchemeTheoreticallyDominant_j := inferInstance }

end CompactifiedComposition
end AlgebraicGeometry.Scheme.Hom
