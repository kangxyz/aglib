/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Basic
public import Aglib.AlgebraicGeometry.Gluing.Coproduct

/-!
# Binary disjoint unions of compactifications

Both structure maps and the original source inclusions are the actual
coproduct maps. No density is asserted merely from an open immersion.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.Compactification

/-- Compactifications combine by actual binary coproducts over the same base. -/
def coprod {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (C : Compactification f) (D : Compactification g) :
    Compactification (Limits.coprod.desc f g) where
  Xbar := C.Xbar ⨿ D.Xbar
  j := Limits.coprod.map C.j D.j
  p := Limits.coprod.desc C.p D.p
  isOpenImmersion_j := inferInstance
  isProper_p := Scheme.OpenPushout.coprodDesc_proper_of_proper C.p D.p
  fac := by apply Limits.coprod.hom_ext <;> simp

/-- Image closure supplies density for the binary coproduct whenever its
original structural map is quasi-compact. -/
theorem exists_dominant_coprod {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (C : Compactification f) (D : Compactification g)
    [QuasiCompact (Limits.coprod.desc f g)] :
    ∃ E : Compactification (Limits.coprod.desc f g), IsDominant E.j := by
  let E := C.coprod D
  let : QuasiCompact (E.j ≫ E.p) := by rw [E.fac]; infer_instance
  have : QuasiCompact E.j := QuasiCompact.of_comp E.j E.p
  exact Scheme.Hom.exists_compactification_of_immersion _ E.j E.p E.fac

/-- The same image-closure construction retains schematic density. -/
theorem exists_schematicallyDense_coprod {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (C : Compactification f) (D : Compactification g)
    [QuasiCompact (Limits.coprod.desc f g)] :
    ∃ E : Compactification (Limits.coprod.desc f g), IsSchemeTheoreticallyDominant E.j := by
  let E := C.coprod D
  let : QuasiCompact (E.j ≫ E.p) := by rw [E.fac]; infer_instance
  have : QuasiCompact E.j := QuasiCompact.of_comp E.j E.p
  exact ⟨Compactification.ofImmersion _ E.j E.p E.fac, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom.Compactification
