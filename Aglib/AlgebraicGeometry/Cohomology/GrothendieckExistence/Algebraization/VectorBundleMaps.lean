/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.Maps
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.VectorBundleCompletionMaps

/-! # Native algebra maps detected by vector-bundle completion

The existing algebra-map construction uses only the original scalar section
cone and finite locally free source, target, unit and source tensor square.
No full-faithfulness hypothesis for all coherent coefficients is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsQuasiAffine]
  {K : X.IdealSheafData}
  (hunit : IsLimit (idealSheafSectionCone X K (SheafOfModules.unit X.ringCatSheaf)))
  {F G : AdicSystem X K} [AdicAlgebraStructure F] [AdicAlgebraStructure G]
  (d : AdicAlgebraizationData F) (e : AdicAlgebraizationData G)
  [IsFiniteLocallyFree X d.coherent.obj] [IsFiniteLocallyFree X e.coherent.obj]
  [IsFiniteLocallyFree X (d.coherent.obj ⊗ d.coherent.obj)]
  (phi : F ⟶ G) [∀ n, IsMonHom (phi.hom.app n)]

/-- Lift the original native algebra map with every original quotient equation. -/
def vectorBundleAlgebraizationMapData :
    { f : d.algebra ⟶ e.algebra //
      (Functor.const ℕᵒᵖ).map f.hom.hom ≫ e.quotientMaps =
        d.quotientMaps ≫ phi.hom } := by
  let eu : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  let : IsFiniteLocallyFree X (𝟙_ X.Modules) := finiteLocallyFree_of_iso eu
  let β := (adicSystemToDiagram X K).mapIso e.beta
  let p := vectorBundleCompletionLiftData X K hunit d.coherent.obj e.coherent.obj β
    (d.quotientMaps ≫ phi.hom)
  have hu : JointlyDetects (fun n => e.quotientMaps.app n) (𝟙_ X.Modules) := by
    intro a b hab
    exact vectorBundleCompletionMaps_injective X K hunit
      (𝟙_ X.Modules) e.coherent.obj β hab
  have ht : JointlyDetects (fun n => e.quotientMaps.app n)
      (d.algebra.X ⊗ d.algebra.X) := by
    intro a b hab
    exact vectorBundleCompletionMaps_injective X K hunit
      (d.coherent.obj ⊗ d.coherent.obj) e.coherent.obj β hab
  exact algebraMapOfLiftedFamily d.quotientMaps e.quotientMaps phi.hom p hu ht

include hunit in
omit [IsFiniteLocallyFree X (d.coherent.obj ⊗ d.coherent.obj)]
    [∀ n, IsMonHom (phi.hom.app n)] in
/-- The same original quotient family determines the native algebra map uniquely. -/
theorem vectorBundleAlgebraizationMap_unique (a b : d.algebra ⟶ e.algebra)
    (ha : (Functor.const ℕᵒᵖ).map a.hom.hom ≫ e.quotientMaps =
      d.quotientMaps ≫ phi.hom)
    (hb : (Functor.const ℕᵒᵖ).map b.hom.hom ≫ e.quotientMaps =
      d.quotientMaps ≫ phi.hom) : a = b := by
  apply algebraMapOfLiftedFamily_unique d.quotientMaps e.quotientMaps phi.hom _ a b ha hb
  intro f g hfg
  exact vectorBundleCompletionMaps_injective X K hunit d.coherent.obj e.coherent.obj
    ((adicSystemToDiagram X K).mapIso e.beta) hfg

end AlgebraicGeometry.Scheme.Modules.Coherent
