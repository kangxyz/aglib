/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomologyPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsOfUnityInverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-!
# Original module-unit cohomology with roots coefficients

On the same scheme, the original module-unit comparison followed by the
original roots-underlying isomorphism identifies Ext with roots cohomology
at every level. The geometric pullback square uses the selected roots
inverse-image isomorphism only at positive globally invertible level. It
allows arbitrary scheme morphisms and retains four independent Ext universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open GroupCohomology.Kummer.Coefficients

universe u wMX wMU wAX wAU

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules

section SameScheme

variable (X : Scheme.{u}) (n : ℕ)
  [HasExt.{wMX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]

/-- The canonical module-unit/roots cohomology comparison on the original
objects, valid at every level including zero and one. -/
def moduleRootsUnitExtCohomologyAddEquiv (q : ℕ) :
    Ext.{wMX} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q ≃+
      Sheaf.H.{wAX} (mu X n) q :=
  (etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMX, wAX} X
    (constantRing X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q).trans
      ((Sheaf.functorH X.smallEtaleTopology q).mapIso
        (moduleRootsOfUnityUnderlyingIso X n)).addCommGroupIsoToAddEquiv

/-- The forward map is the original unit comparison followed by the actual
underlying-roots coefficient map. -/
theorem moduleRootsUnitExtCohomologyAddEquiv_apply (q : ℕ)
    (e : Ext.{wMX} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q) :
    moduleRootsUnitExtCohomologyAddEquiv X n q e =
      Sheaf.H.map (moduleRootsOfUnityUnderlyingIso X n).hom q
        (etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMX, wAX} X
          (constantRing X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q e) := rfl

end SameScheme

section Pullback

variable {U X : Scheme.{u}} (f : U ⟶ X) (n : ℕ) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{wMX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- The native roots pullback on module-unit Ext, using the original exact
inverse image, selected unit transport and selected roots transport. -/
def moduleRootsUnitExtPullback (q : ℕ) :
    Ext.{wMX} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q →+
      Ext.{wMU} (moduleUnit U (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity U n) q :=
  ((Ext.mk₀ (moduleRootsOfUnityInverseImageIso f n hn hinv).hom).postcomp
    (moduleUnit U (ULift.{u + 1} (ZMod n))) (add_zero q)).comp
      (moduleUnitExtPullback f n (moduleRootsOfUnity X n) q)

/-- The map retains the actual roots coefficient morphism after the original
unit Ext pullback, without defining it by conjugating cohomology. -/
theorem moduleRootsUnitExtPullback_apply (q : ℕ)
    (e : Ext.{wMX} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q) :
    moduleRootsUnitExtPullback f n hn hinv q e =
      (moduleUnitExtPullback f n (moduleRootsOfUnity X n) q e).comp
        (Ext.mk₀ (moduleRootsOfUnityInverseImageIso f n hn hinv).hom) (add_zero q) := rfl

variable [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]

/-- The whole original module-unit/roots cohomology pullback square. The roots
iso uses its actual positive invertible level bounds; no bound is added on f. -/
theorem moduleRootsUnitExtCohomologyPullback_square (q : ℕ) :
    (moduleRootsUnitExtCohomologyAddEquiv.{u, wMU, wAU} U n q).toAddMonoidHom.comp
        (moduleRootsUnitExtPullback.{u, wMX, wMU} f n hn hinv q) =
      (Kummer.rootsCohomologyPullback.{u, wAX, wAU} f n hn hinv q).comp
        (moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, wAX} X n q).toAddMonoidHom := by
  ext e
  have hu : Sheaf.H.map
      ((moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f).hom.app
        (moduleRootsOfUnity X n)) q
      (etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMU, wAU} U
        (constantRing U (ULift.{u + 1} (ZMod n)))
        ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity X n)) q
        (moduleUnitExtPullback.{u, wMX, wMU} f n (moduleRootsOfUnity X n) q e)) =
      cohomologyPullback.{u, wAX, wAU} f
        ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj
          (moduleRootsOfUnity X n)) q
        (etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMX, wAX} X
          (constantRing X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q e) :=
    DFunLike.congr_fun (moduleUnitExtCohomologyPullback_square f n (moduleRootsOfUnity X n) q) e
  change moduleRootsUnitExtCohomologyAddEquiv U n q
      ((moduleUnitExtPullback f n (moduleRootsOfUnity X n) q e).comp
        (Ext.mk₀ (moduleRootsOfUnityInverseImageIso f n hn hinv).hom) (add_zero q)) = _
  rw [moduleRootsUnitExtCohomologyAddEquiv_apply, moduleUnitExtAddEquiv_naturality]
  rw [← Sheaf.H.map_comp_apply, moduleRootsOfUnityInverseImageIso_underlying]
  simp only [Sheaf.H.map_comp_apply]
  rw [hu, ← cohomologyPullback_coefficientMap]
  rfl

end Pullback

end AlgebraicGeometry.Scheme.EtaleCohomology
