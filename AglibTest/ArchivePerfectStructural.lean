/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalModels
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure

/-! # Native objects and maps for the structural perfect-complex migration -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AglibTest.ArchivePerfect

/-- The standard derived category used by these interface checks. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

-- The source's actual standard Gabriel–Zisman carrier and Q are definitionally native.
example (X : Scheme.{u}) :
    DerivedCategory X.Modules =
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).Localization := rfl

example (X : Scheme.{u}) :
    DerivedCategory.Q (C := X.Modules) =
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).Q := rfl

example (X : Scheme.{u}) :
    strictToPerfect X ⋙ (locallyPerfect X).ι = (strictPerfect X).ι := rfl

example (X : Scheme.{u}) (S : ShortComplex (StrictPerfect X)) :
    (strictExactStructure X).conflation S ↔
      (S.map (strictPerfect X).ι).ShortExact := Iff.rfl

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

example (K : StrictPerfect X) :
    ((strictRestrict j).obj K).obj = (restrict j).obj K.obj := rfl

example :
    derivedRestrict j = (Scheme.Modules.restrictFunctor j).mapDerivedCategory := rfl

example :
    derivedRestrictFactors j =
      (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors := rfl

-- The factorization identifies the actual restricted chain maps with their derived images.
example {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    (derivedRestrict j).map (DerivedCategory.Q.map f) ≫
        (derivedRestrictFactors j).hom.app L =
      (derivedRestrictFactors j).hom.app K ≫ DerivedCategory.Q.map ((restrict j).map f) :=
  (derivedRestrictFactors j).hom.naturality f

example {K L : CochainComplex X.Modules ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    (restrictDerivedIso j e).hom =
      (derivedRestrictFactors j).inv.app K ≫ (derivedRestrict j).map e.hom ≫
        (derivedRestrictFactors j).hom.app L := by
  simp [restrictDerivedIso]

example : (derivedRestrict j).CommShift ℤ := by
  dsimp [derivedRestrict]
  infer_instance

example : (derivedRestrict j).IsTriangulated := by
  dsimp [derivedRestrict]
  infer_instance

-- Compare the source's old direct GZ lift with the chosen native exact restriction.
-- Its component on each original complex is precisely the inverse factorization component.
example :
    let W := HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)
    let F := restrict j ⋙ DerivedCategory.Q (C := U.Modules)
    ∃ (hF : W.IsInvertedBy F)
      (e : Localization.Construction.lift F hF ≅ derivedRestrict j),
      ∀ K : CochainComplex X.Modules ℤ,
        e.hom.app (DerivedCategory.Q.obj K) = (derivedRestrictFactors j).inv.app K := by
  dsimp only
  let W := HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)
  let F := restrict j ⋙ DerivedCategory.Q (C := U.Modules)
  let hF : W.IsInvertedBy F := by
    intro K L f hf
    let : QuasiIso f := hf
    change IsIso (DerivedCategory.Q.map ((restrict j).map f))
    infer_instance
  let G := Localization.Construction.lift F hF
  let : Localization.Lifting (DerivedCategory.Q (C := X.Modules)) W F G :=
    ⟨eqToIso (Localization.Construction.fac F hF)⟩
  let : Localization.Lifting (DerivedCategory.Q (C := X.Modules)) W F (derivedRestrict j) :=
    ⟨derivedRestrictFactors j⟩
  refine ⟨hF, Localization.liftNatIso DerivedCategory.Q W F F G (derivedRestrict j)
    (Iso.refl F), ?_⟩
  intro K
  change (Localization.liftNatTrans (DerivedCategory.Q (C := X.Modules)) W F F G
    (derivedRestrict j) (𝟙 F)).app (DerivedCategory.Q.obj K) = _
  rw [Localization.liftNatTrans_app]
  change (eqToIso (Localization.Construction.fac F hF)).hom.app K ≫
    (Iso.refl F).hom.app K ≫ (derivedRestrictFactors j).inv.app K = _
  simp

end AglibTest.ArchivePerfect
