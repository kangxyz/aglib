/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Complex
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/FlasqueComplexDerivedPushforward.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 70]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The installed derived unit on bounded-below flasque complexes

Use the original injective replacement of the given bounded-below complex.
The actual direct image preserves its quasi-isomorphism because both source
and target have flasque terms. Naturality of the installed derived unit
then proves that its original component is invertible. No replacement
comparison is supplied as a hypothesis.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- Standard original module-sheaf derived categories. -/
local instance flasqueComplexStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
/-- Every bounded-below flasque complex computes its original derived direct image. -/
theorem isIso_derivedPushforwardPlusUnit_of_flasque {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex.Plus X.Modules)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf) :
    IsIso ((derivedPushforwardPlusUnit f).app K) := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  obtain ⟨J, hJ, q, hq⟩ := CochainComplex.Plus.exists_quasiIso_injective K a
  let L := (InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J
  let F := Scheme.Modules.pushforward f
  let : QuasiIso q.hom := hq
  have hL (n : ℤ) : TopCat.Presheaf.IsFlasque (L.obj.X n).presheaf := by
    let : Injective (L.obj.X n) := inferInstanceAs (Injective (J.obj.X n).obj)
    infer_instance
  obtain ⟨b, hb⟩ := L.property
  let := hb
  have hFq : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map q.hom) :=
    quasiIso_pushforward_of_flasque f q.hom a b
      (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
      (fun n hn => CochainComplex.isZero_of_isStrictlyGE L.obj b n hn) hK hL
  have hQq : IsIso (DerivedCategory.Plus.Q.map q) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) q hq
  have hFQq : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map q)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso Y.Modules) _ hFq
  have hI : IsIso ((derivedPushforwardPlusUnit f).app L) :=
    inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J)))
  have hRq : IsIso ((DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f).map q) :=
    inferInstanceAs (IsIso ((derivedPushforwardPlus f).map (DerivedCategory.Plus.Q.map q)))
  have hcomp : IsIso ((derivedPushforwardPlusUnit f).app K ≫
      (DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f).map q) := by
    rw [← (derivedPushforwardPlusUnit f).naturality q]
    exact inferInstanceAs
      (IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map q) ≫
        (derivedPushforwardPlusUnit f).app L))
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f).map q)
end AlgebraicGeometry.Scheme.Modules
end
