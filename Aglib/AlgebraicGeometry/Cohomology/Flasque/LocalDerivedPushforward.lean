/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Locality.QuasiIso
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Complex
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/LocallyFlasqueDerivedPushforward.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 113]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Local flasque computation of actual bounded-below direct images

A bounded-below complex computes its installed direct image if its terms are
flasque on the inverse images of a genuine target open cover. Original open
base change and local quasi-isomorphism detection compare its actual injective
replacement. No upper bound, global flasqueness, or supplied replacement
comparison is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v}
  (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
  (hcover : ∀ y : Y, ∃ (i : ι) (z : U i), j i z = y)
include hcover
/-- Direct image preserves original bounded-below quasi-isomorphisms when the terms
are flasque on the actual inverse images of a target open cover. -/
theorem quasiIso_pushforward_of_locally_flasque
    {K L : CochainComplex X.Modules ℤ} (q : K ⟶ L) [QuasiIso q]
    (a b : ℤ) (hKa : ∀ n, n < a → IsZero (K.X n))
    (hLb : ∀ n, n < b → IsZero (L.X n))
    (hK : ∀ i n, TopCat.Presheaf.IsFlasque
      ((K.X n).restrict (pullback.fst f (j i))).presheaf)
    (hL : ∀ i n, TopCat.Presheaf.IsFlasque
      ((L.X n).restrict (pullback.fst f (j i))).presheaf) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map q) := by
  apply quasiIso_of_restrict_openCover U j hcover
  intro i
  let P := Scheme.Modules.restrictFunctor (pullback.fst f (j i))
  let G := Scheme.Modules.pushforward (pullback.snd f (j i))
  have hq : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
      ((P.mapHomologicalComplex (.up ℤ)).map q)) :=
    quasiIso_pushforward_of_flasque (pullback.snd f (j i))
      ((P.mapHomologicalComplex (.up ℤ)).map q) a b
      (fun n hn => P.map_isZero (hKa n hn))
      (fun n hn => P.map_isZero (hLb n hn)) (hK i) (hL i)
  let e := NatIso.mapHomologicalComplex (openBaseChange f (j i)) (.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality q).symm)).mpr hq
end AlgebraicGeometry.Scheme.Modules

noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- Standard original module-sheaf derived categories. -/
local instance locallyFlasqueComplexStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
/-- Every locally flasque bounded-below complex computes its original derived direct image. -/
theorem isIso_derivedPushforwardPlusUnit_of_locally_flasque {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type*} (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ y : Y, ∃ (i : ι) (z : U i), j i z = y)
    (K : CochainComplex.Plus X.Modules)
    (hK : ∀ i n, TopCat.Presheaf.IsFlasque
      ((K.obj.X n).restrict (pullback.fst f (j i))).presheaf) :
    IsIso ((derivedPushforwardPlusUnit f).app K) := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  obtain ⟨J, hJ, q, hq⟩ := CochainComplex.Plus.exists_quasiIso_injective K a
  let L := (InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J
  let F := Scheme.Modules.pushforward f
  let : QuasiIso q.hom := hq
  have hL (i : ι) (n : ℤ) : TopCat.Presheaf.IsFlasque
      ((L.obj.X n).restrict (pullback.fst f (j i))).presheaf := by
    let : Injective (L.obj.X n) := inferInstanceAs (Injective (J.obj.X n).obj)
    infer_instance
  obtain ⟨b, hb⟩ := L.property
  let := hb
  have hFq : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map q.hom) :=
    quasiIso_pushforward_of_locally_flasque f U j hcover q.hom a b
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
