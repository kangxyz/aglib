/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.PullbackPushforward
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Complex
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso

/-! # Stable facts for Godement open base change

This leaf retains the original mathematical values and declarations from the
open-base-change module. The compatibility facade retains the source provenance.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

namespace Plus

/-- The standard derived category used for bounded-below flasque direct-image comparisons. -/
local instance openBaseChangeDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

lemma pushforward_quasiIso_of_flasque {P X : Scheme.{u}} (p : P ⟶ X)
    {K M : CochainComplex.Plus P.Modules} (s : K ⟶ M) [QuasiIso s.hom]
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf)
    (hM : ∀ n, TopCat.Presheaf.IsFlasque (M.obj.X n).presheaf) :
    QuasiIso ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map s).hom := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := M.property
  let := ha
  let := hb
  exact quasiIso_pushforward_of_flasque p s.hom a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE M.obj b n hn) hK hM

lemma quasiIso_of_isIso_Q_map {X : Scheme.{u}}
    {K M : CochainComplex.Plus X.Modules} (s : K ⟶ M)
    (h : IsIso (DerivedCategory.Plus.Q.map s)) : QuasiIso s.hom := by
  let := h
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).mp
  change IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map s))
  infer_instance

lemma quasiIso_of_span {Y : Scheme.{u}}
    {A B C D E : CochainComplex.Plus Y.Modules}
    (u : A ⟶ B) (β : B ⟶ C) [IsIso β] (r : C ⟶ E) (v : A ⟶ D) (s : D ⟶ E)
    (he : u ≫ β ≫ r = v ≫ s)
    (hr : QuasiIso r.hom) (hv : QuasiIso v.hom) (hs : QuasiIso s.hom) :
    QuasiIso u.hom := by
  let := hr
  let := hv
  let := hs
  let e := (CochainComplex.Plus.ι Y.Modules).mapIso (asIso β)
  have : IsIso β.hom := by
    change IsIso e.hom
    infer_instance
  have : QuasiIso (u.hom ≫ (β.hom ≫ r.hom)) := by
    have hvs : QuasiIso (v.hom ≫ s.hom) := inferInstance
    have hehom : u.hom ≫ β.hom ≫ r.hom = v.hom ≫ s.hom :=
      congrArg (fun q => q.hom) he
    exact hehom.symm ▸ hvs
  exact _root_.quasiIso_of_comp_right u.hom (β.hom ≫ r.hom)

end Plus

namespace Godement

/-- The standard derived category used for the cartesian open Godement comparison. -/
local instance openBaseChangeDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

lemma totalPlus_terms_isFlasque (P : Scheme.{u}) (K : CochainComplex.Plus P.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((godementTotalPlus P).obj K).obj.X n).presheaf := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  exact godementTotal_isFlasque K.obj a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE K.obj a i hi) n

end Godement
end AlgebraicGeometry.Scheme.Modules
