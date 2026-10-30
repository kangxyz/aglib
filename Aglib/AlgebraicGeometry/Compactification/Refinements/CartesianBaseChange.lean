/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenSquare
public import Aglib.AlgebraicGeometry.Compactification.BaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso

/-!
# Actual Cartesian squares for raw base-changed refinements

These squares concern the supplied ambient pullbacks and their original open
sources. They assert neither density of a raw pullback nor any choice of a new
compactification.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (b : T ⟶ S)

/-- The literal raw pullback compactification has the actual Cartesian open square. -/
theorem isPullback_rawCompactificationOpen :
    IsPullback (pullback.snd b f) (C.baseChange b).j C.j (pullback.snd b C.p) := by
  have hout : IsPullback ((C.baseChange b).j ≫ pullback.fst b C.p)
      (pullback.snd b f) b (C.j ≫ C.p) := by
    simpa only [Hom.Compactification.baseChange_j_fst, Hom.Compactification.fac] using
      (IsPullback.of_hasPullback b f)
  exact (hout.of_right (Hom.Compactification.baseChange_j_snd C b)
    (IsPullback.of_hasPullback b C.p)).flip

/-- The original source-isomorphism open square. -/
theorem isPullback_sourceIsoOpen {X X' M : Scheme.{u}} (e : X' ≅ X) (j : X ⟶ M) :
    IsPullback e.hom (e.hom ≫ j) j (𝟙 M) :=
  IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩

/-- The original ambient/base identity square. -/
theorem isPullback_sourceIsoProperIdentity {Y S : Scheme.{u}} (p : Y ⟶ S) :
    IsPullback (𝟙 Y) p p (𝟙 S) :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

universe u

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  {C D : DenseCompactification f} (a : C ⟶ D) (b : T ⟶ S)

/-- The supplied map of raw ambient pullbacks is itself Cartesian over the
original refinement map. -/
theorem isPullback_baseChangeAmbientMap :
    IsPullback (pullback.snd b C.p) (baseChangeAmbientMap a b) a.hom
      (pullback.snd b D.p) := by
  have hout : IsPullback
      (baseChangeAmbientMap a b ≫ pullback.fst b D.p)
      (pullback.snd b C.p) b (a.hom ≫ D.p) := by
    simpa only [baseChangeAmbientMap_fst, a.base_fac] using
      (IsPullback.of_hasPullback b C.p)
  exact (hout.of_right (baseChangeAmbientMap_snd a b)
    (IsPullback.of_hasPullback b D.p)).flip

/-- The raw base-changed refinement retains the actual Cartesian square over
its common open source, with no density assumption on either raw model. -/
theorem isPullback_baseChangeAmbientMap_open [QuasiCompact f] :
    IsPullback (C.toCompactification.baseChange b).j (𝟙 (pullback b f))
      (baseChangeAmbientMap a b) (D.toCompactification.baseChange b).j := by
  let jC : pullback b f ⟶ pullback b C.p := (C.toCompactification.baseChange b).j
  let jD : pullback b f ⟶ pullback b D.p := (D.toCompactification.baseChange b).j
  change IsPullback jC (𝟙 (pullback b f)) (baseChangeAmbientMap a b) jD
  have hC : IsPullback (pullback.snd b f) jC C.j (pullback.snd b C.p) :=
    EtaleCohomology.isPullback_rawCompactificationOpen C.toCompactification b
  have hD : IsPullback (pullback.snd b f) jD D.j (pullback.snd b D.p) :=
    EtaleCohomology.isPullback_rawCompactificationOpen D.toCompactification b
  have hopen : jC ≫ baseChangeAmbientMap a b = jD := baseChange_j_ambientMap a b
  have hout : IsPullback (𝟙 (pullback b f) ≫ pullback.snd b f) jC D.j
      (baseChangeAmbientMap a b ≫ pullback.snd b D.p) := by
    rw [baseChangeAmbientMap_snd a b]
    simpa only [Category.id_comp, Category.comp_id] using
      (hC.paste_horiz (isPullback_open a).flip)
  exact (hout.of_right ((Category.id_comp _).trans hopen.symm) hD).flip

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
