/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeSourceIso
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange

/-! # Actual source-isomorphism and raw base-change geometry -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u
variable {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  (e : X' ≅ X) (he : e.hom ≫ f = f') (b : T ⟶ S)

/-- Pullback of the actual source isomorphism, with both native projections retained. -/
def sourceBaseChangeIso : pullback b f' ≅ pullback b f :=
  Hom.DenseCompactification.pullbackSourceIso f' e he b

@[reassoc]
theorem sourceBaseChangeIso_hom_fst :
    (sourceBaseChangeIso f f' e he b).hom ≫ pullback.fst b f = pullback.fst b f' :=
  Hom.DenseCompactification.pullbackSourceIso_hom_fst f' e he b

@[reassoc]
theorem sourceBaseChangeIso_hom_snd :
    (sourceBaseChangeIso f f' e he b).hom ≫ pullback.snd b f = pullback.snd b f' ≫ e.hom :=
  Hom.DenseCompactification.pullbackSourceIso_hom_snd f' e he b

variable (C : Hom.Compactification f)

/-- Actual raw model after base change and source transport, without densification. -/
def sourceBaseChangeTransportModel : Hom.Compactification (pullback.fst b f') :=
  (C.baseChange b).ofSourceIso (pullback.fst b f') (sourceBaseChangeIso f f' e he b)
    (sourceBaseChangeIso_hom_fst f f' e he b)

/-- The original raw open immersions coincide after the actual universal source map. -/
theorem sourceBaseChange_open :
    ((C.ofSourceIso f' e he).baseChange b).j =
      (sourceBaseChangeIso f f' e he b).hom ≫ (C.baseChange b).j := by
  apply pullback.hom_ext (f := b) (g := C.p)
  · calc
      _ = pullback.fst b f' := Hom.Compactification.baseChange_j_fst _ _
      _ = (sourceBaseChangeIso f f' e he b).hom ≫ pullback.fst b f :=
        (sourceBaseChangeIso_hom_fst f f' e he b).symm
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (fun z => (sourceBaseChangeIso f f' e he b).hom ≫ z)
          (Hom.Compactification.baseChange_j_fst C b)) |>.symm
  · calc
      _ = pullback.snd b f' ≫ (e.hom ≫ C.j) := Hom.Compactification.baseChange_j_snd _ _
      _ = ((sourceBaseChangeIso f f' e he b).hom ≫ pullback.snd b f) ≫ C.j := by
        rw [sourceBaseChangeIso_hom_snd, Category.assoc]
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (fun z => (sourceBaseChangeIso f f' e he b).hom ≫ z)
          (Hom.Compactification.baseChange_j_snd C b).symm).trans
          (Category.assoc _ _ _).symm)

private theorem sourceBaseChange_identityOpen {U M : Scheme.{u}} (j k : U ⟶ M) (h : j = k) :
    IsPullback j (𝟙 U) (𝟙 M) k := by
  subst k
  exact IsPullback.of_vert_isIso ⟨by simp⟩

private theorem sourceBaseChange_removeIdentity {U V M N : Scheme.{u}}
    (a : U ⟶ V) (j : U ⟶ M) (i : V ⟶ N) (q : M ⟶ N)
    (h : IsPullback a j i (q ≫ 𝟙 N)) : IsPullback a j i q :=
  (Category.comp_id q) ▸ h

/-- The comparison of the two original raw ambients is the actual identity map. -/
theorem sourceBaseChange_open_isPullback :
    IsPullback ((C.ofSourceIso f' e he).baseChange b).j
      (𝟙 (pullback b f')) (𝟙 (pullback b C.p))
      (sourceBaseChangeTransportModel f f' e he b C).j :=
  sourceBaseChange_identityOpen _ _ (sourceBaseChange_open f f' e he b C)

/-- The composite source square before source transport uses the actual given open map. -/
theorem sourceBaseChange_totalOpen :
    IsPullback (pullback.snd b f' ≫ e.hom) ((C.ofSourceIso f' e he).baseChange b).j
      C.j (pullback.snd b C.p) := by
  have h := (isPullback_rawCompactificationOpen (C.ofSourceIso f' e he) b).paste_horiz
    (isPullback_sourceIsoOpen e C.j)
  exact sourceBaseChange_removeIdentity _ _ _ _ h

end AlgebraicGeometry.Scheme.EtaleCohomology
