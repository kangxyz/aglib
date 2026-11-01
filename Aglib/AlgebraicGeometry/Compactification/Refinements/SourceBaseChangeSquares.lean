/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceBaseChange

/-! # Original source-transported raw open squares -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology

private theorem sourceBaseChange_removeLeftIdentity {U V M N : Scheme}
    (a : U ⟶ V) (j : U ⟶ M) (i : V ⟶ N) (q : M ⟶ N)
    (h : IsPullback a j i (𝟙 M ≫ q)) : IsPullback a j i q :=
  (Category.id_comp q) ▸ h

universe u
variable {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  (e : X' ≅ X) (he : e.hom ≫ f = f') (b : T ⟶ S) (C : Hom.Compactification f)

/-- The actual source-transported raw open square, before transporting its source arrow. -/
theorem sourceBaseChange_transportOpen :
    IsPullback ((sourceBaseChangeIso f f' e he b).hom ≫ pullback.snd b f)
      (sourceBaseChangeTransportModel f f' e he b C).j C.j (pullback.snd b C.p) :=
  sourceBaseChange_removeLeftIdentity _ _ _ _
    ((isPullback_sourceIsoOpen (sourceBaseChangeIso f f' e he b) (C.baseChange b).j).paste_horiz
      (isPullback_rawCompactificationOpen C b))

/-- The same original square after the actual universal projection equality. -/
theorem sourceBaseChange_transportTotalOpen :
    IsPullback (pullback.snd b f' ≫ e.hom)
      (sourceBaseChangeTransportModel f f' e he b C).j C.j (pullback.snd b C.p) :=
  (sourceBaseChangeIso_hom_snd f f' e he b) ▸
    sourceBaseChange_transportOpen f f' e he b C

end AlgebraicGeometry.Scheme.EtaleCohomology
