/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Representable
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Zariski-local representability on locally Noetherian test schemes

Being locally Noetherian passes to open immersions and is local for open covers
(`isLocallyNoetherian_of_isOpenImmersion`, `isLocallyNoetherian_iff_openCover`), so the property
`fun T : Over S => IsLocallyNoetherian T.left` satisfies `IsOpenLocal`. This is the property
whose full subcategory is the category of locally Noetherian test schemes over `S` used for
Hilbert and Quot functors (Nitsure, arXiv:math/0504590v1, §1, pp. 3–4) and for the Picard
functor in Kleiman, arXiv:math/0504020v1, Thm 4.8.

Hence a Zariski sheaf on locally Noetherian schemes over `S`, covered by representable open
subfunctors, is represented by a locally Noetherian scheme over `S`
(`isRepresentable_of_isLocallyNoetherian`): the representing object `𝒰.glued` is an object of the
full subcategory.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S : Scheme.{u}}

instance isOpenLocal_isLocallyNoetherian :
    IsOpenLocal (fun T : Over S => IsLocallyNoetherian T.left) where
  of_isOpenImmersion g hg hT := by
    have : IsOpenImmersion g.left := hg
    have : IsLocallyNoetherian _ := hT
    exact isLocallyNoetherian_of_isOpenImmersion g.left
  of_jointlySurjective {T} ι W g hg hcov hW := by
    let 𝒱 : T.left.OpenCover :=
      { I₀ := ι
        X i := (W i).left
        f i := (g i).left
        mem₀ := by
          rw [presieve₀_mem_precoverage_iff]
          exact ⟨hcov, hg⟩ }
    exact (isLocallyNoetherian_iff_openCover 𝒱).2 hW

/-- **Stacks, Tag 01JJ** (Lemma 26.15.4) on locally Noetherian test schemes over `S`: a Zariski
sheaf on locally Noetherian schemes over `S` covered by representable open subfunctors is
represented by a locally Noetherian scheme over `S`, glued from the representing schemes. -/
theorem isRepresentable_of_isLocallyNoetherian
    {F : (ObjectProperty.FullSubcategory fun T : Over S => IsLocallyNoetherian T.left)ᵒᵖ ⥤
      Type v}
    (hF : IsZariskiSheaf F) (𝒰 : SubfunctorCover F) : F.IsRepresentable :=
  𝒰.isRepresentable hF

end AlgebraicGeometry.Scheme.LocalRepresentability
