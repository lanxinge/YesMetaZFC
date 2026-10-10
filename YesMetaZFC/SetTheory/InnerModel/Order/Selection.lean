import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Construction
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.KP.Sigma1

/-! # 集合良序的有界选择与有限字典序

公共选择层直接供构造码序和逐层 Jensen 序使用；像和纤维均由 KP 实际构造。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Po_lex_d {D : Type u} (R : D → D → Prop) (a b c x y z : D) : Prop :=
  R a x ∨ (a = x ∧ (R b y ∨ (b = y ∧ R c z)))

theorem po_lex_trans_l {D : Type u} {R : D → D → Prop} {a b c x y z p q r : D}
    (ha : R a x → R x p → R a p) (hb : R b y → R y q → R b q) (hc : R c z → R z r → R c r)
    (h : Po_lex_d R a b c x y z) (g : Po_lex_d R x y z p q r) : Po_lex_d R a b c p q r := by
  rcases h with h | ⟨h, g' | ⟨g', f⟩⟩ <;> rcases g with i | ⟨i, j | ⟨j, k⟩⟩
  · exact Or.inl (ha h i)
  · exact Or.inl (i ▸ h)
  · exact Or.inl (i ▸ h)
  · exact Or.inl (h.symm ▸ i)
  · exact Or.inr ⟨h.trans i, Or.inl (hb g' j)⟩
  · exact Or.inr ⟨h.trans i, Or.inl (j ▸ g')⟩
  · exact Or.inl (h.symm ▸ i)
  · exact Or.inr ⟨h.trans i, Or.inl (g'.symm ▸ j)⟩
  · exact Or.inr ⟨h.trans i, Or.inr ⟨g'.trans j, hc f k⟩⟩

def Po_min_d (R : M.Domain → M.Domain → Prop) (X : M.Domain) : Prop :=
  ∃ c, M.mem c X ∧ ∀ d, M.mem d X → c = d ∨ R c d

theorem po_ordinal_min_l (hKP : M.Models KP) {X : M.Domain}
    (ho : ∀ a, M.mem a X → M.IsOrdinal a) (hn : ∃ a, M.mem a X) : Po_min_d M.mem X := by
  obtain ⟨a, ha, hm⟩ := KP.mem_minimal_exists_d hKP hn
  refine ⟨a, ha, fun b hb => ?_⟩
  rcases Structure.IsOrdinal.trichotomy hKP.1 (ho a ha) (ho b hb) (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP a b) with h | h | h
  · exact Or.inl (hKP.1.eq_of_same_members a b h)
  · exact Or.inr h
  · exact (hm b hb h).elim

theorem po_minfiber_l (hKP : M.Models KP) {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ c, M.mem c X → ∃ a, φ.toBinarySchema.denote ρ c a)
    (hu : ∀ c, M.mem c X → ∀ a b, φ.toBinarySchema.denote ρ c a → φ.toBinarySchema.denote ρ c b → a = b)
    {R : M.Domain → M.Domain → Prop}
    (hl : ∀ Y, (∀ a, M.mem a Y ↔ ∃ c, M.mem c X ∧ φ.toBinarySchema.denote ρ c a) → Po_min_d R Y) :
    ∃ a U, (∀ c, M.mem c U ↔ M.mem c X ∧ φ.toBinarySchema.denote ρ c a) ∧
      (∃ c, M.mem c U) ∧ ∀ c, M.mem c X → ∀ b, φ.toBinarySchema.denote ρ c b → a = b ∨ R a b := by
  obtain ⟨Y, hY⟩ := KP.d0_image_l hKP φ ρ X ht hu
  obtain ⟨a, ha, hm⟩ := hl Y hY
  let ψ : Delta0UnarySchema (n + 1) := {
    body := binary_pred_m φ.toBinarySchema (fun i => .bound ⟨i.val + 2, by omega⟩) .newest (.bound 1)
    freeClosed := by simp -implicitDefEqProofs
    delta0 := φ.delta0.bind_l _ }
  have hψ c : ψ.toUnarySchema.denote (ρ.push a) c ↔ φ.toBinarySchema.denote ρ c a := by
    simp only [UnarySchema.denote, ψ, binary_pred_sat_l]; rfl
  obtain ⟨U, hU⟩ := KP.separation_exists_d hKP ψ (ρ.push a) X
  have hf c : M.mem c U ↔ M.mem c X ∧ φ.toBinarySchema.denote ρ c a :=
    (hU c).trans (and_congr_right fun _ => hψ c)
  obtain ⟨c, hc, hca⟩ := (hY a).mp ha
  exact ⟨a, U, hf, ⟨c, (hf c).mpr ⟨hc, hca⟩⟩, fun d hd b hb => hm b ((hY b).mpr ⟨d, hd, hb⟩)⟩

theorem po_pair_bound_l {T p a b : M.Domain} (ht : M.TransitiveSet T) (hp : M.mem p T)
    (h : KPair_d M p a b) : M.mem a T ∧ M.mem b T := by
  have lift z (hz : z = a ∨ z = b) : M.mem z T := by
    obtain ⟨s, hs, hz⟩ := (kpair_union_l M h z).mpr hz
    exact ht s (ht p hp s hs) z hz
  exact ⟨lift a (Or.inl rfl), lift b (Or.inr rfl)⟩

end YesMetaZFC.SetTheory.InnerModel
