import YesMetaZFC.SetTheory.Foundation
import YesMetaZFC.SetTheory.Ord.Basic
import YesMetaZFC.SetTheory.Definitional.Project.Ord.Syntax

/-! # KP 序数的有界语法核

只用基础公理把传递性、成员传递性及线性比较识别为序数。
本层先于自然数构造，供 ω 上的 Δ₀ 归纳直接使用。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}
namespace KP

def Ord0_d (a : M.Domain) : Prop := M.TransitiveSet a ∧
  (∀ b, M.mem b a → M.TransitiveSet b) ∧
  ∀ b, M.mem b a → ∀ c, M.mem c a → b = c ∨ M.mem b c ∨ M.mem c b

def ord0_m {n} (a : Term n) : Formula 1 n :=
  .conj (Formula.isTransitive a) (.conj (Formula.forallMem a (Formula.isTransitive .newest))
    (Formula.forallMem a (Formula.forallMem a.weaken
      (.disj (Formula.extensionalEq (.bound 1) .newest) (.disj (.mem (.bound 1) .newest) (.mem .newest (.bound 1)))))))
derive_free_closed ord0_m

theorem ord0_delta_l {n} (a : Term n) : (ord0_m a).IsDelta0 :=
  .conj (Formula.isTransitive_delta0 _) (.conj (.forallMem _ (Formula.isTransitive_delta0 _))
    (.forallMem _ (.forallMem _ (.disj (.atom _ _ _) (.disj (.mem _ _) (.mem _ _))))))

theorem ord0_iff_l (hKP : M.Models KP) {a : M.Domain} : Ord0_d a ↔ M.IsOrdinal a := by
  constructor
  · rintro ⟨ht, hm, hc⟩
    have cmp b hb c hc' : M.SameMembers b c ∨ M.mem b c ∨ M.mem c b :=
      (hc b hb c hc').imp_left (fun (he : b = c) => he ▸ (fun _ => Iff.rfl))
    refine ⟨ht, ⟨⟨fun b _ => mem_irrefl_d hKP b,
      fun b _ c _ d hd hbc hcd => hm d hd c hcd b hbc, cmp⟩, ?_⟩⟩
    intro B hB hn
    obtain ⟨b, hb, hmin⟩ := mem_minimal_exists_d hKP hn
    exact ⟨b, hb, fun c hc => (cmp b (hB b hb) c (hB c hc)).elim Or.inl
      (fun h => h.elim Or.inr (fun h => (hmin c hc h).elim))⟩
  · intro h
    exact ⟨h.transitive, fun b hb => (h.mem hb).transitive, fun b hb c hc =>
      (h.wellOrder.linear.compare b hb c hc).imp_left (hKP.1.eq_of_same_members _ _)⟩

theorem ord0_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (a : Term n) :
    Formula.satisfies ρ (ord0_m a) ↔ M.IsOrdinal (a.eval ρ) := by
  apply Iff.trans ?_ (ord0_iff_l hKP)
  simp only [ord0_m, Ord0_d, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

end KP
end YesMetaZFC.SetTheory
