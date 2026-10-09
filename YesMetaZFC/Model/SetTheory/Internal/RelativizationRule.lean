import YesMetaZFC.Model.SetTheory.Internal.Builder
import YesMetaZFC.SetTheory.Notation

/-! # 限制编译的纯语法证书

规则只检查原指令、新指令和旧根到新根的图。存在量词展开为
∃vᵢ( vᵢ∈v_b ∧ ψ )，其中合取由两次取反和一次或非编码。
证书不包含任何预设的真值保持断言。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sr_at_d (k : Nat) (G r i j : M.Domain) : Prop := ∃ c, M.PairMember I r c G ∧ Sop_d I k c i j
def sr_at_m (k : Nat) {d} (G r i j : Term d) : Formula 1 d := .existsE (.conj
  (Formula.orderedPairMem 𝒞 r.weaken .newest G.weaken) (sop_m (𝒞 := 𝒞) k .newest i.weaken j.weaken))
derive_free_closed sr_at_m

theorem sr_at_sat_l (k : Nat) {d} (ρ : Env M d) (G r i j : Term d) :
    Formula.satisfies ρ (sr_at_m (𝒞 := 𝒞) k G r i j) ↔ Sr_at_d I k (G.eval ρ) (r.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [sr_at_m, Sr_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, sop_sat_l I, Definitional.Term.eval_weaken]; rfl

def Sr_rule_d (b T G c u : M.Domain) : Prop :=
  (∃ i j, Sop_d I 0 c i j ∧ Sr_at_d I 0 G u i j) ∨
  (∃ i j, Sop_d I 1 c i j ∧ Sr_at_d I 1 G u i j) ∨
  (∃ i j v w, Sop_d I 2 c i j ∧ M.PairMember I i v T ∧ M.PairMember I j w T ∧ Sr_at_d I 2 G u v w) ∨
  ∃ i j v a p q t, Sop_d I 3 c i j ∧ M.PairMember I j v T ∧ Sr_at_d I 0 G a i b ∧
    Sr_at_d I 2 G p a a ∧ Sr_at_d I 2 G q v v ∧ Sr_at_d I 2 G t p q ∧ Sr_at_d I 3 G u i t

def sr_rule_m {d} (b T G c u : Term d) : Formula 1 d := set[d] ⟪
  (∃ i j, ⌜sop_m (𝒞 := 𝒞) 0⌝ₚ(⌜c⌝ₛ, i, j) ∧ ⌜sr_at_m (𝒞 := 𝒞) 0⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, i, j)) ∨
  (∃ i j, ⌜sop_m (𝒞 := 𝒞) 1⌝ₚ(⌜c⌝ₛ, i, j) ∧ ⌜sr_at_m (𝒞 := 𝒞) 1⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, i, j)) ∨
  (∃ i j v w, ⌜sop_m (𝒞 := 𝒞) 2⌝ₚ(⌜c⌝ₛ, i, j) ∧ ⌜Formula.orderedPairMem 𝒞⌝ₚ(i, v, ⌜T⌝ₛ) ∧
    ⌜Formula.orderedPairMem 𝒞⌝ₚ(j, w, ⌜T⌝ₛ) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, v, w)) ∨
  (∃ i j v a p q t, ⌜sop_m (𝒞 := 𝒞) 3⌝ₚ(⌜c⌝ₛ, i, j) ∧ ⌜Formula.orderedPairMem 𝒞⌝ₚ(j, v, ⌜T⌝ₛ) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 0⌝ₚ(⌜G⌝ₛ, a, i, ⌜b⌝ₛ) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, p, a, a) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, q, v, v) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, t, p, q) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 3⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, i, t))⟫
derive_free_closed sr_rule_m

theorem sr_rule_sat_l {d} (ρ : Env M d) (b T G c u : Term d) :
    Formula.satisfies ρ (sr_rule_m (𝒞 := 𝒞) b T G c u) ↔
      Sr_rule_d I (b.eval ρ) (T.eval ρ) (G.eval ρ) (c.eval ρ) (u.eval ρ) := by
  simp only [sr_rule_m, Sr_rule_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, sop_sat_l I, sr_at_sat_l I,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem Sr_at_d.extend_l {ω m G l H z r i j : M.Domain} {a : Nat}
    (h : Sr_at_d I a G r i j) (e : Sbuild_d I ω m G l H z) : Sr_at_d I a H r i j := by
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨c, ((e.cut.2 r c).mp hc).2, hs⟩

theorem Sr_rule_d.mono_l {b T U G H c u : M.Domain} (h : Sr_rule_d I b T G c u)
    (map : ∀ i j, M.PairMember I i j T → M.PairMember I i j U)
    (program : ∀ i j, M.PairMember I i j G → M.PairMember I i j H) : Sr_rule_d I b U H c u := by
  have row {k r i j} (h : Sr_at_d I k G r i j) : Sr_at_d I k H r i j :=
    h.elim fun c h => ⟨c, program r c h.1, h.2⟩
  rcases h with ⟨i, j, hs, h⟩ | ⟨i, j, hs, h⟩ | ⟨i, j, v, w, hs, hi, hj, h⟩ |
    ⟨i, j, v, a, p, q, t, hs, hj, ha, hp, hq, ht, hu⟩
  · exact Or.inl ⟨i, j, hs, row h⟩
  · exact Or.inr (Or.inl ⟨i, j, hs, row h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, j, v, w, hs, map i v hi, map j w hj, row h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, j, v, a, p, q, t, hs, map j v hj, row ha, row hp, row hq, row ht, row hu⟩))

end YesMetaZFC.SetTheory.Internal
