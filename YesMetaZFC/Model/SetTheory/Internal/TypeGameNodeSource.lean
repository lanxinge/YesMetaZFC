import YesMetaZFC.Model.SetTheory.Internal.TypeGameNode
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # 完整树节点在传递源中的绝对性

所有见证均从已有函数图或树成员中回收。源模型只需传递性，
不要求后继秩层对配对、替换或 ZF 封闭。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X}) (hE : Extensional M)
  (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
local notation "N" => rt_model_l X nx
local notation "I" => kpair_interpretation_l M hE hP
include hX

theorem tg_graph_source_l {d} (ρ : Env N d) (k f : Term d) :
    Formula.satisfies ρ (tg_graph_m k f) ↔ Tg_graph_d I (k.eval ρ).val (f.eval ρ).val := by
  simp only [tg_graph_m, Tg_graph_d, Formula.satisfies_conj_iff,
    rt_function_formula_l hX nx hE hP, rt_domain_formula_l hX nx hE hP]

theorem tg_join_source_l {d} (ρ : Env N d) (k s t g q : Term d) :
    Formula.satisfies ρ (tg_join_m k s t g q) ↔
      Tg_join_d I (k.eval ρ).val (s.eval ρ).val (t.eval ρ).val (g.eval ρ).val (q.eval ρ).val := by
  simp only [tg_join_m, Tg_join_d, Formula.satisfies_conj_iff, tg_graph_source_l hX nx hE hP,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    rt_entry_formula_l hX nx hE, rt_kpair_formula_l hX nx hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · intro h i hi
    obtain ⟨x, y, z, v, p, hx, hy, hz, hv, hp, hq⟩ := h ⟨i, hX _ (k.eval ρ).property i hi⟩ hi
    exact ⟨x.val, y.val, z.val, v.val, p.val, hx, hy, hz, hv, hp, hq⟩
  · intro h i hi
    obtain ⟨x, y, z, v, p, hx, hy, hz, hv, hp, hq⟩ := h i.val hi
    have xp := rd_entry_transitive_l hX (s.eval ρ).property hx
    have yp := rd_entry_transitive_l hX (t.eval ρ).property hy
    have zp := rd_entry_transitive_l hX (g.eval ρ).property hz
    have pp := (rd_entry_transitive_l hX (q.eval ρ).property hq).2
    have vp := (hp.mem_l M hX pp).2
    exact ⟨⟨x, xp.2⟩, ⟨y, yp.2⟩, ⟨z, zp.2⟩, ⟨v, vp⟩, ⟨p, pp⟩, hx, hy, hz, hv, hp, hq⟩

theorem tg_node_source_l {d} (ρ : Env N d) (k S s t g : Term d) :
    Formula.satisfies ρ (tg_node_m k S s t g) ↔
      Tg_node_d I (k.eval ρ).val (S.eval ρ).val (s.eval ρ).val (t.eval ρ).val (g.eval ρ).val := by
  simp only [tg_node_m, Tg_node_d, Formula.satisfies_conj_iff, tg_graph_source_l hX nx hE hP,
    Formula.satisfies_existsMem_iff, tg_join_source_l hX nx hE hP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩))
  · rintro ⟨q, hq, h⟩
    exact ⟨q.val, hq, h⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨⟨q, hX _ (S.eval ρ).property q hq⟩, hq, h⟩

end YesMetaZFC.SetTheory.Internal
