import YesMetaZFC.Model.SetTheory.Internal.TransitiveFunctionFormula
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 类型游戏的完整节点谓词

节点仍是有限函数图。三张坐标图都有同一个精确定义域，逐点合成的三元组图
必须属于树；不从一个裸成员式推断函数性，也不对标签的枚举位置加条件。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_graph_d (k f : M.Domain) : Prop := M.IsSetFunction I f ∧ M.IsDomainOf I k f

def tg_graph_m {d} (k f : Term d) : Formula 1 d :=
  .conj (Formula.isFunction kpair_convention_l f) (Formula.isDomain kpair_convention_l k f)
derive_free_closed tg_graph_m

theorem tg_graph_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k f : Term d) :
    Formula.satisfies ρ (tg_graph_m k f) ↔ Tg_graph_d I (k.eval ρ) (f.eval ρ) := by
  simp only [tg_graph_m, Tg_graph_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunction_iff I hE, Formula.satisfies_isDomain_iff I]

def Tg_join_d (k s t g q : M.Domain) : Prop := Tg_graph_d I k q ∧ ∀ i, M.mem i k →
  ∃ x y z v p, M.PairMember I i x s ∧ M.PairMember I i y t ∧ M.PairMember I i z g ∧
    I.Codes v y z ∧ I.Codes p x v ∧ M.PairMember I i p q

def tg_join_m {d} (k s t g q : Term d) : Formula 1 d := set[d] ⟪⌜tg_graph_m⌝ₚ(⌜k⌝ₛ, ⌜q⌝ₛ) ∧
  (∀ i ∈ ⌜k⌝ₛ, ∃ x y z v p, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, x, ⌜s⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, y, ⌜t⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, z, ⌜g⌝ₛ) ∧
    ⌜kpair_convention_l.code⌝ₚ(v, y, z) ∧ ⌜kpair_convention_l.code⌝ₚ(p, x, v) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, p, ⌜q⌝ₛ))⟫
derive_free_closed tg_join_m

theorem tg_join_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k s t g q : Term d) :
    Formula.satisfies ρ (tg_join_m k s t g q) ↔ Tg_join_d I (k.eval ρ) (s.eval ρ) (t.eval ρ) (g.eval ρ) (q.eval ρ) := by
  simp only [tg_join_m, Tg_join_d, Formula.satisfies_conj_iff, tg_graph_sat_l I hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
    I.satisfies_code_iff, Definitional.Term.eval_weaken]
  rfl

def Tg_node_d (k S s t g : M.Domain) : Prop := Tg_graph_d I k s ∧ Tg_graph_d I k t ∧
  Tg_graph_d I k g ∧ ∃ q, M.mem q S ∧ Tg_join_d I k s t g q

def tg_node_m {d} (k S s t g : Term d) : Formula 1 d := set[d] ⟪
  ⌜tg_graph_m⌝ₚ(⌜k⌝ₛ, ⌜s⌝ₛ) ∧ ⌜tg_graph_m⌝ₚ(⌜k⌝ₛ, ⌜t⌝ₛ) ∧ ⌜tg_graph_m⌝ₚ(⌜k⌝ₛ, ⌜g⌝ₛ) ∧
    (∃ q ∈ ⌜S⌝ₛ, ⌜tg_join_m⌝ₚ(⌜k⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜g⌝ₛ, q))⟫
derive_free_closed tg_node_m

theorem tg_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k S s t g : Term d) :
    Formula.satisfies ρ (tg_node_m k S s t g) ↔ Tg_node_d I (k.eval ρ) (S.eval ρ) (s.eval ρ) (t.eval ρ) (g.eval ρ) := by
  simp only [tg_node_m, Tg_node_d, Formula.satisfies_conj_iff, tg_graph_sat_l I hE,
    Formula.satisfies_existsMem_iff, tg_join_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem tg_graph_empty_l {e : M.Domain} (he : ∀ x, ¬ M.mem x e) : Tg_graph_d I e e := by
  have no a b : ¬ M.PairMember I a b e := fun ⟨p, _, hp⟩ => he p hp
  exact ⟨⟨fun p hp => (he p hp).elim, fun a b _ h _ => (no a b h).elim⟩,
    fun i => iff_of_false (he i) (fun ⟨x, hx⟩ => no i x hx)⟩

/-- 长度零的完整节点条件恰为空根属于树。 -/
theorem tg_node_empty_l (hE : Extensional M) {e S : M.Domain} (he : ∀ x, ¬ M.mem x e) :
    Tg_node_d I e S e e e ↔ M.mem e S := by
  constructor
  · rintro ⟨_, _, _, q, hq, graph, _⟩
    have empty p (hp : M.mem p q) : False := by
      obtain ⟨i, x, pair⟩ := graph.1.1 p hp
      exact he i ((graph.2 i).mpr ⟨x, p, pair, hp⟩)
    exact hE.eq_of_same_members q e (fun x => iff_of_false (empty x) (he x)) ▸ hq
  · intro hS
    have graph := tg_graph_empty_l I he
    exact ⟨graph, graph, graph, e, hS, graph, fun i hi => (he i hi).elim⟩

/-- 三张实际同域函数图总能合成原节点图，字母表和节点均为模型内集合。 -/
theorem tg_join_exists_l (hZF : M.Models ZF) {k X Y Z s t g : M.Domain}
    (hs : M.IsSetFunctionFromTo I s k X) (ht : M.IsSetFunctionFromTo I t k Y) (hg : M.IsSetFunctionFromTo I g k Z) :
    ∃ V P q, M.IsCartesianProduct I V Y Z ∧ M.IsCartesianProduct I P X V ∧
      M.IsSetFunctionFromTo I q k P ∧ Tg_join_d I k s t g q := by
  obtain ⟨V, hv⟩ := ZF.exists_cartesianProduct hZF I Y Z
  obtain ⟨P, hp⟩ := ZF.exists_cartesianProduct hZF I X V
  let φ : BinarySchema 3 := {
    body := set[5] ⟪∃ x y z v,
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, x, ⌜(.bound 4 : Term 5)⌝ₛ) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, y, ⌜(.bound 3 : Term 5)⌝ₛ) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, z, ⌜(.bound 2 : Term 5)⌝ₛ) ∧
      ⌜kpair_convention_l.code⌝ₚ(v, y, z) ∧ ⌜kpair_convention_l.code⌝ₚ(⌜(.newest : Term 5)⌝ₛ, x, v)⟫ }
  let ρ : Env M 3 := ⟨Fin.cases g (Fin.cases t (fun _ => s)), fun _ => s⟩
  have read i p : φ.denote ρ i p ↔ ∃ x y z v, M.PairMember I i x s ∧ M.PairMember I i y t ∧
      M.PairMember I i z g ∧ I.Codes v y z ∧ I.Codes p x v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff]
    rfl
  obtain ⟨q, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := k) (target := P)
    (fun i hi => by
      obtain ⟨x, _, hx⟩ := hs.2.2 i hi
      obtain ⟨y, _, hy⟩ := ht.2.2 i hi
      obtain ⟨z, _, hz⟩ := hg.2.2 i hi
      obtain ⟨v, cv⟩ := I.total y z
      obtain ⟨p, cp⟩ := I.total x v
      exact ⟨p, (read i p).mpr ⟨x, y, z, v, hx, hy, hz, cv, cp⟩⟩)
    (fun i _ p q hp hq => by
      obtain ⟨x, y, z, v, hx, hy, hz, cv, cp⟩ := (read i p).mp hp
      obtain ⟨x', y', z', v', hx', hy', hz', cv', cq⟩ := (read i q).mp hq
      have ex := hs.1.2 i x' x hx' hx
      have ey := ht.1.2 i y' y hy' hy
      have ez := hg.1.2 i z' z hz' hz
      subst x' y' z'
      exact I.unique cp (I.unique cv' cv ▸ cq))
    (fun i p _ h => by
      obtain ⟨x, y, z, v, hx, hy, hz, cv, cp⟩ := (read i p).mp h
      exact (hp p).mpr ⟨x, hs.output_mem_of_pairMember hx, v,
        (hv v).mpr ⟨y, ht.output_mem_of_pairMember hy, z, hg.output_mem_of_pairMember hz, cv⟩, cp⟩)
  refine ⟨V, P, q, hv, hp, fn, ⟨fn.1, fn.2.1⟩, fun i hi => ?_⟩
  obtain ⟨p, _, hq⟩ := fn.2.2 i hi
  obtain ⟨x, y, z, v, hx, hy, hz, cv, cp⟩ := (read i p).mp ((graph i p).mp hq).2
  exact ⟨x, y, z, v, p, hx, hy, hz, cv, cp, hq⟩

end YesMetaZFC.SetTheory.Internal
