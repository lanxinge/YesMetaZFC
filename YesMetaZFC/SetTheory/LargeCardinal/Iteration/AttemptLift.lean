import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember

/-! # 末结点嵌入确定唯一的联合行图

这里只编码既有节点构造的逐行值方程。完整节点仍由原构造给出；唯一性
使随后收集各结点的秩值可以直接使用替代，而不选择有限行或节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ja_lift_d (T G U k π P : M.Domain) : Prop := M.IsSetFunction I P ∧
  (∀ i, (∃ p, Rd_entry_d i p P) ↔ Rd_entry_d i k T) ∧
  ∀ i p, Rd_entry_d i p P → M.IsSetRelation I p ∧
    ∀ n y, Rd_entry_d n y p ↔ M.mem n k ∧ Ja_value_d G U k π i n y

def ja_lift_m {d} (T G U k π P : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜P⌝ₛ) ∧
    (∀ i, (∃ p, ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ)) ↔ ⌜rd_entry0_m⌝ₚ(i, ⌜k⌝ₛ, ⌜T⌝ₛ)) ∧
    (∀ i p, ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ) → ⌜Formula.isRelation kpair_convention_l⌝ₚ(p) ∧
      (∀ n y, ⌜rd_entry0_m⌝ₚ(n, y, p) ↔ n ∈ ⌜k⌝ₛ ∧ ⌜ja_value_m⌝ₚ(⌜G⌝ₛ, ⌜U⌝ₛ, ⌜k⌝ₛ, ⌜π⌝ₛ, i, n, y)))⟫
derive_free_closed ja_lift_m

theorem ja_lift_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T G U k π P : Term d) :
    Formula.satisfies ρ (ja_lift_m T G U k π P) ↔
      Ja_lift_d I (T.eval ρ) (G.eval ρ) (U.eval ρ) (k.eval ρ) (π.eval ρ) (P.eval ρ) := by
  simp only [ja_lift_m, Ja_lift_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_isFunction_iff I hE, Formula.satisfies_isRelation_iff I,
    rd_entry0_sat_l hE, Formula.satisfies_mem_iff, ja_value_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Ja_lift_d.unique_l (hKP : M.Models KP) {T G U k π P Q : M.Domain}
    (h : Ja_lift_d (kp_pair_l hKP) T G U k π P) (g : Ja_lift_d (kp_pair_l hKP) T G U k π Q) : P = Q := by
  have sub {P Q} (h : Ja_lift_d (kp_pair_l hKP) T G U k π P) (g : Ja_lift_d (kp_pair_l hKP) T G U k π Q)
      i p (hp : Rd_entry_d i p P) : Rd_entry_d i p Q := by
    obtain ⟨q, hq⟩ := (g.2.1 i).mpr ((h.2.1 i).mp ⟨p, hp⟩)
    have eq := (h.2.2 i p hp).1.eq_of_pairMember_iff hKP.1 (g.2.2 i q hq).1
      (fun n y => ((h.2.2 i p hp).2 n y).trans ((g.2.2 i q hq).2 n y).symm)
    exact eq.symm ▸ hq
  exact h.1.1.eq_of_pairMember_iff hKP.1 g.1.1 (fun i p => ⟨sub h g i p, sub g h i p⟩)

theorem Ja_node_d.lift_l (hZF : M.Models ZF) {ω T Q G U G₀ U₀ A S o q k P π : M.Domain}
    (tree : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF)) ω ω Q U)
    (node : Ja_node_d (kp_pair_l (ZF.modelsKP hZF)) ω T Q G U A S o q k P)
    (values : ∀ i p, Rd_entry_d i p P → ∀ n y, Rd_entry_d n y p ↔ M.mem n k ∧ Ja_value_d G₀ U₀ k π i n y) :
    Ja_lift_d (kp_pair_l (ZF.modelsKP hZF)) T G₀ U₀ k π P := by
  refine ⟨node.function, node.domain, fun i p hp => ⟨?_, values i p hp⟩⟩
  have hi := (tree.order.bound i k ((node.domain i).mp ⟨p, hp⟩)).1
  obtain ⟨c, X, R, hc, mx⟩ := tree.model_l hZF hi
  obtain ⟨e, he⟩ := (en.domain i).mp hi
  have fn := (node.rows i p c X R e hp hc mx.1 he).1
  exact fun r hr => (fn.1 r hr).elim fun x hx => hx.2.elim fun y hy => ⟨x, y, hy.2⟩

end YesMetaZFC.SetTheory.LargeCardinal
