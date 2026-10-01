import YesMetaZFC.Model.Forcing.Iteration.Stage.SystemSuccessor
import YesMetaZFC.Model.Forcing.Iteration.Stage.SystemSyntax

/-! # 读取整个内部历史的后继规则

规则是实际原公式，输入整个条件集序列、序关系序列和当前长度。正确性包含
后继阶段、所有旧前缀提升及支撑保持；Cohen 规则由已有生产构造完整实现。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def row_rule_env_l {n} (ρ : Env M n) (δ F H e : M.Domain) : Env M (n+4) :=
  (((ρ.push δ).push F).push H).push e

def Row_extend_d (I : kpair_convention_l.Interpretation M) (k : Bool) (ω δ F H e D V : M.Domain) : Prop :=
  Row_stage_d M δ D V e ∧
  (∀ α B R, Entry_d M α B F → Entry_d M α R H → Row_link_d I α B R D V) ∧
  ∀ p, M.mem p D → Row_supp_d I k ω p

/-- 所有输出由一条原公式给出；存在唯一性和保持性必须由具体规则证明。 -/
def Row_rule_d (I : kpair_convention_l.Interpretation M) (k : Bool) (ω : M.Domain) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) : Prop :=
  ∀ δ F H e, Row_system_d I δ F H e → Row_system_supp_d I k ω F → (∃ α, M.SuccessorOf δ α) →
    ∃ D V, φ.denote (row_rule_env_l ρ δ F H e) D V ∧ Row_extend_d I k ω δ F H e D V ∧
      ∀ D' V', φ.denote (row_rule_env_l ρ δ F H e) D' V' → D' = D ∧ V' = V

def Cohen_rule_d (I : kpair_convention_l.Interpretation M) (κ δ F H e D V : M.Domain) : Prop :=
  ∃ α B R t, M.SuccessorOf δ α ∧ Entry_d M α B F ∧ Entry_d M α R H ∧
    Check_d M e κ t ∧ Row_cohen_d I α B R e t D V

def cohen_rule_m {n} (κ δ F H e D V : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (Formula.isSuccessor δ.weaken.weaken.weaken.weaken (.bound 3))
      (.conj (entry_m (.bound 3) (.bound 2) F.weaken.weaken.weaken.weaken)
        (.conj (entry_m (.bound 3) (.bound 1) H.weaken.weaken.weaken.weaken)
          (.conj (check_m e.weaken.weaken.weaken.weaken κ.weaken.weaken.weaken.weaken .newest)
            (row_cohen_m (.bound 3) (.bound 2) (.bound 1) e.weaken.weaken.weaken.weaken .newest
              D.weaken.weaken.weaken.weaken V.weaken.weaken.weaken.weaken))))))))
derive_free_closed cohen_rule_m

def cohen_rule_s : BinarySchema 5 := {
  body := cohen_rule_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

theorem cohen_rule_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (κ δ F H e D V : Term n) : Formula.satisfies ρ (cohen_rule_m κ δ F H e D V) ↔
      Cohen_rule_d I (κ.eval ρ) (δ.eval ρ) (F.eval ρ) (H.eval ρ) (e.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [cohen_rule_m, Cohen_rule_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, entry_sat_l M hE, check_sat_l M hE, row_cohen_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem cohen_rule_denote_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 1) (δ F H e D V) : cohen_rule_s.denote (row_rule_env_l ρ δ F H e) D V ↔
      Cohen_rule_d I (ρ.bound 0) δ F H e D V :=
  cohen_rule_sat_l I hE (((row_rule_env_l ρ δ F H e).push D).push V) _ _ _ _ _ _ _

/-- 任意地模型添加量产生真实的规则实例；通用递归的规则输入允许读取全部历史。 -/
theorem cohen_rule_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) (k : Bool) (ρ : Env M 1) :
    Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω cohen_rule_s ρ := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro δ F H e h hSupp hSucc
  obtain ⟨α, hδ⟩ := hSucc
  obtain ⟨B, hB⟩ := (h.conditions.2.2 α).mp hδ.predecessor_mem
  obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp hδ.predecessor_mem
  have hs := h.stages α B R hB hR
  obtain ⟨t, ht, htn, hut⟩ := zf_check_l M hZF hs.base (ρ.bound 0)
  obtain ⟨μ, D, V, _, F', H', _, hNext, hCohen, _, _, hF, hH, hS⟩ := row_system_cohen_l hZF h hδ hB hR htn
  have hd := (hF δ D).mpr (Or.inr ⟨rfl, rfl⟩)
  have hv := (hH δ V).mpr (Or.inr ⟨rfl, rfl⟩)
  refine ⟨D, V, (cohen_rule_denote_l I hZF.1 ρ δ F H e D V).mpr ⟨α, B, R, t, hδ, hB, hR, ht, hCohen⟩,
    ⟨hNext.stages δ D V hd hv, ?_, (hS I k ω hω hSupp) δ D hd⟩, ?_⟩
  · intro i P S hi hs
    exact hNext.links i δ P S D V ((hF i P).mpr (Or.inl hi)) ((hH i S).mpr (Or.inl hs)) hd hv
      (h.conditions.1.transitive.memberSubset ((h.conditions.2.2 i).mpr ⟨P, hi⟩))
  · intro D' V' h'
    obtain ⟨α', B', R', t', hδ', hB', hR', ht', hCohen'⟩ := (cohen_rule_denote_l I hZF.1 ρ δ F H e D' V').mp h'
    have ha := Structure.SuccessorOf.predecessor_eq hZF.1 (h.conditions.1.mem hδ.predecessor_mem) hδ hδ'
    subst α'
    have hb := h.conditions.2.1.2 α B B' hB hB'
    have hr := h.relations.2.1.2 α R R' hR hR'
    have htt := hut t' ht'
    subst B'; subst R'; subst t'
    exact row_cohen_unique_l hZF hs.order htn hCohen' hCohen

end YesMetaZFC.Model.Forcing.Internal
