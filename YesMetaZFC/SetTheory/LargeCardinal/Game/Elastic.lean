import YesMetaZFC.Model.SetTheory.Types.DropEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticDomain

/-! # 类型游戏中 dcp 的弹性条件

规则只对删除末位的原语法投影检查四条弹性查询。实现读取自动恢复
同一前缀及其前驱层；查询集合本身不被假定具有额外逻辑闭包。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_elastic_d (l n D : M.Domain) (q : Ee_queries_d M) (t : M.Domain) : Prop :=
  ∃ v, Td_dcp_d I l n D t v ∧ Ee_elastic_d q v

def tg_elastic_m {d} (l n D g h i e t : Term d) : Formula 1 d := set[d] ⟪∃ v,
  ⌜td_dcp_m⌝ₚ(⌜l⌝ₛ, ⌜n⌝ₛ, ⌜D⌝ₛ, ⌜t⌝ₛ, v) ∧ ⌜ee_elastic_m⌝ₚ(⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ, v)⟫
derive_free_closed tg_elastic_m

theorem tg_elastic_sat_l (hE : Extensional M) {d} (ρ : Env M d) (l n D g h i e t : Term d) :
    Formula.satisfies ρ (tg_elastic_m l n D g h i e t) ↔
      Tg_elastic_d I (l.eval ρ) (n.eval ρ) (D.eval ρ) ⟨g.eval ρ, h.eval ρ, i.eval ρ, e.eval ρ⟩ (t.eval ρ) := by
  simp only [tg_elastic_m, Tg_elastic_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    td_dcp_sat_l I hE, ee_elastic_sat_l, Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 只消费 dcp⁻ 的定义域，所需强度为 ZF；不使用不可达性或扩展器。 -/
theorem td_defined_read_l {ω κ l n B U D P δ η Y c R r t v : M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (language : Ee_language_d hZF ω κ l B U D q)
    (hY : V_d Q η Y) (model : Smem_d Q c Y R) (type : Tt_realized_d Q ω c Y R n r δ U P t)
    (drop : Td_dcp_d Q l n D t v) (defined : Ee_defined_d q v) :
    ∃ s ν A b H w, M.IsRestrictionOf Q s r l ∧ Tt_realized_d Q ω c Y R l s δ U D v ∧
      M.SuccessorOf η ν ∧ V_d Q ν A ∧ Smem_d Q b A H ∧
      Ee_minus_d Q ω D q v w ∧ Tt_realized_d Q ω b A H l s δ U D w := by
  obtain ⟨s, v', cut, drop', prefixType⟩ := type.dcp_l hZF hω drop.1 language.pool
  have eq := drop'.unique_l Q hZF.1 drop
  subst v'
  obtain ⟨ν, A, b, H, w, succ, hA, lower, minus, realized⟩ := language.defined_l hZF hω hY model prefixType defined
  exact ⟨s, ν, A, b, H, w, cut, prefixType, succ, hA, lower, minus, realized⟩

end YesMetaZFC.SetTheory.LargeCardinal
