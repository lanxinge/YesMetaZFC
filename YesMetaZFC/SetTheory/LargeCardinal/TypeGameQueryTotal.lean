import YesMetaZFC.SetTheory.LargeCardinal.TypeGameSetup
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCatalogRead

/-! # 原查询表覆盖全部合法新参数

表在开局前已经取定。这里只反射它的实际全域性，因此新反射层中的新键
也能读取原表项；没有为每轮另选一张语义查询表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_query_total_m {d} (ω e δ Q : Term d) : Formula 1 d := set[d] ⟪
  ∀ κ ∈ ⌜δ⌝ₛ, ∀ k s t, ⌜tg_query_request_m⌝ₚ(⌜ω⌝ₛ, κ, k, s, t) →
    ∃ x c, ⌜rd_quad_m⌝ₚ(x, κ, k, s, t) ∧ ⌜rd_entry0_m⌝ₚ(x, c, ⌜Q⌝ₛ) ∧
      ⌜tg_query_packet_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, κ, k, s, t, c)⟫
derive_free_closed tg_query_total_m

theorem Tg_setup_d.query_total_l (hZFC : M.Models ZFC) {p : Tg_params_d M.Domain} {X : M.Domain}
    (setup : Tg_setup_d hZFC p X) {d} (ρ : Env M d) (ω e δ Q : Term d)
    (hw : ω.eval ρ = p.ω) (he : e.eval ρ = p.e) (hd : δ.eval ρ = p.δ) (hq : Q.eval ρ = p.Q) :
    Formula.satisfies ρ (tg_query_total_m ω e δ Q) := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [tg_query_total_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, tg_query_request_sat_l hZF,
    Formula.satisfies_conj_iff, rd_quad_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    tg_query_packet_sat_l hZF, Definitional.Term.eval_weaken, hw, he, hd, hq]
  intro κ hk k s t request
  exact setup.queries.get_l hZFC setup.limit setup.above setup.rank hk request

end YesMetaZFC.SetTheory.LargeCardinal
