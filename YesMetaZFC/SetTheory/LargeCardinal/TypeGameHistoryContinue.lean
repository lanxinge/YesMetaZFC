import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContinueAuto
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastRoots

/-! # 统一历史自动驱动非空继续分支

轮号由原规则读取；旧完整源、根图、固定锚点、共同层及下界均从同一历史行
取得。增长规则给出的当前界足以覆盖整列支撑，调用方不再选择旧源或构造 seed。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_past_events_d.continue_tree_l {ω X R μ K η C c₀ α ξ T Q G E L H b c o π Cᵣ γ Z : M.Domain}
    (context : Tg_context_d ω X η C) (source : Ic_model_d hZF ω μ K X R)
    (nc : Nonempty {x // M.mem x C}) (ι : Env (rt_model_l C nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val = ω) (ne : ι.bound 23 ≠ ι.bound 1)
    (tree : It_pnice_d hZF ω c₀ α T Q G E L) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (mx : Smem_d I c X R) (ho : ∀ x, ¬ M.mem x o)
    (root : It_map_d G o ξ π) (image : Rd_entry_d Cᵣ C π) (anchor : Tg_anchor_d γ Z X π)
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z) (letters : M.mem (ι.bound 6).val Z)
    (past : Tg_past_d hZF ω (ι.bound 19).val H X b) (links : Tg_past_links_d I H Q)
    (roots : Tg_past_roots_d ω H G o Cᵣ γ Z)
    (events : Tg_past_events_d ω H C (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val (ι.bound 20).val)
    (below : M.mem b (ι.bound 24).val) (bounds : ∀ i ν, Rd_entry_d i ν L → M.mem ν b ∨ ν = b) :
    Tg_tree_step_d hZF ω X η c₀ α ξ T Q G E c o Cᵣ γ Z H nc ι := by
  have fs := (context.read_l hZF source.source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ι).mp issued
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, fork, _, _, _, _, _, _, language⟩ :=
    tg_issued_query_l J ext ι issued
  have index : M.mem (ι.bound 22).val (ι.bound 19).val := ((Formula.satisfies_conj_iff ..).mp (fork ne)).1
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at language
  have κlimit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ι.bound 24)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.2.2.1)
  have card : Sc_inaccessible_d ω X (ι.bound 5).val :=
    context.control_card_l hZF source.source nc _ state.control hw
  have δlimit := card.limit_l (ZF.modelsKP hZF) source.source.transitive source.source.theory.algebra.pair
  obtain ⟨k, Y, S, μ₀, K₀, η₀, C₀, ℓ, V, q, d, row, node, model, saved, member, rank, bound⟩ :=
    past.select_l hZF links index
  let nc₀ : Nonempty {x // M.mem x C₀} := ⟨⟨ω, saved.context.omega⟩⟩
  obtain ⟨ρ₀, code, round, hw₀, hκV, hU, hD, hu⟩ := saved.read_l hZF nc₀
  obtain ⟨⟨π₀, root₀, image₀, anchor₀⟩, v, code', high⟩ := roots _ _ _ _ _ _ _ _ _ _ _ row
  have eq : v 15 = (ρ₀.bound 15).val := congrFun (rt_tuple_inj_l code' code) 17
  have high : M.MemberSubset γ (ρ₀.bound 15).val := eq ▸ high
  obtain ⟨v, code', traced⟩ := events _ _ _ _ _ _ _ _ _ _ _ row
  have eq := rt_tuple_inj_l code' code
  have et : v 41 = (ρ₀.bound 41).val := congrFun eq 43
  have eτ : v 15 = (ρ₀.bound 15).val := congrFun eq 17
  have ew : v 11 = (ρ₀.bound 11).val := congrFun eq 13
  have trace : Tg_trace_d ω C (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val (ι.bound 22).val
      (ι.bound 20).val (ρ₀.bound 41).val (ρ₀.bound 15).val (ρ₀.bound 11).val := et ▸ eτ ▸ ew ▸ traced
  have hℓκ := ordinal_down_l (ZF.modelsKP hZF) saved.limit.1 κlimit.1 bound below
  have hℓδ := δlimit.1.transitive (ι.bound 24).val state.bound ℓ hℓκ
  have above i ν (hn : Rd_entry_d i ν L) : M.mem ν (ι.bound 24).val :=
    (bounds i ν hn).elim (κlimit.1.transitive b below ν) (fun eq => eq.symm ▸ below)
  obtain ⟨_, _, _, _, _, _, step⟩ := context.continue_tree_l hZFC saved.context source saved.source nc nc₀ ρ₀ round hw₀ tree succ hc node mx model
    ho root root₀ image image₀ anchor anchor₀ high hγ hωZ ι issued hw ne letters row code trace member rank
    (saved.source.source.transitive C₀ saved.context.member V saved.member) saved.rank saved.limit saved.member
    hℓδ hκV hU hD hu above
  exact step

end YesMetaZFC.SetTheory.LargeCardinal
