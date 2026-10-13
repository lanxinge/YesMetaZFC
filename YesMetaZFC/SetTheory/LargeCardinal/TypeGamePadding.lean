import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRound
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnchor
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastStep

/-! # 重置轮的 padding 与回到偶数枝的实际超幂

先保持当前模型，添加恒等边；再把同一模型中产生的回答扩展器施加到原
偶数节点。两次延伸都保存旧树，padding 本身不改变支撑列和原字母表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 38)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))
local notation "σ" => (Fin.cases (p 31) (Fin.cases (p 32) (Fin.cases (p 33) (Fin.cases (p 34)
  (Fin.cases (p 35) (Fin.cases (p 36) (fun _ => p 37)))))))

theorem Tg_context_d.pad_round_l {c₀ α ξ T J G E H c R μ K o π Cᵣ γ Z₀ : M.Domain}
    (context : Tg_context_d ω X η C) (owner : Ic_model_d hZF ω μ K X R)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (mx : Smem_d I c X R) (hw : p 0 = ω)
    (ho : ∀ x, ¬ M.mem x o) (root : It_map_d G o ξ π) (iRoot : Rd_entry_d Cᵣ C π)
    (anchor : Tg_anchor_d γ Z₀ X π) (lower : M.MemberSubset γ (p 5))
    (above : ∀ i ν, Rd_entry_d i ν H → M.mem ν (p 23) ∨ ν = p 23)
    (seed : Formula.satisfies ρ tg_seed0_m) :
    ∃ v : Fin 16 → (rt_model_l C nc).Domain,
      Formula.satisfies (tg_round_env_d ρ v) tg_round0_m ∧
      ∃ β T₁ J₁ G₁ E₁ id π₁,
        It_pnice_d hZF ω c₀ β T₁ J₁ G₁ E₁ H ∧ It_extension_d α ξ ξ T J G E β T₁ J₁ G₁ E₁ ∧
        Rd_entry_d α c J₁ ∧ It_map_d G₁ ξ α id ∧ (∀ x y, Rd_entry_d x y id → x = y) ∧
        (∀ q, Rd_entry_d ξ q E₁ → ∀ x, ¬ M.mem x q) ∧
        It_map_d G₁ o α π₁ ∧ Rd_entry_d Cᵣ C π₁ ∧ Tg_anchor_d γ Z₀ X π₁ ∧
      ∃ β₂ T₂ J₂ G₂ E₂ H₂ d j N R' K₀ L F κ' U' D' u' η' C' W,
        It_pnice_d hZF ω c₀ β₂ T₂ J₂ G₂ E₂ H₂ ∧ It_extension_d β α ξ T₁ J₁ G₁ E₁ β₂ T₂ J₂ G₂ E₂ ∧
        Rd_entry_d β d J₂ ∧ It_map_d G₂ ξ β j ∧ Smem_d I d N R' ∧ Ic_model_d hZF ω L K₀ N R' ∧
        It_ultra_d hZF ω (p 5) L F c d j ∧ Wd_crit_d I X j (p 5) κ' ∧
        M.IsLimitOrdinal L ∧ M.mem (v 15).val L ∧ M.MemberSubset L κ' ∧
        (∀ i ν, Rd_entry_d i ν H₂ → M.mem ν κ' ∨ ν = κ') ∧
        Rd_entry_d (p 15) U' j ∧ Rd_entry_d (p 16) D' j ∧ Rd_entry_d (p 18) u' j ∧
        Tg_reply_d I ω (p 7) (p 8) κ' (v 15).val U' D' (v 12).val u' (v 11).val (p 20) σ
          (p 22) ⟨(v 2).val, (v 1).val, (v 0).val⟩ ∧
        Rd_entry_d η η' j ∧ Rd_entry_d C C' j ∧ Tg_context_d ω N η' C' ∧
        Tg_reply_in_d ω (p 7) (p 8) κ' (v 15).val U' D' (v 12).val u' (v 11).val (p 20) (p 22)
          (v 2).val (v 1).val (v 0).val σ C' ∧
        M.mem W X ∧ M.mem W C ∧ Vr_d X L W ∧ Er_level_d N L W ∧ M.mem (v 12).val W ∧ M.mem (v 11).val W ∧
        (∀ ν, M.mem ν L → Ea_agree_d ω ν X N) ∧
        (∃ V₀, M.mem V₀ X ∧ Vr_d X (p 5) V₀ ∧ M.mem V₀ N ∧ Vr_d N (p 5) V₀ ∧
          ∀ x, M.mem x V₀ → Rd_entry_d x x j) ∧
        ∃ π₂, It_map_d G₂ o β π₂ ∧ Rd_entry_d Cᵣ C' π₂ ∧ Tg_anchor_d γ Z₀ N π₂ ∧
          Tg_past_update_d hZF ω X (p 5) α X R μ K η C L W N κ' j J J₂
            (fun i => ((tg_round_env_d ρ v).bound i).val) := by
  obtain ⟨v, valid⟩ := tg_successor_read_l ρ seed (context.renew_l hZF owner.source nc ρ seed)
  let ε := tg_round_env_d ρ v
  obtain ⟨β, T₁, J₁, G₁, E₁, c₁, id, padded, pad, hc₁, nextNode, edge₁, identity, empty⟩ := tree.pad_l hZF succ
  have eq := tree.tree.diagram.model_function.2 ξ c₁ c hc₁ hc
  subst c₁
  have oldNode := pad.2.2.1 ξ c hc
  have oldRoot := (pad.2.2.2.1 o ξ π succ.predecessor_mem).mpr root
  have embed := padded.tree.diagram.elementary ξ α id c X R c X R edge₁ oldNode nextNode mx.1 mx.1
  have fixed x (hx : M.mem x X) : Rd_entry_d x x id := by
    obtain ⟨y, _, hxy⟩ := embed.1.1.2.2 x hx
    exact (identity x y hxy).symm ▸ hxy
  obtain ⟨π₁, root₁⟩ := padded.tree.diagram.map_l hZF (padded.tree.diagram.order.root_l hZF ho α pad.1.predecessor_mem)
  have iRoot₁ := padded.tree.diagram.comp o ξ α π id π₁ oldRoot edge₁ root₁ Cᵣ C C iRoot (fixed C context.member)
  have anchor₁ : Tg_anchor_d γ Z₀ X π₁ := ⟨anchor.height, anchor.member, anchor.rank,
    fun x hx => padded.tree.diagram.comp o ξ α π id π₁ oldRoot edge₁ root₁ x x x (anchor.fixed x hx)
      (fixed x (owner.source.transitive Z₀ anchor.member x hx))⟩
  obtain ⟨ζ, V, hV, rank, hζ, hVC, hζδ, hκV⟩ := context.round_scope_l hZFC nc ε owner hw valid
  obtain ⟨β₂, T₂, J₂, G₂, E₂, H₂, d, j, N, R', K₀, L, F, κ', U', D', u', η', C', W,
    result, ext, target, edge, mn, ready, ultra, critical, limit, bound, subset, heights,
    hU, hD, hu, reply, iη, iC, context', legal, hW, hWC, common, level, hQW, hwW, agreement, fixedV⟩ :=
    context.round_l hZFC nc ε context owner owner padded pad.1 nextNode oldNode mx mx
      hV rank hV rank hζ hVC hζδ hκV hw above valid
  obtain ⟨π₂, root₂⟩ := result.tree.diagram.map_l hZF (result.tree.diagram.order.root_l hZF ho β ext.1.predecessor_mem)
  have oldRoot₂ := (ext.2.2.2.1 o ξ π ((padded.tree.diagram.model_domain ξ).mpr ⟨c, oldNode⟩)).mpr oldRoot
  have iRoot₂ := result.tree.diagram.comp o ξ β π j π₂ oldRoot₂ edge root₂ Cᵣ C C' iRoot iC
  have data := (Formula.satisfies_conj_iff ..).mp valid |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at data
  have hκL := limit.1.transitive (v 15).val bound (p 5) data.2.1
  have copy := fixedV
  obtain ⟨V₀, hV₀, rank₀, _, _, pointwise⟩ := copy
  have anchor₂ := anchor.extend_l hZF owner.source.transitive owner.source.transitive ready.source.transitive
    anchor.member anchor.rank hW common level.member level.hierarchy limit hκL lower
    hV₀ rank₀ pointwise result.tree.diagram oldRoot₂ edge root₂
  have past := context.past_update_l hZF owner nc ε valid hw owner.source.transitive hW common hW common limit
    (limit.1.transitive _ hκL) limit hWC common bound hwW (limit.1.transitive _ hκL)
    ready.source.transitive level.member level.hierarchy subset hV₀ rank₀ pointwise
    (fun i d hi => ext.2.2.1 i d (pad.2.2.1 i d hi)) (ext.2.2.1 α c nextNode) mx
  exact ⟨v, valid, β, T₁, J₁, G₁, E₁, id, π₁, padded, pad, nextNode, edge₁, identity, empty,
    root₁, iRoot₁, anchor₁, β₂, T₂, J₂, G₂, E₂, H₂, d, j, N, R', K₀, L, F, κ', U', D', u', η', C', W,
    result, ext, target, edge, mn, ready, ultra, critical, limit, bound, subset, heights,
    hU, hD, hu, reply, iη, iC, context', legal, hW, hWC, common, level, hQW, hwW, agreement, fixedV,
    π₂, root₂, iRoot₂, anchor₂, past⟩

end YesMetaZFC.SetTheory.LargeCardinal
