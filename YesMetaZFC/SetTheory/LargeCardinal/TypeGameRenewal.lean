import YesMetaZFC.SetTheory.LargeCardinal.TypeRenewal
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameSetup
import YesMetaZFC.Model.SetTheory.Internal.TypeGameGraph

/-! # 从原游戏节点自动构造每轮弹性回答

局部不可分辨参数带由游戏的原最小对给出。树的实际节点保证全部旧标签
属于该参数带；根与序数末位的区别由空根和配对编码保证，无须额外排列假设。
回答同时保留原节点，满足规则 (7) 的三条查询，并给出实际一步扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Tg_low_d.band_l (hZF : M.Models ZF) {ω e δ S ν : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hδ : M.IsOrdinal δ) (hwδ : M.mem ω δ) (low : Tg_low_d hZF ω e δ S ν) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ γ W F μ, M.IsLimitOrdinal γ ∧ V_d I γ W ∧ M.mem ω W ∧ M.mem δ W ∧ M.mem S W ∧
      Tt_pool_d I ω e W F ∧ Li_pair_d I ω e W F ν μ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ρ, θ, γ, W, F, μ, rank, ho, max, sum, hW, pool, least⟩ := low
  have limit := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I ho).limit_value (hω.isLimitOrdinal hZF) sum
  have lt : M.mem θ γ := (ZF.ordinalAddition_mem_iff hZF I (hω.isOrdinal hZF) sum).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl⟩)
  have dγ := ordinal_down_l (ZF.modelsKP hZF) hδ limit.1 (fun x hx => (max x).mpr (Or.inl hx)) lt
  have rγ := ordinal_down_l (ZF.modelsKP hZF) (rank.ordinal I) limit.1
    (fun x hx => (max x).mpr (Or.inr hx)) lt
  exact ⟨γ, W, F, μ, limit, hW, ZF.v_ordinal_mem_l I hZF hW (limit.1.transitive δ dγ ω hwδ),
    ZF.v_ordinal_mem_l I hZF hW dγ, (ZF.rk_mem_l I hZF rank hW).mpr rγ, pool, least.2.1⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_low_d.renew_l {ω e δ S ν κ k l n α A c R r B U D P u v b a z χ s t g : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hd : Woodin_d I δ) (low : Tg_low_d hZF ω e δ S ν) (root : M.mem e S)
    (hκδ : M.mem κ δ) (succ : M.SuccessorOf n l)
    (height : M.SuccessorOf α ν) (hA : V_d I α A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R n r δ U P u)
    (language : Ee_language_d hZF ω κ l B U D q) (drop : Td_dcp_d I l n D u v)
    (elastic : Ee_elastic_d q v) (first : Rd_entry_d e S r) (last : Rd_entry_d l ν r)
    (set : Sg_set_d I e l r g) (node : Tg_node_d I k S s t g)
    (prog : Ts_program_d hZF ω l b σ a z) (hχ : M.mem χ δ) :
    ∃ τ C V Q w η Y d H, ∃ q' : Ee_queries_d M, ∃ p : Tg_reply_queries_d M,
      M.mem χ τ ∧ M.mem κ τ ∧ M.mem τ δ ∧ Tg_height_d ν η ∧ V_d I η Y ∧ Smem_d I d Y H ∧
      Ee_language_d hZF ω τ n C V Q q' ∧ Tt_realized_d I ω d Y H n r δ V Q w ∧ Ee_elastic_d q' w ∧
      Tg_reply_language_d hZF ω e l n τ C V Q p ∧ M.mem p.root w ∧ M.mem p.bound w ∧ M.mem p.height w ∧
      Tx_exceeds_d hZF ω δ κ l U D v τ n V Q w ∧ Ee_one_step_d hZF ω κ δ l v τ n w b σ z := by
  have woodin := hd
  obtain ⟨ω₀, _, hw₀, hwδ, regular, _⟩ := woodin
  have eq := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hw₀.2 ω hω.1 x, hω.2 ω₀ hw₀.1 x⟩)
  subst ω₀
  obtain ⟨hδν, A₀, hA₀, hS₀⟩ := low.read_l hZF regular.isCardinal.1
  obtain ⟨γ, W, F, μ, hγ, hW, hwW, hδW, hSW, pool, pair⟩ := low.band_l hZF hω he heω regular.isCardinal.1 hwδ
  have labels := node.labels_mem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    (ZF.v_transitive_l I hZF hW) hSW (sc_v_pair_l hZF hγ hW)
  have values i x (hi : M.mem i l) (hx : Rd_entry_d i x r) : M.mem x W ∧ x ≠ ν := by
    by_cases eq : i = e
    · have same := type.tuple.2.2 e ((type.tuple.bound_l first).1) x (type.tuple.bound_l hx).2 S
        (type.tuple.bound_l first).2 (eq ▸ hx) first
      subst x
      exact ⟨hSW, fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) ν
        (ZF.v_ordinal_height_l hZF hA₀ pair.1 (eq ▸ hS₀))⟩
    · have gx := (set x).mpr ⟨i, hi, eq, hx⟩
      obtain ⟨j, y, cp⟩ := node.2.2.1.1.1 x gx
      exact ⟨labels x gx, fun eq => cp.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF)) (eq.symm ▸ pair.1.transitive)⟩
  obtain ⟨τ, C, V, Q, w, η, Y, d, H, q', hχτ, hκτ, hτδ, level, hY, mdl, lang, real, el, exceeds, step⟩ :=
    tg_renew_l hZFC hω he heω hd hγ hW hwW hδW pool pair hδν hκδ succ height hA model type language
      drop elastic last values prog hχ
  obtain ⟨C', V', Q', p, target⟩ := tg_reply_language_l hZF hω he type.finite
    (type.tuple.bound_l first).1 succ.predecessor_mem lang.limit
  have eqC := ZF.v_unique_l I hZF target.rank lang.rank
  subst C'
  have eqV := hZF.1.eq_of_same_members V' V (fun x => (target.constants x).trans (lang.constants x).symm)
  subst V'
  have eqQ := target.pool.unique_l hZF.1 I lang.pool
  subst Q'
  exact ⟨τ, C, V, Q, w, η, Y, d, H, q', p, hχτ, hκτ, hτδ, level, hY, mdl, lang, real, el, target,
    (target.root.2 d Y H r δ w S mdl (ZF.v_transitive_l I hZF hY) real first).mpr root,
    (target.bound.2 η Y d H r δ w S ν hY mdl real first last).mpr ⟨pair.1, hδν, A₀, hA₀, hS₀⟩,
    (target.height.2 η Y d H r δ w ν hY mdl real last).mpr level, exceeds, step⟩

end YesMetaZFC.SetTheory.LargeCardinal
