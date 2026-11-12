import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.LocalTypeTransportTuple
import YesMetaZFC.Model.SetTheory.Types.DropEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinTypeStep
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax

/-! # 局部不可分辨点提升同一完整类型的原前缀

只移动原元组的末位高度；原前缀中的全部对象逐项保持。两种类型游戏
共同使用该提升，不把低处的类型换成另一个逻辑等价的代码集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Li_pair_d.raise_prefix_l
    {ω e γ W F δ ν μ κ q n α A c R r B U D P u v : M.Domain}
    (pair : Li_pair_d I ω e W F ν μ)
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (hγ : M.IsLimitOrdinal γ)
    (hW : V_d I γ W) (hδW : M.mem δ W) (band : Tt_pool_d I ω e W F)
    (hκδ : M.mem κ δ) (parameters : V_d I κ B)
    (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (pool : Tt_pool_d I ω q U D) (succ : M.SuccessorOf n q)
    (height : M.SuccessorOf α ν) (rank : V_d I α A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R n r δ U P u) (drop : Td_dcp_d I q n D u v)
    (last : Rd_entry_d q ν r)
    (values : ∀ i x, M.mem i q → Rd_entry_d i x r → M.mem x W ∧ x ≠ ν) :
    ∃ β Y d H s, M.SuccessorOf β μ ∧ V_d I β Y ∧ Smem_d I d Y H ∧
      Tt_realized_d I ω d Y H q s δ U D v ∧
      (∀ i x, M.mem i q → (Rd_entry_d i x s ↔ Rd_entry_d i x r)) := by
  obtain ⟨V,hV⟩ := ZF.v_exists_l I hZF hδ.1
  obtain ⟨one,so,ho⟩ := hw.1.2 e heω
  have zero : M.IsOrdinalAddition I ν ν e := (ZF.ordinalAddition_zero_iff hZF I empty).mpr rfl
  have add := (ZF.ordinalAddition_successor_iff hZF I (Structure.IsOrdinal.of_no_members empty) so).mpr
    ⟨ν,zero,height⟩
  obtain ⟨β,Y,d,H,r',add',hY,upper,move,type'⟩ := pair.transport_l hZF hw empty heω
    hδ hwδ hγ hW hδW band hκδ ho so.predecessor_mem add rank model hV parameters constants type (by
      intro i x hx
      rcases (succ i).mp (type.tuple.bound_l hx).1 with hi | eq
      · exact Or.inr (values i x hi hx).1
      · exact Or.inl ((fn0_function_l (ZF.modelsKP hZF) type.tuple).1.2 q x ν
          (hZF.1.eq_of_same_members i q eq ▸ hx) last))
  obtain ⟨t,zt,sb⟩ := (ZF.ordinalAddition_successor_iff hZF I (Structure.IsOrdinal.of_no_members empty) so).mp add'
  have et := (ZF.ordinalAddition_zero_iff hZF I empty).mp zt
  subst t
  obtain ⟨s,v',cut,drop',full⟩ := type'.dcp_l hZF hw succ pool
  have ev := drop.2.unique_l I hZF.1 drop'.2
  subst v'
  refine ⟨β,Y,d,H,s,sb,hY,upper,full,fun i x hi => ?_⟩
  refine (cut.2 i x).trans ((and_iff_right hi).trans ((move i x).trans ⟨?_,?_⟩))
  · rintro ⟨y,hy,change⟩
    exact change.elim (fun h => ((values i y hi hy).2 h.1).elim) (fun h => h.2.symm ▸ hy)
  · intro hx
    exact ⟨x,hx,Or.inr ⟨(values i x hi hx).2,rfl⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 迭代轮中的弹性回答与一步扩展器

把同一个 u 从低不可分辨点搬到高点，删除末位后保持全部旧对象。
在低点加三层选择域更大的完整弹性 w，真实超过高处的 dcp(u)，
再调用原一步引理。低处排列不预先固定，整个实际元组保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_renew_l {ω e γ W F δ ν μ κ l n α A c R r B U D P u v b a z χ : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hd : Woodin_d I δ) (hγ : M.IsLimitOrdinal γ) (hW : V_d I γ W) (hwW : M.mem ω W)
    (hδW : M.mem δ W) (pool : Tt_pool_d I ω e W F) (pair : Li_pair_d I ω e W F ν μ)
    (hδν : M.mem δ ν) (hκδ : M.mem κ δ) (succ : M.SuccessorOf n l)
    (height : M.SuccessorOf α ν) (hA : V_d I α A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R n r δ U P u)
    (language : Ee_language_d hZF ω κ l B U D q) (drop : Td_dcp_d I l n D u v)
    (elastic : Ee_elastic_d q v) (last : Rd_entry_d l ν r)
    (values : ∀ i x, M.mem i l → Rd_entry_d i x r → M.mem x W ∧ x ≠ ν)
    (prog : Ts_program_d hZF ω l b σ a z) (hχ : M.mem χ δ) :
    ∃ τ C V Q w η Y d S, ∃ q' : Ee_queries_d M,
      M.mem χ τ ∧ M.mem κ τ ∧ M.mem τ δ ∧ Tg_height_d ν η ∧ V_d I η Y ∧ Smem_d I d Y S ∧
      Ee_language_d hZF ω τ n C V Q q' ∧ Tt_realized_d I ω d Y S n r δ V Q w ∧ Ee_elastic_d q' w ∧
      Tx_exceeds_d hZF ω δ κ l U D v τ n V Q w ∧ Ee_one_step_d hZF ω κ δ l v τ n w b σ z := by
  have woodin := hd
  obtain ⟨ω₀, _, hw₀, hwδ, regular, _⟩ := woodin
  have eq := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hw₀.2 ω hω.1 x, hω.2 ω₀ hw₀.1 x⟩)
  subst ω₀
  obtain ⟨one, h1, hw1⟩ := hω.1.2 e heω
  obtain ⟨two, h2, hw2⟩ := hω.1.2 one hw1
  obtain ⟨three, h3, hw3⟩ := hω.1.2 two hw2
  have zero : M.IsOrdinalAddition I ν ν e := (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl
  have add1 := (ZF.ordinalAddition_successor_iff hZF I (Structure.IsOrdinal.of_no_members he) h1).mpr ⟨ν, zero, height⟩
  obtain ⟨β, ob, step2⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) (v_ordinal_l I hA)
  have add2 := (ZF.ordinalAddition_successor_iff hZF I (hω.members_areOrdinals (ZF.modelsKP hZF) one hw1) h2).mpr ⟨α, add1, step2⟩
  have βδ := ob.transitive α step2.predecessor_mem δ ((height δ).mpr (Or.inl hδν))
  obtain ⟨ω', _, Z, η, Y, _, _, d, S, hw', _, hZ, step3, hY, _, lower, choose⟩ :=
    woodin_elastic_l hZFC hd ob βδ
  have eq := hZF.1.eq_of_same_members ω' ω (fun x => ⟨hw'.2 ω hω.1 x, hω.2 ω' hw'.1 x⟩)
  subst ω'
  have add3 := (ZF.ordinalAddition_successor_iff hZF I (hω.members_areOrdinals (ZF.modelsKP hZF) two hw2) h3).mpr ⟨β, add2, step3⟩
  have below := pair.finite_gap_l hZF hω he heω hW hwW pool hw3 add3
  -- 只搬动末位；低处的每个旧对象都落在共同参数带中并与 ν 不同。
  obtain ⟨α',A',c',R',s',highsucc,hA',upper,small,kept⟩ := pair.raise_prefix_l hZF hω he heω
    regular.isLimitOrdinal hwδ hγ hW hδW pool hκδ language.rank language.constants language.pool
    succ height hA model type drop last values
  obtain ⟨η', _, hsη⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) (v_ordinal_l I hY)
  have gap' : M.mem η' α' := by
    exact ordinal_down_l (ZF.modelsKP hZF) (KP.successor_isOrdinal (ZF.modelsKP hZF) (v_ordinal_l I hY) hsη)
      (v_ordinal_l I hA') (b := μ) (fun t ht => ((hsη t).mp ht).elim
        (pair.2.1.transitive η below t) (fun eq => (hZF.1.eq_of_same_members t η eq).symm ▸ below)) highsucc.predecessor_mem
  have targetTuple := type.tuple.mono_target_l (ZF.v_mono_l I hZF hA hZ (fun x hx => (step2 x).mpr (Or.inl hx)))
  have bound : ∃ ξ, M.mem ξ δ ∧ (χ = ξ ∨ M.mem χ ξ) ∧ (κ = ξ ∨ M.mem κ ξ) := by
    rcases regular.isCardinal.1.wellOrder.linear.compare χ hχ κ hκδ with eq | lt | gt
    · exact ⟨κ, hκδ, Or.inl (hZF.1.eq_of_same_members χ κ eq), Or.inl rfl⟩
    · exact ⟨κ, hκδ, Or.inr lt, Or.inl rfl⟩
    · exact ⟨χ, hχ, Or.inl rfl, Or.inr gt⟩
  obtain ⟨ξ, hξ, χξ, κξ⟩ := bound
  obtain ⟨τ, _, _, C, V, Q, q', _, w, hξτ, hτδ, hτ, _, lang, _, realized, _, el⟩ :=
    choose n r type.finite targetTuple ξ hξ
  have κτ := κξ.elim (fun eq => eq.symm ▸ hξτ) (hτ.1.transitive ξ hξτ κ)
  have witness : Ts_at_d hZF ω δ l s' n V Q w η :=
    ts_at_prefix_l hZF hω hY lower realized (fun i hi => (succ i).mpr (Or.inl hi)) kept
  have exceeds : Tx_exceeds_d hZF ω δ κ l U D v τ n V Q w :=
    ⟨κτ, fun i hi => (succ i).mpr (Or.inl hi), α', A', c', R', s', hA', upper, small, η, η', hsη, gap', witness⟩
  exact ⟨τ, C, V, Q, w, η, Y, d, S, q', χξ.elim (fun eq => eq.symm ▸ hξτ) (hτ.1.transitive ξ hξτ χ),
    κτ, hτδ, ⟨α, β, height, step2, step3⟩, hY, lower, lang, realized, el, exceeds,
    ee_one_step_l hZFC hω prog language hτ hτδ lang.rank lang.constants elastic exceeds⟩

end YesMetaZFC.SetTheory.LargeCardinal
