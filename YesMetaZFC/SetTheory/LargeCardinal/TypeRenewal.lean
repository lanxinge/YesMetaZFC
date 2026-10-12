import YesMetaZFC.SetTheory.LargeCardinal.LocalIndiscerniblesGap
import YesMetaZFC.SetTheory.LargeCardinal.LocalTypeTransportTuple
import YesMetaZFC.SetTheory.LargeCardinal.TypeOneStep
import YesMetaZFC.SetTheory.LargeCardinal.WoodinTypes
import YesMetaZFC.Model.SetTheory.Internal.TypeDrop
import YesMetaZFC.Model.SetTheory.Internal.TypeGameHeight

/-! # 迭代轮中的弹性回答与一步扩展器

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
  obtain ⟨Cδ, hcδ⟩ := ZF.v_exists_l I hZF regular.isCardinal.1
  obtain ⟨one, h1, hw1⟩ := hω.1.2 e heω
  obtain ⟨two, h2, hw2⟩ := hω.1.2 one hw1
  obtain ⟨three, h3, hw3⟩ := hω.1.2 two hw2
  have zero : M.IsOrdinalAddition I ν ν e := (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl
  have add1 := (ZF.ordinalAddition_successor_iff hZF I (Structure.IsOrdinal.of_no_members he) h1).mpr ⟨ν, zero, height⟩
  obtain ⟨β, ob, step2⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) (v_ordinal_l I hA)
  have add2 := (ZF.ordinalAddition_successor_iff hZF I (hω.members_areOrdinals hZF one hw1) h2).mpr ⟨α, add1, step2⟩
  have βδ := ob.transitive α step2.predecessor_mem δ ((height δ).mpr (Or.inl hδν))
  obtain ⟨ω', _, Z, η, Y, _, _, d, S, hw', _, hZ, step3, hY, _, lower, choose⟩ :=
    woodin_elastic_l hZFC hd ob βδ
  have eq := hZF.1.eq_of_same_members ω' ω (fun x => ⟨hw'.2 ω hω.1 x, hω.2 ω' hw'.1 x⟩)
  subst ω'
  have add3 := (ZF.ordinalAddition_successor_iff hZF I (hω.members_areOrdinals hZF two hw2) h3).mpr ⟨β, add2, step3⟩
  have below := pair.finite_gap_l hZF hω he heω hW hwW pool hw3 add3
  -- 只搬动末位；低处的每个旧对象都落在共同参数带中并与 ν 不同。
  obtain ⟨α', A', c', R', r', add', hA', upper, move, type'⟩ := pair.transport_l hZF hω he heω
    regular.isLimitOrdinal hwδ hγ hW hδW pool hκδ hw1 h1.predecessor_mem add1 hA model hcδ language.rank language.constants type (by
      intro i x hx
      rcases (succ i).mp (type.tuple.bound_l hx).1 with hi | eq
      · exact Or.inr (values i x hi hx).1
      · exact Or.inl (type.tuple.2.2 l succ.predecessor_mem x (type.tuple.bound_l hx).2 ν
          (type.tuple.bound_l last).2 (hZF.1.eq_of_same_members i l eq ▸ hx) last))
  obtain ⟨s', v', cut, drop', small⟩ := type'.dcp_l hZF hω succ language.pool
  have eqv := drop.2.unique_l I hZF.1 drop'.2
  subst v'
  have kept i x (hi : M.mem i l) : Rd_entry_d i x s' ↔ Rd_entry_d i x r := by
    refine (cut.2 i x).trans ((and_iff_right hi).trans ?_)
    refine (move i x).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy, change⟩
      exact change.elim (fun h => ((values i y hi hy).2 h.1).elim) (fun h => h.2.symm ▸ hy)
    · intro hx
      exact ⟨x, hx, Or.inr ⟨(values i x hi hx).2, rfl⟩⟩
  obtain ⟨η', _, hsη⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) (v_ordinal_l I hY)
  have gap' : M.mem η' α' := by
    obtain ⟨v₀, hv₀, highsucc⟩ := (ZF.ordinalAddition_successor_iff hZF I (Structure.IsOrdinal.of_no_members he) h1).mp add'
    have eq := (ZF.ordinalAddition_zero_iff hZF I he).mp hv₀
    subst v₀
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
  obtain ⟨Y', d', S', r₀, f, g, π, hY', mdl, real, ff, fg, graph, orig, bij, perm⟩ := ts_at_self_l hZF hω hY lower realized
  have witness : Ts_at_d hZF ω δ l s' n V Q w η :=
    ⟨Y', d', S', r₀, f, g, π, hY', mdl, real, ff, fg, graph,
      fun i x hi => (kept i x hi).trans (orig i x ((succ i).mpr (Or.inl hi))), bij, perm⟩
  have exceeds : Tx_exceeds_d hZF ω δ κ l U D v τ n V Q w :=
    ⟨κτ, fun i hi => (succ i).mpr (Or.inl hi), α', A', c', R', s', hA', upper, small, η, η', hsη, gap', witness⟩
  exact ⟨τ, C, V, Q, w, η, Y, d, S, q', χξ.elim (fun eq => eq.symm ▸ hξτ) (hτ.1.transitive ξ hξτ χ),
    κτ, hτδ, ⟨α, β, height, step2, step3⟩, hY, lower, lang, realized, el, exceeds,
    ee_one_step_l hZFC hω prog language hτ hτδ lang.rank lang.constants elastic exceeds⟩

end YesMetaZFC.SetTheory.LargeCardinal
