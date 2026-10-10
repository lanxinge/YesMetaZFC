import YesMetaZFC.SetTheory.FlatPairing.RecursionSource
import YesMetaZFC.SetTheory.FlatPairing.RankObjects
import YesMetaZFC.SetTheory.CumulativePairing
import YesMetaZFC.SetTheory.CumulativeRelative
import YesMetaZFC.SetTheory.FunctionRecoding

/-! # 后继秩层中的完整累积层级

平坦历史只保存严格较早层，故历史及其每个限制都属于当前后继层。
向上读取时重编码同一历史，直接复用已有的相对幂集递归比较证明。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY

/-- 相对历史由实际图拥有；比较不要求源内拥有重编码后的辅助图。 -/
theorem rt_fp_v_up_l {ν X : M.Domain} (hV : V_d I ν X) (hs : M.SuccessorOf μ ν)
    (α A : (N).Domain) (h : V_d J α A) : V_d Q α.val A.val := by
  have trans := ZF.v_transitive_l I hZF hW
  have pow := ZF.v_successor_l I hZF hV hW hs
  have hXY := (pow X).mpr (fun _ h => h)
  have entry := rt_fp_entry_l I hZF hω hW hωY
  obtain ⟨F, history, root⟩ := h
  have ho := (rt_ordinal_iff_l trans (Nonempty.intro (Subtype.mk ω hωY)) (ZF.modelsKP hZF) α).mp history.1.1
  have dom := (rt_fp_domain_l I hZF hω hW hωY α F).mp history.1.2.2
  have values x y (hxy : M.PairMember K x y F.val) : M.mem y X := by
    obtain ⟨p, cp, hp⟩ := hxy
    exact (((fp_fixed_l hZF.1 hω).mp cp).inverse_rank_l I hZF hω.1 hV ((pow F.val).mp F.property p hp)).2
  have fn : M.IsSetFunctionFromTo K F.val α.val X :=
    ⟨(rt_fp_function_l I hZF hω hW hωY F).mp history.1.2.1, dom,
      fun x hx => ((dom x).mp hx).imp fun y hy => ⟨values x y hy, hy⟩⟩
  obtain ⟨G, graph, recode⟩ := fn_recode_l K Q hZF fn
  have read (a P W : (N).Domain)
      (cut : ∀ x y, (N).PairMember J x y P ↔ (N).mem x a ∧ (N).PairMember J x y F)
      (step : V_step_d J P W) (t : M.Domain) (ht : M.mem t Y) : Vc_step_d a.val X G W.val t := by
    refine (step ⟨t, ht⟩).trans ⟨?_, ?_⟩
    · rintro ⟨x, U, hx, sub⟩
      obtain ⟨ha, hF⟩ := (cut x U).mp hx
      have hF' := (entry x U F).mp hF
      exact ⟨x.val, ha, U.val, values x.val U.val hF', (recode x.val U.val).mpr hF',
        fun z hz => sub ⟨z, trans t ht z hz⟩ hz⟩
    · rintro ⟨x, hx, U, hU, he, sub⟩
      let x' : (N).Domain := ⟨x, trans a.val a.property x hx⟩
      let U' : (N).Domain := ⟨U, trans X hXY U hU⟩
      exact ⟨x', U', (cut x' U').mpr ⟨hx, (entry x' U' F).mpr ((recode x U).mp he)⟩,
        fun z hz => sub z.val hz⟩
  obtain ⟨V, hv⟩ := ZF.v_exists_l Q hZF ho
  have hα := ZF.v_ordinal_height_l hZF hW ho α.property
  have hvY := ZF.v_mem_l I hZF ((v_pairing_l Q I hZF).mp hv) hW hα
  have eq := vr_compare_l hZF trans hXY (fn0_of_function_l (ZF.modelsKP hZF) graph)
    (fun _ h => h) A.property hv (trans V hvY) (fun β hβ U he => by
      let β' : (N).Domain := ⟨β, trans α.val α.property β hβ⟩
      let U' : (N).Domain := ⟨U, trans X hXY U (graph.output_mem_of_pairMember he)⟩
      obtain ⟨P, cut, step⟩ := history.2 β' hβ U' ((entry β' U' F).mpr ((recode β U).mp he))
      exact read β' P U' cut.2 step)
    (read α F A (fun x y => ⟨fun h => ⟨(history.1.2.2 x).mpr ⟨y, h⟩, h⟩, And.right⟩) root)
  exact eq ▸ hv

/-- 每个真实层的平坦历史及全部初段实际属于当前后继层。 -/
theorem rt_fp_v_down_l {ν X : M.Domain} (hV : V_d I ν X) (hs : M.SuccessorOf μ ν)
    (α A : (N).Domain) (h : V_d Q α.val A.val) : V_d J α A := by
  have trans := ZF.v_transitive_l I hZF hW
  have pow := ZF.v_successor_l I hZF hV hW hs
  have hXY := (pow X).mpr (fun _ h => h)
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have hων : M.MemberSubset ω ν := by
    rcases (hs ω).mp (ZF.v_ordinal_height_l hZF hW (hω.isOrdinal hZF) hωY) with lt | eq
    · exact (v_ordinal_l I hV).transitive ω lt
    · exact fun x hx => (eq x).mp hx
  have ho := v_ordinal_l Q h
  have hαμ := ZF.v_ordinal_height_l hZF hW ho α.property
  have hαν : M.MemberSubset α.val ν := by
    rcases (hs α.val).mp hαμ with hα | hα
    · exact (v_ordinal_l I hV).transitive α.val hα
    · exact fun x hx => (hα x).mp hx
  have hK := (v_pairing_l Q K hZF).mp h
  obtain ⟨F, history, root⟩ := hK
  have fn : M.IsSetFunctionFromTo K F α.val X := ⟨history.1.2.1, history.1.2.2, fun β hβ => by
    obtain ⟨U, he⟩ := (history.1.2.2 β).mp hβ
    exact ⟨U, ZF.v_mem_l I hZF ((v_pairing_l K I hZF).mp (history.recursionValue_of_pairMember hβ he))
      hV (hαν β hβ), he⟩⟩
  have hFX := fp_function_rank_l I hZF hω hV hων
    (fun β hβ => ZF.v_ordinal_mem_l I hZF hV (hαν β hβ)) fn
  let F' : (N).Domain := ⟨F, (pow F).mpr hFX⟩
  have fn' := (rt_fp_function_from_l I hZF hω hW hωY F' α ⟨X, hXY⟩).mpr fn
  have step (P W : (N).Domain) (hp : V_step_d K P.val W.val) : V_step_d J P W := by
    intro t
    refine (hp t.val).trans ⟨?_, ?_⟩
    · rintro ⟨β, U, he, sub⟩
      have own := rt_fp_coordinates_l I hZF hω hW P.property he
      exact ⟨⟨β, own.1⟩, ⟨U, own.2⟩, (entry _ _ P).mpr he, fun z hz => sub z.val hz⟩
    · rintro ⟨β, U, he, sub⟩
      exact ⟨β.val, U.val, (entry β U P).mp he, fun z hz => sub ⟨z, trans t.val t.property z hz⟩ hz⟩
  refine ⟨F', ⟨⟨rt_ordinal_l trans (Nonempty.intro (Subtype.mk ω hωY)) α ho, fn'.1, fn'.2.1⟩, ?_⟩,
    step F' A root⟩
  intro β hβ U he
  obtain ⟨P, cut, hP⟩ := history.2 β.val hβ U.val ((entry β U F').mp he)
  have hPX : M.MemberSubset P X := by
    intro p hp
    obtain ⟨x, y, cp⟩ := cut.1 p hp
    exact hFX p (history.1.2.1.1.mem_iff_pairMember.mpr ⟨x, y, cp, ((cut.2 x y).mp ⟨p, cp, hp⟩).2⟩)
  let P' : (N).Domain := ⟨P, (pow P).mpr hPX⟩
  exact ⟨P', (rt_fp_restriction_l I hZF hω hW hωY P' F' β).mpr cut, step P' U hP⟩

theorem rt_fp_v_l {ν X : M.Domain} (hV : V_d I ν X) (hs : M.SuccessorOf μ ν)
    (α A : (N).Domain) : V_d J α A ↔ V_d Q α.val A.val :=
  ⟨rt_fp_v_up_l I hZF hω hW hωY hV hs α A, rt_fp_v_down_l I hZF hω hW hωY hV hs α A⟩

end YesMetaZFC.SetTheory.Internal
