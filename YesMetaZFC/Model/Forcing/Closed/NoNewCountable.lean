import YesMetaZFC.Model.Forcing.Closed.NoNewFunctions
import YesMetaZFC.Model.Forcing.Internal.Extension.ZF
import YesMetaZFC.SetTheory.FunctionRetraction

/-! # 可数闭扩张中旧集合的可数子集全部来自地模型

非空可数集的单射给出带默认值的枚举；反射该枚举，再取地模型中的实际值域。
这同时返回旧子集、内部可数性和精确的嵌入等式。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hU : Generic_d M B R z U)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
include O hU

/-- 扩张内部可数的旧集合子集，恰好是一个地模型内部可数子集的像。 -/
theorem no_new_countable_l {ω b X} (hω : M.IsOmega ω) (hc : Closed_d I B R z ω) (hb : U b)
    (e : M.Domain → (E).Domain) (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y)
    {Y : (E).Domain} (hY : (E).MemberSubset Y (e X)) (hy : (E).CardinalLessOrEqual J Y (e ω)) :
    ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ e A = Y := by
  classical
  by_cases hn : ∃ y, y ∈ Y
  · obtain ⟨y, hyY⟩ := hn
    obtain ⟨g, hg⟩ := hy
    obtain ⟨F, hF, hfg⟩ := ZF.injection_retract_l J (preserves_zf_l O hZF hU) hg (fun _ h => h) hyY
    have hFX : (E).IsSetFunctionFromTo J F (e ω) (e X) := ⟨hF.1, hF.2.1, fun i hi => by
      obtain ⟨x, hx, hix⟩ := hF.2.2 i hi
      exact ⟨x, hY x hx, hix⟩⟩
    obtain ⟨G, hG, hGF⟩ := no_new_functions_l O hZFC hU hω hc hb e hv he hFX
    obtain ⟨A, hA⟩ := ZF.exists_range_of_setFunction hZF I hG.1 hG.2.1
    have hGA : M.IsSetFunctionFromTo I G ω A := ⟨hG.1, hG.2.1, fun i hi => by
      obtain ⟨x, _, hix⟩ := hG.2.2 i hi
      exact ⟨x, (hA x).mpr ⟨i, hix⟩, hix⟩⟩
    refine ⟨A, (fun x hx => ?_), ZFC.surjection_bound_l I hZFC hGA (fun x hx => ?_), ?_⟩
    · obtain ⟨i, hix⟩ := (hA x).mp hx
      exact hG.output_mem_of_pairMember hix
    · obtain ⟨i, hix⟩ := (hA x).mp hx
      exact ⟨i, hG.input_mem_of_pairMember hix, hix⟩
    · apply (extension_ext_l O hZF hU).eq_of_same_members
      intro x
      constructor
      · intro hx
        obtain ⟨a, ha, rfl⟩ := (he A x).mp hx
        obtain ⟨i, hia⟩ := (hA a).mp ha
        have hiF : Entry_d E (e i) (e a) F := hGF ▸
          (image_entries_l e he hG.1.1 (e i) (e a)).mpr ⟨i, a, hia, rfl, rfl⟩
        exact hF.output_mem_of_pairMember hiF
      · intro hx
        obtain ⟨i, _, hxi⟩ := hg.1.2.2 x hx
        have hiF := hfg x i hxi
        rw [← hGF] at hiF
        obtain ⟨j, a, hja, _, hax⟩ := (image_entries_l e he hG.1.1 i x).mp hiF
        exact (he A x).mpr ⟨a, (hA a).mpr ⟨j, hja⟩, hax⟩
  · obtain ⟨A, hA, _⟩ := hω.1.1
    refine ⟨A, (fun x hx => (hA x hx).elim),
      ZF.exists_inclusionInjection hZF I (fun x hx => (hA x hx).elim), ?_⟩
    apply (extension_ext_l O hZF hU).eq_of_same_members
    intro x
    exact ⟨fun hx => (he A x).mp hx |>.elim fun a ha => (hA a ha.1).elim,
      fun hx => (hn ⟨x, hx⟩).elim⟩

end YesMetaZFC.Model.Forcing.Internal
