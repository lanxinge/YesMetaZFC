import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticQuery
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.Model.SetTheory.Types.SubtypeLift

/-! # 子类型从前驱伸展提升到原类型伸展

保留同一扩展器和实际超幂，只把前驱集合的像换成原类型的像。
唯一查询码原样进入新投影，故结论仍是定义 3.6 的原成员性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Et_stretch_d.subtype_l {ω θ κ L F X R n U D t t₀ E v b a z : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hUX : M.mem U X) (hDX : M.mem D X) {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (minus : Tm_minus_d I ω D t t₀)
    {ν μ A Y c₀ R₀ d₀ S₀ s δ : M.Domain} (hA : V_d I ν A) (hY : V_d I μ Y) (hs : M.SuccessorOf μ ν)
    (lower : Smem_d I c₀ A R₀) (upper : Smem_d I d₀ Y S₀) (type : Tt_realized_d I ω d₀ Y S₀ n s δ U D t)
    (tuple : Fn0_d n A s) (point : M.mem δ A) (constants : M.MemberSubset U A)
    (h : Et_stretch_d hZF ω κ L F X R t₀ E v)
    {ℓ τ m U₀ w : M.Domain} (subtype : Ts_subtype_d ω n ℓ τ m U₀ w b σ z v) :
    ∃ v', Et_stretch_d hZF ω κ L F X R t E v' ∧ Ts_subtype_d ω n ℓ τ m U₀ w b σ z v' := by
  obtain ⟨c, d, Z, S, j, t₀', hm, hn, ultra, ht₀, cut⟩ := h
  have hj := ultra.elementary_l hZF hm.1 hn.1
  have hZ := ultra.transitive_l hZF hn.1
  have htX := v_subset_mem_l I hX hDX (fun p hp => ((type.truth p).mp hp).1)
  obtain ⟨t', _, htt⟩ := hj.1.1.2.2 t htX
  obtain ⟨D', _, hDD⟩ := hj.1.1.2.2 D hDX
  obtain ⟨hτ, nm, q, code, hq⟩ := subtype
  have omega : ∃ C H, KPair_d M q z C ∧ Fn0_d b H C ∧ ∃ e, KPair_d M e ω ω ∧ Rd_entry_d (σ 6) e C := by
    obtain ⟨_, N, C, v, _, column, _, params, vals, pair⟩ := code
    exact ⟨C, N, pair, column, v 6, vals.2.2.2.2.2.2, params 6⟩
  obtain ⟨C, H, pair, column, omega⟩ := omega
  have raised := hj.subtype_minus_l hZF hω hX hθ hωX hZ hm hn prog hUX hDD htt ht₀ minus
    hA hY hs lower upper type tuple point constants pair column omega ((cut q).mp hq).2
  let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => t', fun _ => t'⟩
  obtain ⟨v', sep⟩ := ZF.separation_exists_d hZF φ ρ E
  have cut' p : M.mem p v' ↔ M.mem p E ∧ M.mem p t' := sep p
  exact ⟨v', ⟨c, d, Z, S, j, t', hm, hn, ultra, htt, cut'⟩,
    hτ, nm, q, code, (cut' q).mpr ⟨((cut q).mp hq).1, raised⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
