import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticRead
import YesMetaZFC.SetTheory.LargeCardinal.SubtypeStretch
import YesMetaZFC.Model.SetTheory.Internal.TypeExceeds
import YesMetaZFC.SetTheory.Card.Cofinality.OmegaAddition

/-! # Neeman 引理 3.23：弹性类型的一步伸展

超过关系提供高低两个实际实现及原有的任意有限排列。弹性在前驱层给出
同一扩展器的伸展；子类型的固定查询随后从前驱像上升到原类型像。
投影高度为实际的 τ+ω，源与最大强度在证明中构造，原编译程序保持不变。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 一步构造保留事先固定的子类型程序；伸展与成员判断共享同一查询域。 -/
def Ee_one_step_d (hZF : M.Models ZF) (ω κ δ n u τ m w b : M.Domain)
    (σ : Fin 7 → M.Domain) (z : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ ℓ X K R L F B U D v,
    M.IsOrdinalAddition I ℓ τ ω ∧ M.IsLimitOrdinal ℓ ∧ M.mem τ ℓ ∧ M.mem ℓ δ ∧
    V_d I δ X ∧ Ep_source_d hZF ω κ K X R ∧ M.mem L δ ∧ M.mem κ L ∧ M.mem ℓ L ∧
    It_local_d ω X κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d hZF ω κ L X F ∧
    V_d I ℓ B ∧ (∀ x, M.mem x U ↔ M.mem x B ∨ x = ℓ) ∧ Tt_pool_d I ω n U D ∧
    Et_stretch_d hZF ω κ L F X R u D v ∧ Ts_subtype_d ω n ℓ τ m U w b σ z v

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 弹性与超过关系自动产生一步伸展；不预设 δ 不可达、源模型或扩展器。 -/
theorem ee_one_step_l {ω κ δ n m B U D u τ C V W w b a z : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (prog : Ts_program_d hZF ω n b σ a z)
    (language : Ee_language_d hZF ω κ n B U D q)
    (hτ : M.IsLimitOrdinal τ) (hτδ : M.mem τ δ)
    (hC : V_d I τ C) (constants : ∀ x, M.mem x V ↔ M.mem x C ∨ x = τ)
    (elastic : Ee_elastic_d q u) (exceeds : Tx_exceeds_d hZF ω δ κ n U D u τ m V W w) :
    Ee_one_step_d hZF ω κ δ n u τ m w b σ z := by
  obtain ⟨hκτ, nm, η, Y, c, S, s, hY, upper, type, ν, μ, next, gap, hw⟩ := exceeds
  have inacc := (language.inaccessible c Y S s δ u upper type).mp elastic.2.1
  have ⟨_, regular, _⟩ := sc_v_inaccessible_read_l hZF hY inacc
  have hκδ := regular.isCardinal.1.transitive τ hτδ κ hκτ
  obtain ⟨hwδ, regular, _, η₀, A, X, K, R, c₀, S₀, u₀, succ, hA, hX, source,
    lower, minus, original, all⟩ := language.realized_l hZFC hω hκδ hY upper type elastic
  -- ν+1<η₀+1 给出 ν<η₀，保留超过见证中的原元组及排列。
  have hνη : M.mem ν η₀ := by
    rcases (succ μ).mp gap with lt | eq
    · exact (v_ordinal_l I hA).transitive μ lt ν next.predecessor_mem
    · exact (eq ν).mp next.predecessor_mem
  have small : M.mem m ω ∧ Tt_pool_d I ω m V W ∧ M.MemberSubset w W := by
    obtain ⟨_, _, _, _, _, _, _, _, _, realized, _⟩ := hw
    exact ⟨realized.finite, realized.pool, fun p hp => ((realized.truth p).mp hp).1⟩
  -- δ 的正则性保证 τ+ω<δ；弹性随后在这个确切高度选择扩展器。
  obtain ⟨ℓ, sum, hℓ, hτℓ, hℓδ⟩ := ZF.oa_omega_bound_l hZF I hω regular.isLimitOrdinal regular hwδ hτδ
  obtain ⟨L, F, B₁, U₁, D₁, v₀, hLδ, hκL, hℓL, hB₁, constants₁, pool₁,
    truth₁, loc, inaccessible, strength, stretch⟩ := all ℓ hℓδ
  have hwX := ZF.v_ordinal_mem_l I hZF hX hwδ
  have hUX := tt_constants_rank_l hZF hX regular.isLimitOrdinal hκδ language.rank language.constants
  have hDX := language.pool.rank_mem_l hZF hω hX regular.isLimitOrdinal hwX type.finite hUX
  have hU₁X := tt_constants_rank_l hZF hX regular.isLimitOrdinal hℓδ hB₁ constants₁
  have hXA := ZF.v_mono_l I hZF hX hA ((v_ordinal_l I hA).transitive δ
    (ZF.v_ordinal_height_l hZF hA regular.isCardinal.1 original.point))
  have realized : Tt_realized_d I ω c₀ A S₀ n s δ U₁ D₁ v₀ :=
    ⟨lower.1, type.finite, original.tuple, original.point,
      fun x hx => hXA x ((ZF.v_transitive_l I hZF hX) U₁ hU₁X x hx), pool₁, truth₁⟩
  have subtype := (ts_subtype_realized_l hZF hω prog hA lower realized hℓ hτ hτℓ small.1
    hB₁ constants₁ hC constants small.2.1 small.2.2).mpr ⟨nm, ν, hνη, hw⟩
  -- 搬运固定查询，而非仅以两个类型共享实现元组代替子类型成员关系。
  obtain ⟨v, stretched, subtype⟩ := stretch.subtype_l hZF hω hX regular.isLimitOrdinal hwX hUX hDX
    prog minus.2 hA hY succ lower upper type original.tuple original.point original.constants subtype
  exact ⟨ℓ, X, K, R, L, F, B₁, U₁, D₁, v, sum, hℓ, hτℓ, hℓδ,
    hX, source, hLδ, hκL, hℓL, loc, inaccessible, strength, hB₁, constants₁, pool₁, stretched, subtype⟩

end YesMetaZFC.SetTheory.LargeCardinal
