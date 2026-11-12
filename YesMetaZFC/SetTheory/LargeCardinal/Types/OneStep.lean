import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SubtypeStretch
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax
import YesMetaZFC.SetTheory.Card.Cofinality.OmegaAddition

/-! # 从可实现弹性类型自动提取伸展数据

实现高度不预设为后继，δ 的不可达性也不外加。二者均由原查询读取；
随后实际构造 Vδ 的源实例，返回同一元组的前驱类型及全部高度的扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_language_d.realized_l {ω κ n B U D δ η Y c S s t : M.Domain} {q : Ee_queries_d M}
    (language : Ee_language_d hZF ω κ n B U D q) (hω : M.IsOmega ω) (hk : M.mem κ δ)
    (hY : V_d I η Y) (model : Smem_d I c Y S) (type : Tt_realized_d I ω c Y S n s δ U D t)
    (elastic : Ee_elastic_d q t) :
    M.mem ω δ ∧ M.IsRegularCardinal I δ ∧ M.IsStrongLimitCardinal I δ ∧
      ∃ ν A X K R b Q w, M.SuccessorOf η ν ∧ V_d I ν A ∧ V_d I δ X ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R ∧
        Smem_d I b A Q ∧ Ee_minus_d I ω D q t w ∧ Tt_realized_d I ω b A Q n s δ U D w ∧
          ∀ τ, M.mem τ δ → Ee_step_d hZF ω κ δ n s b X R w τ := by
  have inacc := (language.inaccessible c Y S s δ t model type).mp elastic.2.1
  obtain ⟨above, regular, strong⟩ := sc_v_inaccessible_read_l hZF hY inacc
  obtain ⟨ν, succ⟩ := (language.successor η Y c S s δ t hY model type).mp elastic.1.1
  obtain ⟨A, hA⟩ := ZF.v_exists_l I hZF ((v_ordinal_l I hY).mem succ.predecessor_mem)
  obtain ⟨X, hX⟩ := ZF.v_exists_l I hZF regular.1.1
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨R, source⟩ := ep_regular_source_l hZFC hω above regular hX hk (hω.subset_limitOrdinal (ZF.modelsKP hZF) language.limit) hK
  obtain ⟨_, b, Q, w, lower, minus, realized, all⟩ :=
    (language.read hZFC ν η A Y X c S δ K R s t hA hY succ hX regular.isLimitOrdinal above hk source model type).mp elastic
  exact ⟨above, regular, strong, ν, A, X, K, R, b, Q, w, succ, hA, hX, source, lower, ⟨elastic.1, minus⟩, realized, all⟩

/-- 同一实际完整类型的弹性与查询编译的选择无关，可直接接入开局时固定的表。 -/
theorem Ee_language_d.elastic_transfer_l {ω κ n B U D δ η Y c R s t : M.Domain} {q q' : Ee_queries_d M}
    (source : Ee_language_d hZF ω κ n B U D q) (target : Ee_language_d hZF ω κ n B U D q')
    (hω : M.IsOmega ω) (hk : M.mem κ δ) (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n s δ U D t) (elastic : Ee_elastic_d q t) : Ee_elastic_d q' t := by
  obtain ⟨above, regular, _, ν, A, X, K, S, b, Q, w, succ, hA, hX, base, lower, minus, realized, all⟩ :=
    source.realized_l hZFC hω hk hY model type elastic
  exact (target.read hZFC ν η A Y X c R δ K S s t hA hY succ hX regular.isLimitOrdinal above hk base model type).mpr
    ⟨(source.inaccessible c Y R s δ t model type).mp elastic.2.1, b, Q, w, lower, minus.2, realized, all⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## Neeman 引理 3.23：弹性类型的一步伸展

超过关系提供高低两个实际实现及原有的任意有限排列。弹性在前驱层给出
同一扩展器的伸展；子类型的固定查询随后从前驱像上升到原类型像。
投影高度仍为实际的 τ+ω；同一构造允许支撑高于任意指定的 χ<δ。
先在更高常量域使用弹性，再将同一次超幂的类型限制回原投影域。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 任意 χ<δ 均有支撑更高的一步伸展，投影域和原子类型程序保持不变。 -/
def Ee_one_step_d (hZF : M.Models ZF) (ω κ δ n u τ m w b : M.Domain)
    (σ : Fin 7 → M.Domain) (z : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∀ χ, M.mem χ δ → ∃ ℓ X K R L F B U D v,
    M.IsOrdinalAddition I ℓ τ ω ∧ M.IsLimitOrdinal ℓ ∧ M.mem τ ℓ ∧ M.mem ℓ δ ∧
    V_d I δ X ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R ∧ M.mem L δ ∧ M.mem κ L ∧ M.mem ℓ L ∧ M.mem χ L ∧
    It_local_d I ω X R κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F ∧
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
  intro χ hχ
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
  -- 投影域保持 τ+ω，扩展器则在同时覆盖 χ 的高度选择。
  obtain ⟨ℓ, sum, hℓ, hτℓ, hℓδ, _⟩ := ZF.oa_omega_bound_l hZF I hω regular.isLimitOrdinal regular hwδ hτδ
  obtain ⟨ζ, hζδ, hℓζ, hχζ⟩ : ∃ ζ, M.mem ζ δ ∧
      (ℓ = ζ ∨ M.mem ℓ ζ) ∧ (χ = ζ ∨ M.mem χ ζ) := by
    rcases regular.isCardinal.1.wellOrder.linear.compare ℓ hℓδ χ hχ with eq | lt | gt
    · exact ⟨χ, hχ, Or.inl (hZF.1.eq_of_same_members ℓ χ eq), Or.inl rfl⟩
    · exact ⟨χ, hχ, Or.inr lt, Or.inl rfl⟩
    · exact ⟨ℓ, hℓδ, Or.inl rfl, Or.inr gt⟩
  obtain ⟨L, F, B₂, U₂, D₂, v₂, hLδ, hκL, hζL, hB₂, constants₂, pool₂,
    truth₂, loc, inaccessible, strength, stretch₂⟩ := all ζ hζδ
  have hL := regular.isCardinal.1.mem hLδ
  have hℓL := hℓζ.elim (fun eq => eq.symm ▸ hζL) (hL.transitive ζ hζL ℓ)
  have hχL := hχζ.elim (fun eq => eq.symm ▸ hζL) (hL.transitive ζ hζL χ)
  obtain ⟨B₁, U₁, hB₁, _, constants₁⟩ := tt_constants_exists_l hZF hX regular.isLimitOrdinal hℓδ
  obtain ⟨D₁, pool₁⟩ := tt_pool_exists_l I hZF hω n U₁
  have sub : M.MemberSubset U₁ U₂ := by
    intro x hx
    rcases (constants₁ x).mp hx with hx | eq
    · exact (constants₂ x).mpr (Or.inl (ZF.v_mono_l I hZF hB₁ hB₂
        (hℓζ.elim (fun eq => eq ▸ fun _ h => h) (fun lt => (regular.isCardinal.1.mem hζδ).transitive ℓ lt)) x hx))
    · subst x
      exact (constants₂ ℓ).mpr (hℓζ.elim Or.inr (fun lt => Or.inl (ZF.v_ordinal_mem_l I hZF hB₂ lt)))
  have subD := pool₁.mono_l I pool₂ sub
  obtain ⟨v₀, truth₁, _⟩ := tt_truth_exists_l I hZF ω c₀ n s δ D₁
  have projection := truth₁.project_l I truth₂ subD
  have stretch : Et_stretch_d hZF ω κ L F X R u₀ D₁ v₀ := by
    obtain ⟨c, d, N, S, j, u', mx, my, ultra, image, cut⟩ := stretch₂
    refine ⟨c, d, N, S, j, u', mx, my, ultra, image, fun p => ?_⟩
    exact (projection p).trans ⟨fun h => ⟨h.1, ((cut p).mp h.2).2⟩,
      fun h => ⟨h.1, (cut p).mpr ⟨subD p h.1, h.2⟩⟩⟩
  have hwX := ZF.v_ordinal_mem_l I hZF hX hwδ
  have hUX := tt_constants_rank_l hZF hX regular.isLimitOrdinal hκδ language.rank language.constants
  have hDX := language.pool.rank_mem_l (ZF.modelsKP hZF) hω hX regular.isLimitOrdinal hwX type.finite hUX
  have hU₁X := tt_constants_rank_l hZF hX regular.isLimitOrdinal hℓδ hB₁ constants₁
  have hXA := ZF.v_mono_l I hZF hX hA ((v_ordinal_l I hA).transitive δ
    (ZF.v_ordinal_height_l hZF hA regular.isCardinal.1 original.point))
  have realized : Tt_realized_d I ω c₀ A S₀ n s δ U₁ D₁ v₀ :=
    ⟨lower.1, type.finite, original.tuple, original.point,
      fun x hx => hXA x ((v_transitive_l I hX) U₁ hU₁X x hx), pool₁, truth₁⟩
  have subtype := (ts_subtype_realized_l hZF hω prog hA lower realized hℓ hτ hτℓ small.1
    hB₁ constants₁ hC constants small.2.1 small.2.2).mpr ⟨nm, ν, hνη, hw⟩
  -- 搬运固定查询，而非仅以两个类型共享实现元组代替子类型成员关系。
  obtain ⟨v, stretched, subtype⟩ := stretch.subtype_l hZF hω hX regular.isLimitOrdinal hwX hUX hDX
    prog minus.2 hA hY succ lower upper type original.tuple original.point original.constants subtype
  exact ⟨ℓ, X, K, R, L, F, B₁, U₁, D₁, v, sum, hℓ, hτℓ, hℓδ,
    hX, source, hLδ, hκL, hℓL, hχL, loc, inaccessible, strength, hB₁, constants₁, pool₁, stretched, subtype⟩

end YesMetaZFC.SetTheory.LargeCardinal
