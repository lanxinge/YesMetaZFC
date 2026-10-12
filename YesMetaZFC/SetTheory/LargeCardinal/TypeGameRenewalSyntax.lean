import YesMetaZFC.SetTheory.LargeCardinal.TypeGameImageSyntax

/-! # 每轮更新的有限反射句子

这是已证更新定理的同一个原语言句子。全部对象、原查询及程序槽位都由
集合量词绑定；输出仍包含实际扩展器及其超幂，不量化外部构造器或语义谕示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_low0_m : Formula 1 5 :=
  let ω := Term.bound 0; let e := Term.bound 1; let δ := Term.bound 2
  let S := Term.bound 3; let ν := Term.bound 4
  set[5] ⟪∃ ρ θ γ U D μ,
  ⌜rk_m (𝒞 := kpair_convention_l)⌝ₚ(⌜S⌝ₛ, ρ) ∧ ⌜Formula.isOrdinal⌝ₚ(θ) ∧
  (∀ x, x ∈ θ ↔ x ∈ ⌜δ⌝ₛ ∨ x ∈ ρ) ∧ ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(γ, θ, ⌜ω⌝ₛ) ∧
  ⌜v_m kpair_convention_l⌝ₚ(γ, U) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, U, D) ∧
  ⌜li_least_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, U, D, θ, ⌜ν⌝ₛ, μ)⟫
@[simp] theorem tg_low0_closed_l : tg_low0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_low0_m, Definitional.Formula.FreeClosed]

def tg_low_m {d} (ω e δ S ν : Term d) : Formula 1 d :=
  tg_low0_m.bind (fun i => [ω, e, δ, S, ν].get i)

@[simp] theorem tg_low_closed_l {d} (ω e δ S ν : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hd : δ.freeSupport = [])
    (hS : S.freeSupport = []) (hν : ν.freeSupport = []) : (tg_low_m ω e δ S ν).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_low0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, he, hd, hS, hν, fun i => Fin.elim0 i⟩

theorem tg_low_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω e δ S ν : Term d) :
    Formula.satisfies ρ (tg_low_m ω e δ S ν) ↔
      Tg_low_d hZF (ω.eval ρ) (e.eval ρ) (δ.eval ρ) (S.eval ρ) (ν.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [tg_low_m, Formula.satisfies_bind, tg_low0_m, Tg_low_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rk_sat_l I hZF.1, Formula.satisfies_isOrdinal_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isOrdinalAddition_iff I hZF.1, v_sat_l I hZF.1, tt_pool_sat_l I (ZF.modelsKP hZF),
    li_least_sat_l I (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  rfl

/-- 完整实现、原 dcp 弹性和实际树节点是更新的全部输入。 -/
def tg_seed_m {d} (ω e δ S ν κ k l n α A c R r B U D P u v b a z χ s t g
    g₀ g₁ g₂ g₃ σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜e⌝ₛ) ∧ ⌜e⌝ₛ ∈ ⌜ω⌝ₛ ∧
  ⌜woodin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜δ⌝ₛ) ∧ ⌜tg_low_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜δ⌝ₛ, ⌜S⌝ₛ, ⌜ν⌝ₛ) ∧
  ⌜e⌝ₛ ∈ ⌜S⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜δ⌝ₛ ∧ ⌜Formula.isSuccessor⌝ₚ(⌜l⌝ₛ, ⌜k⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ, ⌜l⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜α⌝ₛ, ⌜ν⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜α⌝ₛ, ⌜A⌝ₛ) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜A⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜A⌝ₛ, ⌜R⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜δ⌝ₛ, ⌜U⌝ₛ, ⌜P⌝ₛ, ⌜u⌝ₛ) ∧
  ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜l⌝ₛ, ⌜B⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜g₀⌝ₛ, ⌜g₁⌝ₛ, ⌜g₂⌝ₛ, ⌜g₃⌝ₛ) ∧
  ⌜td_dcp_m⌝ₚ(⌜l⌝ₛ, ⌜n⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ, ⌜v⌝ₛ) ∧ ⌜ee_elastic_m⌝ₚ(⌜g₀⌝ₛ, ⌜g₁⌝ₛ, ⌜g₂⌝ₛ, ⌜g₃⌝ₛ, ⌜v⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, ⌜S⌝ₛ, ⌜r⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜ν⌝ₛ, ⌜r⌝ₛ) ∧
  ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜e⌝ₛ, ⌜l⌝ₛ, ⌜r⌝ₛ, ⌜g⌝ₛ) ∧ ⌜tg_node_m⌝ₚ(⌜k⌝ₛ, ⌜S⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜g⌝ₛ) ∧
  ⌜fun ω l b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω l b a z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜ω⌝ₛ, ⌜l⌝ₛ, ⌜b⌝ₛ, ⌜a⌝ₛ, ⌜z⌝ₛ, ⌜σ₀⌝ₛ, ⌜σ₁⌝ₛ, ⌜σ₂⌝ₛ, ⌜σ₃⌝ₛ, ⌜σ₄⌝ₛ, ⌜σ₅⌝ₛ, ⌜σ₆⌝ₛ) ∧ ⌜χ⌝ₛ ∈ ⌜δ⌝ₛ ∧
    ⌜tg_bound_raw_m⌝ₚ(⌜δ⌝ₛ, ⌜S⌝ₛ, ⌜ν⌝ₛ)⟫


/-- 一轮的同一组见证同时保存完整实现、弹性和回答超幂。 -/
def tg_round_m {d} (ω e δ ν κ l n r U D u b z χ σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆
    τ C V Q w η Z a H f₀ f₁ f₂ f₃ q₀ q₁ q₂ : Term d) : Formula 1 d := set[d] ⟪
    ⌜χ⌝ₛ ∈ ⌜τ⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜τ⌝ₛ ∧ ⌜τ⌝ₛ ∈ ⌜δ⌝ₛ ∧
    (∃ ξ ζ, ⌜Formula.isSuccessor⌝ₚ(ξ, ⌜ν⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(ζ, ξ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜η⌝ₛ, ζ)) ∧
    ⌜v_sigma_m⌝ₚ(⌜η⌝ₛ, ⌜Z⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, ⌜Z⌝ₛ, ⌜H⌝ₛ) ∧
    ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ, ⌜τ⌝ₛ, ⌜n⌝ₛ, ⌜C⌝ₛ, ⌜V⌝ₛ, ⌜Q⌝ₛ, ⌜f₀⌝ₛ, ⌜f₁⌝ₛ, ⌜f₂⌝ₛ, ⌜f₃⌝ₛ) ∧
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜Z⌝ₛ, ⌜H⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜δ⌝ₛ, ⌜V⌝ₛ, ⌜Q⌝ₛ, ⌜w⌝ₛ) ∧
    ⌜ee_elastic_m⌝ₚ(⌜f₀⌝ₛ, ⌜f₁⌝ₛ, ⌜f₂⌝ₛ, ⌜f₃⌝ₛ, ⌜w⌝ₛ) ∧
    ⌜tg_reply_language_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜τ⌝ₛ, ⌜C⌝ₛ, ⌜V⌝ₛ, ⌜Q⌝ₛ, ⌜q₀⌝ₛ, ⌜q₁⌝ₛ, ⌜q₂⌝ₛ) ∧
    ⌜q₀⌝ₛ ∈ ⌜w⌝ₛ ∧ ⌜q₁⌝ₛ ∈ ⌜w⌝ₛ ∧ ⌜q₂⌝ₛ ∈ ⌜w⌝ₛ ∧
    ⌜b⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₀⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₁⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₂⌝ₛ ∈ ⌜ω⌝ₛ ∧
    ⌜σ₃⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₄⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₅⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₆⌝ₛ ∈ ⌜ω⌝ₛ ∧
    ⌜fun ω κ δ l n U D u τ Q w b z r q h s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_image_m ω κ δ l n U D u τ Q w b z r q h
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜δ⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ, ⌜τ⌝ₛ, ⌜Q⌝ₛ, ⌜w⌝ₛ, ⌜b⌝ₛ, ⌜z⌝ₛ, ⌜q₀⌝ₛ, ⌜q₁⌝ₛ, ⌜q₂⌝ₛ,
        ⌜σ₀⌝ₛ, ⌜σ₁⌝ₛ, ⌜σ₂⌝ₛ, ⌜σ₃⌝ₛ, ⌜σ₄⌝ₛ, ⌜σ₅⌝ₛ, ⌜σ₆⌝ₛ)⟫

/-- 更新仅存在量化这一组共同见证，不重新选择其中的类型或查询。 -/
def tg_successor_m {d} (ω e δ ν κ l n r U D u b z χ σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ : Term d) : Formula 1 d := set[d] ⟪
  ∃ τ C V Q w η Z a H f₀ f₁ f₂ f₃ q₀ q₁ q₂,
    ⌜tg_round_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜δ⌝ₛ, ⌜ν⌝ₛ, ⌜κ⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ,
      ⌜b⌝ₛ, ⌜z⌝ₛ, ⌜χ⌝ₛ, ⌜σ₀⌝ₛ, ⌜σ₁⌝ₛ, ⌜σ₂⌝ₛ, ⌜σ₃⌝ₛ, ⌜σ₄⌝ₛ, ⌜σ₅⌝ₛ, ⌜σ₆⌝ₛ,
      τ, C, V, Q, w, η, Z, a, H, f₀, f₁, f₂, f₃, q₀, q₁, q₂)⟫

-- 绑定位置依次为原输入 ω,e,δ,S,ν,κ,k,l,n,α,A,c,R,r,B,U,D,P,u,v,b,a,z,χ,s,t,g，
-- 再接四个弹性查询与七个程序槽位。所有参数都在原模型中，不使用宿主自然数游戏。
def tg_seed0_m : Formula 1 38 := tg_seed_m
  (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)
  (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
  (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22) (.bound 23) (.bound 24) (.bound 25) (.bound 26)
  (.bound 27) (.bound 28) (.bound 29) (.bound 30) (.bound 31) (.bound 32) (.bound 33) (.bound 34)
  (.bound 35) (.bound 36) (.bound 37)

def tg_successor0_m : Formula 1 38 := tg_successor_m
  (.bound 0) (.bound 1) (.bound 2) (.bound 4) (.bound 5) (.bound 7) (.bound 8) (.bound 13) (.bound 15)
  (.bound 16) (.bound 18) (.bound 20) (.bound 22) (.bound 23) (.bound 31) (.bound 32) (.bound 33)
  (.bound 34) (.bound 35) (.bound 36) (.bound 37)

-- 前十六个位置按量词栈次序保存新见证，后面逐项保留原三十八个输入。
def tg_witness0_m : Formula 1 54 := tg_round_m
  (.bound 16) (.bound 17) (.bound 18) (.bound 20) (.bound 21) (.bound 23) (.bound 24) (.bound 29) (.bound 31)
  (.bound 32) (.bound 34) (.bound 36) (.bound 38) (.bound 39) (.bound 47) (.bound 48) (.bound 49)
  (.bound 50) (.bound 51) (.bound 52) (.bound 53)
  (.bound 15) (.bound 14) (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
  (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)

/-- 一轮状态同时保存原树、元组和节点事实，避免搬运实现时遗失这些联系。 -/
def tg_round0_m : Formula 1 54 := .conj
  (tg_seed0_m.rename (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  tg_witness0_m

@[simp] theorem tg_seed0_closed_l : tg_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_seed0_m, tg_seed_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]
@[simp] theorem tg_successor0_closed_l : tg_successor0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_successor0_m, tg_successor_m, tg_round_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]
@[simp] theorem tg_witness0_closed_l : tg_witness0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_witness0_m, tg_round_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]
@[simp] theorem tg_round0_closed_l : tg_round0_m.FreeClosed :=
  ⟨(Definitional.Formula.freeClosed_rename _ _).mpr tg_seed0_closed_l, tg_witness0_closed_l⟩

def tg_renewal_m : Formula 1 0 := Formula.forallClosure 38 (.imp tg_seed0_m tg_successor0_m)

theorem tg_renewal_closed_l : tg_renewal_m.FreeClosed := 
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tg_seed0_closed_l, tg_successor0_closed_l⟩

/-- 原句子的真实实例来自已经完成的每轮更新证明。 -/
theorem tg_renewal_true_l (hZFC : M.Models ZFC) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tg_renewal_m := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [tg_seed0_m, tg_successor0_m, tg_seed_m, tg_successor_m, tg_round_m, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_mem_iff, woodin_sat_l I hZF.1, tg_low_sat_l hZF, Formula.satisfies_isSuccessor_iff,
    v_sat_l I hZF.1, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF), ee_language_sat_l hZFC,
    td_dcp_sat_l I hZF.1, ee_elastic_sat_l, rd_entry0_sat_l hZF.1, sg_set_sat_l I hZF.1,
    tg_node_sat_l I hZF.1, ts_program_sat_l hZF, Formula.satisfies_exists_iff,
    tg_reply_language_sat_l hZF, v_sigma_sat_l (ZF.modelsKP hZF), tg_image_sat_l hZF,
    Definitional.Term.eval_weaken, tt_eval_cases_l]
  rintro ⟨hω, he, heω, hd, low, root, hκδ, _, succ, height, hA, model, type, language, drop,
    elastic, first, last, set, node, prog, hχ, _⟩
  obtain ⟨τ, C, V, Q, w, η, Z, d, H, q', p, X, K, R₀, L, F, c₀, d₀, Y, T, j, κ', U', D', u',
    hχτ, hκτ, hτδ, level, hZ, model', lang, real, el, target, hX, source, hLδ, hκL, hτL,
    loc, inacc, strength, mx, my, ultra, critical, bound, κlimit, hU, hD, hu, pool, reply⟩ :=
    low.step_l hZFC hω he heω hd root hκδ succ height hA model type language drop elastic first last set node prog hχ
  have limit := inacc.limit_l (ZF.modelsKP hZF) source.transitive source.theory.algebra.pair
  obtain ⟨W, rank⟩ := ZF.v_exists_l I hZF limit.1
  have hwL := ordinal_down_l (ZF.modelsKP hZF) (hω.isOrdinal hZF) limit.1 source.below hκL
  have hVW := tt_constants_rank_l hZF rank limit hτL lang.rank lang.constants
  have hQW := lang.pool.rank_mem_l hZF hω rank limit (ZF.v_ordinal_mem_l I hZF rank hwL) real.finite hVW
  have hs i := hω.transitive hZF _ prog.length _ (prog.slots i)
  have seen : M.mem p.root w ∧ M.mem p.bound w ∧ M.mem p.height w := by
    obtain ⟨_, _, _, _, hr, hb, hh⟩ := reply
    exact ⟨hr, hb, hh⟩
  exact ⟨τ, C, V, Q, w, η, Z, d, H, q'.largest, q'.domain, q'.inaccessible, q'.stretch, p.root, p.bound, p.height,
    hχτ, hκτ, hτδ, level, hZ, model', lang, real, el, target, seen.1, seen.2.1, seen.2.2,
    prog.length, prog.natural, hs 0, hs 1, hs 2, hs 3, hs 4, hs 5, hs 6,
    X, K, R₀, L, F, c₀, d₀, Y, T, j, κ', U', D', u',
    hX, source, hLδ, hκL, hτL, ⟨W, rank, hQW⟩, loc, inacc, strength, mx, my, ultra, critical, bound, κlimit, hU, hD, hu, pool, reply⟩

end YesMetaZFC.SetTheory.LargeCardinal
