import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContext
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadRelative

/-! # 给定地模型内部的初始反射上下文

有限反射在给定模型中实施，所得层及其完整更新核直接还原到外部。
构造不更换工作根，也不要求给定模型对外部可数序列封闭。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X : M.Domain}

include hZF in
theorem tg_context_relative_l (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
    (ground : (rt_model_l X nx).Models ZFC) (ω A : (rt_model_l X nx).Domain)
    (hω : M.IsOmega ω.val) (Φ : List Lr_formula) :
    ∃ η C : (rt_model_l X nx).Domain, Tg_context_d ω.val X η.val C.val ∧ M.mem A.val C.val ∧ Sc_small_d X C.val ∧
      Fs_read_d ω.val C.val ∧ ∀ q ∈ Φ, Lr_reflect_d q.2.val C := by
  let hN := ZFC.models_zf_l ground
  let J := kp_pair_l (ZF.modelsKP hN)
  obtain ⟨P, pair⟩ := KP.exists_pair (ZF.modelsKP hN) ω A
  obtain ⟨η, C, rank, limit, hP, reflect⟩ := ZF.lr_finite_l J hN (⟨0, tg_kernel_m, tg_kernel_closed_l⟩ :: Φ) P
  have trans := ZF.v_transitive_l J hN rank
  have hωC := trans P hP ω ((pair ω).mpr (Or.inl rfl))
  have hAC := trans P hP A ((pair A).mpr (Or.inr rfl))
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ω⟩
  have valid := (reflect ⟨0, tg_kernel_m, tg_kernel_closed_l⟩ (List.mem_cons_self ..)
    ρ (fun i => Fin.elim0 i)).mp (tg_kernel_true_l ground ω)
  have kernel := (rt_model_delta_l hX nx tg_context_delta_l (ρ.push C)).mp valid
  let τ : Env (rt_model_l X nx) 2 := ⟨Fin.cases C (fun _ => η), fun _ => ω⟩
  have relative := (vr_sat_l (ZF.modelsKP hZF) hX nx τ (.bound 1) .newest).mp
    ((v_sigma_sat_l (ZF.modelsKP hN) τ (.bound 1) .newest).mpr rank)
  -- 在给定模型内取序数枚举与最小原像；编号图仍属于该模型。
  obtain ⟨μ, f, ord, fn, onto⟩ := ZFC.ordinal_enum_l ground J C
  obtain ⟨g, inj⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hN J ord fn onto
  let ξ : Env (rt_model_l X nx) 3 := ⟨Fin.cases g (Fin.cases C (fun _ => μ)), fun _ => ω⟩
  have index := (sc_index_sat_l (ZF.modelsKP hN) ξ (.bound 2) (.bound 1) .newest).mpr
    (Sc_index_d.of_injection_l (ZF.modelsKP hN) ord inj)
  have moved := (rt_model_delta_l hX nx (sc_index_delta_l (.bound 2) (.bound 1) .newest) ξ).mp index
  have small : Sc_small_d X C.val := ⟨μ.val, g.val, μ.property, g.property,
    (sc_index_sat_l (ZF.modelsKP hZF) (image_env_l (M := rt_model_l X nx) (N := M) Subtype.val ξ)
      (.bound 2) (.bound 1) .newest).mp moved⟩
  refine ⟨η, C, ⟨η.property, C.property, relative,
    (rt_limit_l hX nx (ZF.modelsKP hZF) η).mp limit, hωC, ?_⟩, hAC, small,
    fs_rank_relative_l hZF hX nx hN ω hω C.property relative
      ((rt_limit_l hX nx (ZF.modelsKP hZF) η).mp limit) hωC,
    fun q hq => reflect q (List.mem_cons_of_mem _ hq)⟩
  exact (Formula.closed_env_l tg_context_m tg_context_closed_l
    (ρ := image_env_l Subtype.val (ρ.push C))
    (η := ((⟨Fin.elim0, fun _ => ω.val⟩ : Env M 0).push C.val))
    (funext (Fin.cases rfl (fun i => Fin.elim0 i)))).mp kernel

end YesMetaZFC.SetTheory.LargeCardinal
