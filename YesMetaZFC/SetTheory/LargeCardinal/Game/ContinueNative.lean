import YesMetaZFC.SetTheory.LargeCardinal.Game.ContinueAssemble
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay

/-! # 当前原关系中的实际继续选择

从同一原事件记录读取真实辅助走法及回答对，消费已搬运的语言、类型、
标签和相邻元数，直接构造继续输入并调用该反射层的原更新核。
结果保留完整 tc_result 和同一历史界坐标，供原生工厂读取同一次选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.continue_native_l {N R w η C : M.Domain}
    (context : Tg_context_d I w N R η C) (nx : ∃ x, M.mem x N)
    (ground : (smdl_structure_l I (R := R) nx).Models ZF)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x ⟨C, context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, context.member⟩ nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val.val = w)
    (ne : ι.bound 23 ≠ ι.bound 1)
    (θ : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, context.member⟩ nc) 10)
    (language : Formula.satisfies θ ee_language0_m) (hθ : (θ.bound 0).val.val = w)
    (u t χ : (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, context.member⟩ nc).Domain)
    (k a : (smdl_structure_l I (R := R) nx).Domain)
    (elastic : Formula.satisfies (θ.push u) (ee_elastic_m (.bound 7) (.bound 8) (.bound 9) (.bound 10) .newest))
    (labels : Fn0_d (M := smdl_structure_l I (R := R) nx) k (θ.bound 0).val t.val)
    (first : (smdl_structure_l I (R := R) nx).SuccessorOf a k)
    (last : (smdl_structure_l I (R := R) nx).SuccessorOf (θ.bound 2).val a)
    (trace : Tg_trace_d I N R w C (ι.bound 4).val.val (ι.bound 1).val.val (ι.bound 2).val.val
      (ι.bound 22).val.val (ι.bound 20).val.val t.val.val (θ.bound 1).val.val u.val.val)
    (below : Rd_entry_d χ.val.val (ι.bound 5).val.val R) :
    ∃ ε : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, context.member⟩ nc) 29,
      Formula.satisfies ε tc_seed0_m ∧ Formula.satisfies ε tc_result0_m ∧
      (∀ j : Fin 10, ε.bound ([0,1,3,4,5,6,17,18,19,20].get j) = θ.bound j) ∧
      ε.bound 7 = u ∧ ε.bound 3 = ι.bound 27 ∧
      (∀ j : Fin 14, ε.bound ([0,2,8,9,13,14,16,21,22,23,24,25,26,27].get j) =
        ι.bound ([0,5,24,28,25,36,37,38,39,40,41,42,43,44].get j)) ∧
      (smdl_structure_l I (R := R) nx).MemberSubset t.val (ι.bound 23).val ∧ ε.bound 28 = χ := by
  let N₀ := smdl_structure_l I (R := R) nx
  let w₀ : N₀.Domain := ⟨w, context.omega_mem⟩
  let C₀ : N₀.Domain := ⟨C, context.member⟩
  have fs := context.finite_l nx ground.1
  let J := rt_pair_l fs.transitive nc ground.1 fs.pair
  have ext := rt_model_ext_l ground.1 fs.transitive nc
  have raw := (tg_trace_native_l I nx w₀ C₀ (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val
    (ι.bound 22).val (ι.bound 20).val t.val (θ.bound 1).val u.val).mp trace
  obtain ⟨_, _, _, n', t', z, en, et, pair, event⟩ :=
    tg_trace0_read_l ground.1 fs.transitive nc (ι.bound 4) (ι.bound 1) (ι.bound 2) (ι.bound 20) raw
  have en : n' = ι.bound 22 := Subtype.ext en
  have et : t' = t := Subtype.ext et
  subst n' t'
  have wi : (ι.bound 0).val = w₀ := Subtype.ext hw
  have wt : (θ.bound 0).val = w₀ := Subtype.ext hθ
  have same : θ.bound 0 = ι.bound 0 := Subtype.ext (wt.trans wi.symm)
  obtain ⟨ε, seed, oldEq, typeEq, arity, newEq, sub, boundEq⟩ :=
    tg_continue_assemble_l ground fs nc ι issued wi ne θ language same u t z χ
      elastic (by
        change Fn0_d (M := N₀) k w₀ t.val
        rw [← wt]
        exact labels) first last ((tg_round_event_sat_l J ext ..).mp event) pair below
  exact ⟨ε, seed, (context.kernel_l nx nc).continue_l ε seed, oldEq, typeEq, arity, newEq, sub, boundEq⟩

end YesMetaZFC.SetTheory.LargeCardinal
