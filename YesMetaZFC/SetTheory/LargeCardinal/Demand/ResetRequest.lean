import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ResetControl
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope

/-! # 已落下重置请求产生同一原生回合

原控制的重置句构造输入；同一 E、P 函数表唯一性把全部源坐标与
四十七槽请求对齐。更新沿用这份输入，不另选请求、语言或程序。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_issued_reset_l (ι : Env M 47) (issued : Formula.satisfies ι td_issued0_m)
    (control : Formula.satisfies (ι.reindex (fun i : Fin 19 => i.castAdd 28))
      (td_reset_control_m (tg_control_params_d Term.bound)))
    (reset : ι.bound 23 = ι.bound 1) {U₁ U₂ z χ : M.Domain}
    (tree : Td_tree_d I (ι.bound 0) (ι.bound 6) (ι.bound 7))
    (alphabet : Td_alphabet_d (ι.bound 7) U₁ U₂) (chosen : M.mem z U₁)
    (hχ : M.mem χ (ι.bound 5)) (separated : Td_separated_d (ι.bound 7)) :
    ∃ ξ : Env M 43, Formula.satisfies ξ td_seed0_m ∧ ξ.bound 24 = χ ∧
      (∀ i : Fin 6, ξ.bound ([0,1,2,3,4,31].get i) =
        ι.bound ([0,1,5,7,8,6].get i)) ∧
      (∀ i : Fin 17, ξ.bound ([0,6,5,8,9,19,16,17,21,23,36,37,38,39,40,41,42].get i) =
        ι.bound ([0,23,24,27,28,25,31,32,37,38,39,40,41,42,43,44,45].get i)) ∧
    ∃ ρ : Env M 62, (∀ i : Fin 43, ρ.bound ⟨19+i.val,by omega⟩ = ξ.bound i) ∧
      Formula.satisfies ρ td_round0_m ∧ ρ.bound 47 = U₁ ∧
        ρ.bound 48 = U₂ ∧ ρ.bound 49 = z := by
  have state := (td_issued_sat_l I hZF.1 ι).mp issued
  have aux := state.auxiliary
  simp only [td_issued_aux0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fseq_end_sat_l I hZF.1,td_aux_sat_l hZF] at aux
  obtain ⟨h,_,aux⟩ := aux
  simp only [td_reset_control_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff,td_aux_sat_l hZF,td_move_sat_l hZF.1,
    td_tree_sat_l I hZF.1,td_alphabet_sat_l hZF.1,Formula.satisfies_mem_iff,
    td_separated_sat_l hZF.1,Tg_params_d.map_l,Definitional.Term.eval_weaken] at control
  have move₀ : Td_move_d (ι.bound 21) (ι.bound 22) (ι.bound 1) (ι.bound 24) (ι.bound 25) :=
    reset ▸ (show Td_move_d (ι.bound 21) (ι.bound 22) (ι.bound 23) (ι.bound 24) (ι.bound 25)
      from state.payload.1)
  have result := control (ι.bound 19) h (ι.bound 21) U₁ U₂ z χ aux
    ⟨ι.bound 22,ι.bound 24,ι.bound 25,move₀⟩ tree alphabet chosen hχ separated
  simp only [td_reset_result_m,Formula.satisfies_bind] at result
  let η : Env M 13 := ⟨fun i => [ι.bound 0,ι.bound 1,ι.bound 5,ι.bound 7,ι.bound 8,
    ι.bound 9,ι.bound 10,ι.bound 21,ι.bound 6,U₁,U₂,z,χ].get i,ι.free⟩
  have fixed : Formula.satisfies η td_reset_result0_m := by
    apply (Formula.closed_env_l td_reset_result0_m td_reset_result0_closed_l
      (ρ := _) (η := η) ?_).mp result
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))) i
  obtain ⟨v,valid⟩ := (rb_exists_sat_l (n := 43) η td_reset_body0_m).mp fixed
  obtain ⟨seed,body⟩ := (Formula.satisfies_conj_iff ..).mp valid
  let ξ : Env M 43 := ⟨v,ι.free⟩
  have seed : Formula.satisfies ξ td_seed0_m := by
    apply (Formula.closed_env_l td_seed0_m td_seed0_closed_l (ρ := _) (η := ξ) ?_).mp
      ((Formula.satisfies_rename ..).mp seed)
    funext i
    change Fin.addCases v _ (i.castAdd 13) = v i
    simp only [Fin.addCases_left]
  simp only [Formula.satisfies_conj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_exists_iff,td_move_sat_l hZF.1,tg_ee_data_sat_l hZF.1,
    tg_program_data_sat_l hZF.1,tt_eval_cases_l,Definitional.Term.eval_weaken] at body
  obtain ⟨hw,he,hδ,hS,hν,_,_,hc,_,_,_,hU₁,hU₂,hz₀,hA,⟨ℓ,move⟩,ee,program⟩ := body
  obtain ⟨_,ek,eκ,eu⟩ := move.unique_l state.payload.1
  have facts := seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at facts
  have add := (Formula.satisfies_isOrdinalAddition_iff I hZF.1 ..).mp facts.2.2.2.2.2.1
  have sq : M.SuccessorOf (ξ.bound 8) (ξ.bound 7) :=
    (Formula.satisfies_isSuccessor_iff ..).mp facts.2.2.2.2.2.2.1
  have sn : M.SuccessorOf (ξ.bound 9) (ξ.bound 8) :=
    (Formula.satisfies_isSuccessor_iff ..).mp facts.2.2.2.2.2.2.2.1
  have arity : Td_arity_d I (ι.bound 23) (ι.bound 26) (ι.bound 27) (ι.bound 28) (ι.bound 29) :=
    state.payload.2.2.2.1
  have ord : M.IsOrdinal (ι.bound 23) := arity.1.elim (fun _ h => h.1.1.1)
  obtain ⟨_,_,unique⟩ := ZF.ordinalAddition_existsUnique hZF I (ι.bound 23) ord
  have ed : ξ.bound 7 = ι.bound 26 :=
    (unique _ ((show ξ.bound 6 = ι.bound 23 from ek) ▸ add)).trans (unique _ arity.1).symm
  have eq : ξ.bound 8 = ι.bound 27 := (ed ▸ sq).eq hZF.1 arity.2.1
  have en : ξ.bound 9 = ι.bound 28 := (eq ▸ sn).eq hZF.1 arity.2.2.1
  have data := state.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at data
  have tables := data.1
  simp only [td_tables_m,Formula.satisfies_conj_iff] at tables
  have ef := (Formula.satisfies_isFunction_iff I hZF.1 ..).mp tables.2.2.2.1
  have pf := (Formula.satisfies_isFunction_iff I hZF.1 ..).mp tables.2.2.2.2.1
  have ee : Tg_ee_data_d (ι.bound 9) (ι.bound 24) (ι.bound 27)
      (ξ.bound 15) (ξ.bound 16) (ξ.bound 17)
      ⟨ξ.bound 32,ξ.bound 33,ξ.bound 34,ξ.bound 35⟩ :=
    (show ξ.bound 5 = ι.bound 24 from eκ) ▸ eq ▸ ee
  have payload := state.payload.2.2.2.2.2.2.2.2.2
  obtain ⟨_,eU,eE,_⟩ := ee.unique_l hZF.1 ef payload.1
  have program : Tg_program_data_d (ι.bound 10) (ι.bound 27) (ξ.bound 21) (ξ.bound 23)
      (Fin.cases (ξ.bound 36) (Fin.cases (ξ.bound 37) (Fin.cases (ξ.bound 38)
        (Fin.cases (ξ.bound 39) (Fin.cases (ξ.bound 40) (Fin.cases (ξ.bound 41)
          (fun _ : Fin 1 => ξ.bound 42))))))) := eq ▸ program
  obtain ⟨eb,ez,es⟩ := program.unique_l hZF.1 pf payload.2
  obtain ⟨ρ,same,round⟩ := td_seed_native_l hZFC ξ seed
  refine ⟨ξ,seed,hc,Fin.cases hw (Fin.cases he (Fin.cases hδ (Fin.cases hS
    (Fin.cases hν (Fin.cases hA (fun i => Fin.elim0 i)))))),?_,ρ,same,round,
      (same 28).trans hU₁,(same 29).trans hU₂,(same 30).trans hz₀⟩
  exact Fin.cases hw (Fin.cases ek (Fin.cases eκ (Fin.cases eq (Fin.cases en (Fin.cases eu
    (Fin.cases eU (Fin.cases eE (Fin.cases eb (Fin.cases ez (Fin.cases (congrFun es 0)
      (Fin.cases (congrFun es 1) (Fin.cases (congrFun es 2) (Fin.cases (congrFun es 3)
        (Fin.cases (congrFun es 4) (Fin.cases (congrFun es 5) (Fin.cases (congrFun es 6)
          (fun i => Fin.elim0 i))))))))))))))))) 

end YesMetaZFC.SetTheory.LargeCardinal
