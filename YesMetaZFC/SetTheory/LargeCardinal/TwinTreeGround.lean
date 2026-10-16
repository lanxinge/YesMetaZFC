import YesMetaZFC.SetTheory.LargeCardinal.TwinTreeSyntax

/-! # 从原坍缩力迫覆盖得到任意地模型的双树结论

有限参数反射构造实际可数初等子模型及经过指定正条件的泛型滤子；
真值定理给出同一扩张中的覆盖，再把地面覆盖和策略存在性反射回来。
原模型无需外部可数、良基或具有实际泛型滤子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u

private theorem td_reflected_l (N : Structure.{u}) (hZFC : N.Models ZFC) (ρ : Env N 24)
    (O : Cond_order_d N (ρ.bound 13) (ρ.bound 14) (ρ.bound 13))
    (input : Formula.satisfies ρ td_input_m) (U : N.Domain → Prop)
    (generic : Generic_d N (ρ.bound 13) (ρ.bound 14) (ρ.bound 13) U) (hp : U (ρ.bound 15)) :
    Formula.satisfies ρ td_output_m := by
  let hN := ZFC.models_zf_l hZFC
  obtain ⟨⟨hw, hd, rank, hA, ha, pair, space, tree, pair', space', tree', collapse, order⟩, checks, force⟩ :=
    (td_input_sat_l hN ρ).mp input
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hN generic hp
  let E := extension_l N hN (ρ.bound 13) (ρ.bound 14) (ρ.bound 13) U
  have hE : E.Models ZF := preserves_zf_l O hN generic
  let η : Env N 8 := ⟨fun i => (td_names_m i).eval ρ, fun _ => (td_names_m 0).eval ρ⟩
  let ξ : Env E 8 := ⟨fun i => e ((td_parameters_m i).eval ρ), fun _ => e (ρ.bound 0)⟩
  have values : Env_val_d hN η ξ := by
    intro t
    cases t with
    | bound i => exact hv _ _ (checks i)
    | free _ => exact hv _ _ (checks 0)
  have forced : Forces_d N (ρ.bound 13) (ρ.bound 14) (ρ.bound 13) td_cover0_m η (ρ.bound 15) :=
    (forces_env_l hN.1 td_cover0_m td_cover0_closed_l
      (⟨fun i => (td_names_m i).eval ρ, ρ.free⟩ : Env N 8) η (fun _ => rfl) (ρ.bound 15)).mp force
  have covered := (forcing_truth_l O hN generic td_cover0_m td_cover0_closed_l η ξ values).mp ⟨_, hp, forced⟩
  have cover := (td_cover_sat_l (kp_pair_l (ZF.modelsKP hE)) hE.1 ξ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mp covered
  have result := td_generic_dichotomy_l hZFC hw hd rank hA ha pair space tree pair' space' tree'
    collapse order O generic hp e hi he hv cover
  exact (td_output_sat_l hN ρ).mpr result

variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

/-- 任一正坍缩条件迫使两树穷尽已足够；不把泛型存在性列为调用前提。 -/
theorem td_ground_l {ω δ A X a Γ Y F T Λ Z G S C Q p : M.Domain}
    (hw : M.IsOmega ω) (hd : Woodin_d I δ) (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A)
    (pair : M.IsCartesianProduct I Y A Γ) (space : Fseq_space_d I ω Y F) (tree : Tree_d F T)
    (pair' : M.IsCartesianProduct I Z A Λ) (space' : Fseq_space_d I ω Z G) (tree' : Tree_d G S)
    (collapse : Fseq_space_d I ω δ C)
    (order : ∀ r s, Entry_d M r s Q ↔ M.mem r C ∧ M.mem s C ∧ M.MemberSubset s r)
    (hp : M.mem p C) (hn : p ≠ C) (η : Env M 8)
    (checks : ∀ i, Check_d M p ([ω, A, Y, F, T, Z, G, S].get i) (η.bound i))
    (force : Forces_d M C Q C td_cover0_m η p) :
    Td_cover_d I ω A Y F T Z G S ∧
      (Tp_win_d hM true true ω A Y F T ∨ Tp_win_d hM false false ω A Z G S) := by
  let O : Cond_order_d M C Q C := {
    refl := fun r hr => (order r r).mpr ⟨hr, hr, fun _ h => h⟩
    trans := fun r s t hr _ ht rs st => (order r t).mpr
      ⟨hr, ht, fun v hv => ((order r s).mp rs).2.2 v (((order s t).mp st).2.2 v hv)⟩
    zero := fun r _ rc => (KP.mem_irrefl_d (ZF.modelsKP hM) C ((order r C).mp rc).2.1).elim }
  let ρ : Env M 24 := ⟨fun i => [ω, δ, A, X, a, Γ, Y, F, T, Λ, Z, G, S, C, Q, p,
    η.bound 0, η.bound 1, η.bound 2, η.bound 3, η.bound 4, η.bound 5, η.bound 6, η.bound 7].get i, η.free⟩
  have names : ∀ i, (td_names_m i).eval ρ = η.bound i := by
    simp only [Fin.forall_fin_succ]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun i => Fin.elim0 i⟩
  have parameters : ∀ i, (td_parameters_m i).eval ρ = [ω, A, Y, F, T, Z, G, S].get i := by
    simp only [Fin.forall_fin_succ]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun i => Fin.elim0 i⟩
  have input : Td_input_d hM ρ := by
    refine ⟨⟨hw, hd, rank, hA, ha, pair, space, tree, pair', space', tree', collapse, order⟩,
      fun i => ?_, ?_⟩
    · rw [parameters i, names i]; exact checks i
    · exact (forces_env_l hM.1 td_cover0_m td_cover0_closed_l η
        (⟨fun i => (td_names_m i).eval ρ, ρ.free⟩ : Env M 8) (fun i => (names i).symm) p).mp force
  have result := source_of_generics_theory_l (Γ := ZFC) td_input_m td_output_m td_input_closed_l td_output_closed_l
    (.bound 13) (.bound 14) (.bound 13) (.bound 15) rfl rfl rfl rfl
    (fun N _ hN ρ O input U generic hp => td_reflected_l N hN ρ O input U generic hp)
    hM hZFC ρ O hp hn ((td_input_sat_l hM ρ).mpr input)
  exact (td_output_sat_l hM ρ).mp result

end YesMetaZFC.SetTheory.LargeCardinal
