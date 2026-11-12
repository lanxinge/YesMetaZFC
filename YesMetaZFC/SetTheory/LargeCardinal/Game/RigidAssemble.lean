import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax

/-! # 由同一旧回答和当前候选调用高度刚性核

秩比较只负责给出常量域的一致性及三个低层参数的归属。其余证书直接在
同一反射结构内重排，完整超过关系与 dcp 定义域交给已经实现的刚性核。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem tg_rigid_assemble_l (kernel : Tg_kernel_d M)
    (ρ : Env M 29) (χ ψ : Env M 12) (ε : Env M 7)
    (ωχ : χ.bound 2 = ρ.bound 0) (τχ : χ.bound 3 = ρ.bound 8)
    (uχ : χ.bound 0 = ρ.bound 13) (mχ : χ.bound 1 = ρ.bound 9)
    (ωψ : ψ.bound 0 = ρ.bound 0) (lψ : ψ.bound 2 = χ.bound 4)
    (nψ : ψ.bound 3 = ρ.bound 9) (eψ : ψ.bound 1 = ε.bound 1)
    (ωε : ε.bound 0 = ρ.bound 0) (nε : ε.bound 3 = ρ.bound 3)
    (hi : M.mem (ε.bound 2) (ρ.bound 3)) (hh : M.mem (ε.bound 6) (ρ.bound 7))
    (eqV : χ.bound 6 = ρ.bound 11)
    (scope : M.mem (ψ.bound 4) (χ.bound 6) ∧ M.mem (ψ.bound 5) (χ.bound 6) ∧
      M.mem (ψ.bound 6) (χ.bound 6))
    (seed : Formula.satisfies ρ tc_seed0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (queries : Formula.satisfies ψ tg_query_row0_m) (reply : Formula.satisfies ε tg_reply_base0_m) :
    M.mem (ψ.bound 8) (ρ.bound 13) := by
  have result := kernel.continue_l ρ seed
  have fullPool := ((Formula.satisfies_conj_iff ..).mp result).2.2
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨omega, _, oldLanguage, _, _, _, _, _, exceeds, _⟩ := seed
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m, ee_domain_pack_m,
    ee_domain_pack0_m, Formula.satisfies_conj_iff] at oldLanguage
  have oldPool := oldLanguage.1.2.1
  have hwU : M.mem (ρ.bound 0) (ρ.bound 5) := oldLanguage.1.1
  obtain ⟨language, elastic⟩ := (Formula.satisfies_conj_iff ..).mp candidate
  simp only [Formula.satisfies_rename, ee_language0_m, Formula.satisfies_conj_iff] at language
  let ξ : Env M 29 := ⟨fun i => [ε.bound 0,ε.bound 1,ε.bound 2,ε.bound 3,ε.bound 4,ε.bound 5,ε.bound 6,
    ρ.bound 1,ρ.bound 2,ρ.bound 5,ρ.bound 6,ρ.bound 7,χ.bound 3,χ.bound 4,χ.bound 1,χ.bound 6,
    χ.bound 7,ρ.bound 12,χ.bound 8,χ.bound 9,χ.bound 0,ψ.bound 4,ψ.bound 5,ψ.bound 6,
    ψ.bound 7,ψ.bound 8,ψ.bound 9,ψ.bound 10,ψ.bound 11].get i, ρ.free⟩
  have raw : Formula.satisfies ξ tc_rigid_seed0_m := by
    simp only [tc_rigid_seed0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, hh, ?_, ?_, ?_, ?_, scope.1, scope.2.1, scope.2.2, ?_⟩
    · apply (Formula.satisfies_isOmega_iff ..).mpr
      change M.IsOmega (ε.bound 0)
      rw [ωε]
      exact (Formula.satisfies_isOmega_iff ..).mp omega
    · change M.mem (ε.bound 2) (ε.bound 3)
      exact nε.symm ▸ hi
    · change M.mem (ε.bound 0) (ρ.bound 5)
      exact ωε.symm ▸ hwU
    · let φ : Formula 1 4 := tt_pool_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)
      let f : Fin 4 → Term 29 := fun i => [.bound 0,.bound 3,.bound 5,.bound 6].get i
      let g : Fin 4 → Term 29 := fun i => [.bound 0,.bound 3,.bound 9,.bound 10].get i
      change Formula.satisfies ξ (φ.bind g)
      apply (Formula.satisfies_bind ξ g φ).mpr
      apply (Formula.closed_env_l φ (by simp -implicitDefEqProofs [φ]) ?_).mp
        ((Formula.satisfies_bind ρ f φ).mp oldPool)
      funext i
      exact Fin.cases ωε.symm (Fin.cases nε.symm (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
    · apply (Formula.satisfies_bind ξ (fun i => [.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,.bound 6].get i)
        tg_reply_base0_m).mpr
      exact (Formula.closed_env_l tg_reply_base0_m tg_reply_base0_closed_l (by
        funext i
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i)).mp reply
    · let φ := ee_domain_pack0_m
      let f : Fin 7 → Term 10 := fun i => [.bound 0,.bound 1,.bound 2,.bound 4,.bound 5,.bound 6,.bound 7].get i
      let g : Fin 7 → Term 29 := fun i => [.bound 0,.bound 12,.bound 13,.bound 15,.bound 16,.bound 18,.bound 19].get i
      change Formula.satisfies ξ (φ.bind g)
      apply (Formula.satisfies_bind ξ g φ).mpr
      apply (Formula.closed_env_l φ ee_domain_pack0_closed_l ?_).mp
        ((Formula.satisfies_bind (χ.reindex (fun i : Fin 10 => i.succ.succ)) f φ).mp language.1)
      funext i
      exact Fin.cases (ωχ.trans ωε.symm) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
    · simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        ee_elastic_m, Formula.satisfies_mem_iff] at elastic
      obtain ⟨v, drop, ⟨hg, hd⟩, _⟩ := elastic
      simp only [Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
      refine ⟨v, ?_, hg, hd⟩
      let φ : Formula 1 5 := td_dcp_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      let f : Fin 5 → Term 13 := fun i => [.bound 5,.bound 2,.bound 8,.bound 1,.bound 0].get i
      let g : Fin 5 → Term 30 := fun i => [.bound 14,.bound 15,.bound 17,.bound 21,.bound 0].get i
      change Formula.satisfies (ξ.push v) (φ.bind g)
      apply (Formula.satisfies_bind (ξ.push v) g φ).mpr
      apply (Formula.closed_env_l φ (by simp -implicitDefEqProofs [φ]) ?_).mp
        ((Formula.satisfies_bind (χ.push v) f φ).mp drop)
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
    · let f : Fin 12 → Term 29 := fun i => [.bound 0,.bound 1,.bound 13,.bound 14,.bound 21,.bound 22,
        .bound 23,.bound 24,.bound 25,.bound 26,.bound 27,.bound 28].get i
      change Formula.satisfies ξ (tg_query_base0_m.bind f)
      apply (Formula.satisfies_bind ξ f tg_query_base0_m).mpr
      apply (Formula.closed_env_l tg_query_base0_m tg_query_base0_closed_l ?_).mp
        ((Formula.satisfies_conj_iff ..).mp queries).1
      funext i
      exact Fin.cases (ωψ.trans ωε.symm) (Fin.cases eψ (Fin.cases lψ
        (Fin.cases (nψ.trans mχ.symm) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
    · let φ : Formula 1 4 := tt_pool_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)
      let f : Fin 4 → Term 29 := fun i => [.bound 0,.bound 9,.bound 11,.bound 12].get i
      let g : Fin 4 → Term 29 := fun i => [.bound 0,.bound 14,.bound 15,.bound 17].get i
      change Formula.satisfies ξ (φ.bind g)
      apply (Formula.satisfies_bind ξ g φ).mpr
      apply (Formula.closed_env_l φ (by simp -implicitDefEqProofs [φ]) ?_).mp
        ((Formula.satisfies_bind ρ f φ).mp fullPool)
      funext i
      exact Fin.cases ωε.symm (Fin.cases mχ.symm (Fin.cases eqV.symm (Fin.cases rfl (fun j => Fin.elim0 j)))) i
    · let φ := tx_exceeds0_m
      let f : Fin 12 → Term 29 := fun i => [.bound 0,.bound 2,.bound 1,.bound 3,.bound 5,.bound 6,
        .bound 7,.bound 8,.bound 9,.bound 11,.bound 12,.bound 13].get i
      let g : Fin 12 → Term 29 := fun i => [.bound 0,.bound 8,.bound 7,.bound 3,.bound 9,.bound 10,
        .bound 11,.bound 12,.bound 14,.bound 15,.bound 17,.bound 20].get i
      change Formula.satisfies ξ (φ.bind g)
      apply (Formula.satisfies_bind ξ g φ).mpr
      apply (Formula.closed_env_l φ tx_exceeds0_closed_l ?_).mp ((Formula.satisfies_bind ρ f φ).mp exceeds)
      funext i
      exact Fin.cases ωε.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases nε.symm (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases τχ.symm (Fin.cases mχ.symm
          (Fin.cases eqV.symm (Fin.cases rfl (Fin.cases uχ.symm (fun j => Fin.elim0 j)))))))))))) i
  exact uχ ▸ kernel.rigid_seed_l ξ raw

end YesMetaZFC.SetTheory.LargeCardinal
