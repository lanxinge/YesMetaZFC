import YesMetaZFC.Model.Forcing.Iteration.Names.ProjectionName
import YesMetaZFC.Model.Forcing.Iteration.Names.Generic

/-! # 前缀被接受后进入新阶段商偏序

真实限制函数确定旧条件的前缀。该函数值被当前泛型接受，恰好使原条件进入
当前商条件名称；规范 N 成员力迫保证仍使用同一个内部小模型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 投影名称被当前泛型接受时，原名称进入该阶段的实际 N 商条件集。 -/
theorem row_quot_enter_l (hZF : M.Models ZF) {β B R b D N f F c ν γ K τ σ p}
    (O : Cond_order_d M B R B) (hb : M.mem b B) (hp : Below_d M B R B p b)
    (hf : Row_proj_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β D B f)
    (hF : Check_d M b f F) (hc : Check_d M b D c) (hν : Check_d M b N ν)
    (hγ : Gname_d (M := M) B b γ)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β B b D N K)
    (hτ : Name_d M B τ) (hσ : Name_d M B σ)
    (hτc : Mem_force_d M B R B p τ c) (hτν : Mem_force_d M B R B p τ ν)
    (hτσ : Rel_force_d M B R B F p τ σ) (hσγ : Mem_force_d M B R B p σ γ) :
    Mem_force_d M B R B p τ K := by
  let ρ₀ : Env M 5 := ((((⟨fun _ => β, fun _ => β⟩ : Env M 1).push B).push R).push b).push D
  let ρ₁ : Env M 10 := ((((ρ₀.push N).push f).push F).push c).push ν
  let ρ : Env M 15 := ((((ρ₁.push γ).push K).push τ).push σ).push p
  let φ : Formula 1 2 := .mem (.bound 0) (.bound 1)
  let es : Fin 2 → Term 15 := Fin.cases (.bound 2) (fun _ => .bound 3)
  let ψ : Formula 1 15 := .conj (.mem (.bound 11) (.bound 13))
    (.conj (below_m (.bound 13) (.bound 12) (.bound 13) (.bound 0) (.bound 11))
    (.conj (row_proj_m (.bound 14) (.bound 10) (.bound 13) (.bound 8))
    (.conj (check_m (.bound 11) (.bound 8) (.bound 7))
    (.conj (check_m (.bound 11) (.bound 10) (.bound 6))
    (.conj (check_m (.bound 11) (.bound 9) (.bound 5))
    (.conj (gname_m (.bound 13) (.bound 11) (.bound 4))
    (.conj (row_quot_m (.bound 14) (.bound 13) (.bound 11) (.bound 10) (.bound 9) (.bound 3))
    (.conj (name_m (.bound 13) (.bound 1))
    (.conj (mem_force_m (.bound 13) (.bound 12) (.bound 13) (.bound 0) (.bound 2) (.bound 6))
    (.conj (mem_force_m (.bound 13) (.bound 12) (.bound 13) (.bound 0) (.bound 2) (.bound 5))
    (.conj (rel_force_m (.bound 13) (.bound 12) (.bound 13) (.bound 7) (.bound 0) (.bound 2) (.bound 1))
      (mem_force_m (.bound 13) (.bound 12) (.bound 13) (.bound 0) (.bound 1) (.bound 4)))))))))))))
  have hφ : φ.FreeClosed := by simp only [φ, Definitional.Formula.FreeClosed]; exact ⟨rfl, rfl⟩
  have hψ : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed]
  have raw (A : SetTheory.Structure.{u}) (hA : A.Models ZF) (η : Env A 15) : Formula.satisfies η ψ ↔
      A.mem (η.bound 11) (η.bound 13) ∧ Below_d A (η.bound 13) (η.bound 12) (η.bound 13) (η.bound 0) (η.bound 11) ∧
      Row_proj_d (kpair_interpretation_l A hA.1 (KP.exists_pair (ZF.modelsKP hA))) (η.bound 14) (η.bound 10) (η.bound 13) (η.bound 8) ∧
      Check_d A (η.bound 11) (η.bound 8) (η.bound 7) ∧ Check_d A (η.bound 11) (η.bound 10) (η.bound 6) ∧
      Check_d A (η.bound 11) (η.bound 9) (η.bound 5) ∧ Gname_d (M := A) (η.bound 13) (η.bound 11) (η.bound 4) ∧
      Row_quot_d (kpair_interpretation_l A hA.1 (KP.exists_pair (ZF.modelsKP hA))) (η.bound 14) (η.bound 13) (η.bound 11)
        (η.bound 10) (η.bound 9) (η.bound 3) ∧ Name_d A (η.bound 13) (η.bound 1) ∧
      Mem_force_d A (η.bound 13) (η.bound 12) (η.bound 13) (η.bound 0) (η.bound 2) (η.bound 6) ∧
      Mem_force_d A (η.bound 13) (η.bound 12) (η.bound 13) (η.bound 0) (η.bound 2) (η.bound 5) ∧
      Rel_force_d A (η.bound 13) (η.bound 12) (η.bound 13) (η.bound 7) (η.bound 0) (η.bound 2) (η.bound 1) ∧
      Mem_force_d A (η.bound 13) (η.bound 12) (η.bound 13) (η.bound 0) (η.bound 1) (η.bound 4) := by
    let J := kpair_interpretation_l A hA.1 (KP.exists_pair (ZF.modelsKP hA))
    simp only [ψ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, below_sat_l A hA.1,
      row_proj_sat_l J hA.1, check_sat_l A hA.1, gname_sat_l hA.1, row_quot_sat_l J hA.1,
      name_sat_l A hA.1, mem_force_sat_l A hA.1, rel_force_sat_l A hA.1]
    rfl
  have hf' := forces_of_generics_l φ hφ ψ hψ es (.bound 13) (.bound 12) (.bound 13) (.bound 0)
    (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl
    (fun A hA η O' _ _ _ hh U hU hpU ξ hξ => ?_) hZF ρ O (Fin.cases hτ (fun _ => hK.1)) hp.1 hp.2.1
      ((raw M hZF ρ).mpr ⟨hb, hp, hf, hF, hc, hν, hγ, hK, hσ, hτc, hτν, hτσ, hσγ⟩)
  · exact (forces_mem_l hZF.1 (.bound 0) (.bound 1) ⟨fun i => (es i).eval ρ, ρ.free⟩ p).mp hf'
  · obtain ⟨hb', hp', hf', hF', hc', hν', hγ', hK', hσ', hτc', hτν', hτσ', hσγ'⟩ := (raw A hA η).mp hh
    let E := extension_l A hA (η.bound 13) (η.bound 12) (η.bound 13) U
    have hbU := hU.upward _ _ hpU hb' hp'.2.2
    obtain ⟨e, hv, hm, hi⟩ := check_map_l O' hA hU hbU
    obtain ⟨y, hy⟩ := name_value_l (R := η.bound 12) (z := η.bound 13) (U := U) hσ'
    obtain ⟨G, hG⟩ := name_value_l (R := η.bound 12) (z := η.bound 13) (U := U) hγ'.1
    have hxD := (qval_mem_forcing_l O' hA hU (hξ 0) (hv _ _ hc')).mp ⟨η.bound 0, hpU, hτc'⟩
    obtain ⟨r, hr, hrx⟩ := (hm (η.bound 10) (ξ.bound 0)).mp hxD
    have hxN := (qval_mem_forcing_l O' hA hU (hξ 0) (hv _ _ hν')).mp ⟨η.bound 0, hpU, hτν'⟩
    have hrN := (image_member_l e hi hm).mp (hrx.symm ▸ hxN)
    have hry := (rel_force_truth_l O' hA hU (hξ 0) hy (hv _ _ hF')).mp ⟨η.bound 0, hpU, hτσ'⟩
    obtain ⟨a, _, hra⟩ := hf'.1.2.2 r hr
    have hEN := extension_ext_l O' hA hU
    have hFunc := image_function_l (hEN := hEN) (hPN := internal_pair_l O' hA hU) e hi hm hf'.1
    have hea := (image_entry_iff_l e hi hm (KP.exists_pair (ZF.modelsKP hA)) hEN r a (η.bound 8)).mp hra
    have hya : y = e a := hFunc.1.2 (e r) y (e a) (hrx.symm ▸ hry) hea
    have hyG := (qval_mem_forcing_l O' hA hU hy hG).mp ⟨η.bound 0, hpU, hσγ'⟩
    obtain ⟨a', haU, hae⟩ := (gname_value_l hA O' hU hγ' hG e hv y).mp hyG
    have haa := hi (hae.trans hya)
    apply (Formula.satisfies_mem_iff ξ (.bound 0) (.bound 1)).mpr
    exact (row_quot_value_l hA O' hU hK' (hξ 1) e hv (ξ.bound 0)).mpr
      ⟨r, a, hr, hrN, ((hf'.2 r a).mp hra).2, haa ▸ haU, hrx⟩

end YesMetaZFC.Model.Forcing.Internal
