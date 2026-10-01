import YesMetaZFC.Model.Forcing.TwoStep.Proper.Witness
import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.TwoStep.Presentation
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem

/-! # 二步主条件的合成

将任意稠密集及任意下方条件一起反射到可数地模型，再在首坐标上取泛型。
泛型中的稠密见证已由前一模块证明可取回 D∩N，因此反射得到原模型的主条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

/-- 首阶段 N 主条件与被迫的 N[G] 主条件合成为实际二步 N 主条件。 -/
theorem two_step_master_l {ω χ H c J d N K q t μ v} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N K) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
    (hv : M.mem v C) (hvq : KPair_d M v q t) (hm : Mstr_d M B R z N q) (hμ : Ng_name_d M B N μ)
    (hForce : Forces_d M B R z mstr_body_m (mstr_env_l A T μ t) q) : Mstr_d M C S C N v := by
  refine ⟨hv, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hv)), fun D hDN hD r hr => ?_⟩
  obtain ⟨p, s, hrp, _, hpb, _⟩ := (h.conditions r).mp hr.1
  -- 参数由偏序、迭代、内部模型、主条件、待处理的下方条件及稠密集组成。
  let ρP : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push A
  let ρ₀ : Env M 9 := (((ρP.push T).push W).push C).push S
  let ρ₁ : Env M 17 := (((((((ρ₀.push ω).push χ).push H).push c).push J).push d).push N).push K
  let ρ : Env M 25 := (((((((ρ₁.push q).push t).push μ).push v).push r).push p).push s).push D
  let es : Fin 4 → Term 25 := Fin.cases (.bound 6) (Fin.cases (.bound 5) (Fin.cases (.bound 19) (fun _ => .bound 20)))
  let model : Formula 1 25 := .conj (Formula.isOmega (.bound 15))
    (.conj (Formula.isRegularCardinal kpair_convention_l (.bound 14))
    (.conj (.mem (.bound 15) (.bound 14))
    (.conj (h_m (𝒞 := kpair_convention_l) (.bound 14) (.bound 13))
    (.conj (smem_m (𝒞 := kpair_convention_l) (.bound 12) (.bound 13) (.bound 11))
    (.conj (ssub_m (𝒞 := kpair_convention_l) (.bound 12) (.bound 10) (.bound 13) (.bound 11) (.bound 9) (.bound 8))
    (.conj (selem_m (𝒞 := kpair_convention_l) (.bound 15) (.bound 12) (.bound 10))
    (.conj (.mem (.bound 24) (.bound 9))
    (.conj (.mem (.bound 23) (.bound 9)) (.mem (.bound 22) (.bound 9))))))))))
  let step : Formula 1 25 := .conj
    (two_step_m (.bound 24) (.bound 23) (.bound 22) (.bound 21) (.bound 20) (.bound 19) (.bound 18) (.bound 17) (.bound 16))
    (.conj (cond_order_m (.bound 17) (.bound 16) (.bound 17))
    (.conj (name_m (.bound 24) (.bound 19))
    (.conj (.mem (.bound 4) (.bound 17))
    (.conj (kpair_m (.bound 4) (.bound 7) (.bound 6))
    (.conj (below_m (.bound 17) (.bound 16) (.bound 17) (.bound 3) (.bound 4))
      (kpair_m (.bound 3) (.bound 2) (.bound 1)))))))
  let master : Formula 1 25 := .conj (mstr_m (.bound 24) (.bound 23) (.bound 22) (.bound 9) (.bound 7))
    (.conj (ng_name_m (.bound 24) (.bound 9) (.bound 5))
    (.conj (force_at_m mstr_body_m es (.bound 24) (.bound 23) (.bound 22) (.bound 7))
    (.conj (.mem (.bound 0) (.bound 9)) (dense_set_m (.bound 17) (.bound 16) (.bound 17) (.bound 0)))))
  let α : Formula 1 25 := .conj model (.conj step master)
  let β : Formula 1 25 := .existsE (.conj (.mem .newest (.bound 1))
    (.conj (.mem .newest (.bound 10)) (cmp_m (.bound 18) (.bound 17) (.bound 18) (.bound 4) .newest)))
  have hes : ∀ i, (es i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  have hα : α.FreeClosed := by
    simp -implicitDefEqProofs [α, model, step, master, Definitional.Formula.FreeClosed, hes]
  have hβ : β.FreeClosed := by simp -implicitDefEqProofs [β, Definitional.Formula.FreeClosed]
  have fenv (M' : SetTheory.Structure.{u}) (hE : Extensional M') (η : Env M' 25) :
      Forces_d M' (η.bound 24) (η.bound 23) (η.bound 22) mstr_body_m
        ⟨fun i => (es i).eval η, η.free⟩ (η.bound 7) ↔
      Forces_d M' (η.bound 24) (η.bound 23) (η.bound 22) mstr_body_m
        (mstr_env_l (η.bound 20) (η.bound 19) (η.bound 5) (η.bound 6)) (η.bound 7) :=
    forces_env_l hE mstr_body_m mstr_body_closed_l _ _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) _
  have raw (M' : SetTheory.Structure.{u}) (hN : M'.Models ZFC) (η : Env M' 25) :
      Formula.satisfies η α ↔
      let I' := kpair_interpretation_l M' hN.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hN)))
      (M'.IsOmega (η.bound 15) ∧ M'.IsRegularCardinal I' (η.bound 14) ∧ M'.mem (η.bound 15) (η.bound 14) ∧
        H_d I' (η.bound 14) (η.bound 13) ∧ Smem_d I' (η.bound 12) (η.bound 13) (η.bound 11) ∧
        Ssub_d I' (η.bound 12) (η.bound 10) (η.bound 13) (η.bound 11) (η.bound 9) (η.bound 8) ∧
        Selem_d I' (η.bound 15) (η.bound 12) (η.bound 10) ∧ M'.mem (η.bound 24) (η.bound 9) ∧
        M'.mem (η.bound 23) (η.bound 9) ∧ M'.mem (η.bound 22) (η.bound 9)) ∧
      (Two_step_d M' (η.bound 24) (η.bound 23) (η.bound 22) (η.bound 21) (η.bound 20) (η.bound 19)
          (η.bound 18) (η.bound 17) (η.bound 16) ∧
        Cond_order_d M' (η.bound 17) (η.bound 16) (η.bound 17) ∧ Name_d M' (η.bound 24) (η.bound 19) ∧
        M'.mem (η.bound 4) (η.bound 17) ∧ KPair_d M' (η.bound 4) (η.bound 7) (η.bound 6) ∧
        Below_d M' (η.bound 17) (η.bound 16) (η.bound 17) (η.bound 3) (η.bound 4) ∧
        KPair_d M' (η.bound 3) (η.bound 2) (η.bound 1)) ∧
      (Mstr_d M' (η.bound 24) (η.bound 23) (η.bound 22) (η.bound 9) (η.bound 7) ∧
        Ng_name_d M' (η.bound 24) (η.bound 9) (η.bound 5) ∧
        Forces_d M' (η.bound 24) (η.bound 23) (η.bound 22) mstr_body_m
          ⟨fun i => (es i).eval η, η.free⟩ (η.bound 7) ∧ M'.mem (η.bound 0) (η.bound 9) ∧
        Dense_set_d M' (η.bound 17) (η.bound 16) (η.bound 17) (η.bound 0)) := by
    let I' := kpair_interpretation_l M' hN.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hN)))
    simp only [α, model, step, master, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
      Formula.satisfies_isRegularCardinal_iff I' hN.1, Formula.satisfies_mem_iff, h_sat_l I' hN.1,
      smem_sat_l I', ssub_sat_l I', selem_sat_l I' hN.1, two_step_sat_l hN.1,
      cond_order_sat_l hN.1, name_sat_l M' hN.1, kpair_sat_l M' hN.1, below_sat_l M' hN.1,
      mstr_sat_l M' hN.1, ng_name_sat_l M' hN.1, force_at_sat_l, dense_set_sat_l M' hN.1]
    rfl
  have result (M' : SetTheory.Structure.{u}) (hE : Extensional M') (η : Env M' 25) :
      Formula.satisfies η β ↔ ∃ x, M'.mem x (η.bound 0) ∧ M'.mem x (η.bound 9) ∧
        Cmp_d M' (η.bound 17) (η.bound 16) (η.bound 17) (η.bound 3) x := by
    simp only [β, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, cmp_sat_l M' hE]
    rfl
  apply (result M hZF.1 ρ).mp
  apply source_of_generics_theory_l (Γ := ZFC) α β hα hβ (.bound 24) (.bound 23) (.bound 22) (.bound 2)
    rfl rfl rfl rfl (fun M' hN hZ η O' hraw U hU hpU => ?_) hZF hZFC ρ O hpb.1 hpb.2.1
      ((raw M hZFC ρ).mpr ⟨⟨hω, hχ, hωχ, hH, ⟨hSub.source, hJ⟩, hSub, hElem, hB, hR, hz⟩,
        ⟨h, L, hT, hv, hvq, hr, hrp⟩, hm, hμ, (fenv M hZF.1 ρ).mpr hForce, hDN, hD⟩)
  obtain ⟨⟨hω', hχ', hωχ', hH', hM', hSub', hElem', hB', hR', hz'⟩,
    ⟨h', L', hT', hv', hvq', hr', hrp'⟩, hm', hμ', hForce', hDN', hD'⟩ := (raw M' hZ η).mp hraw
  exact (result M' hN.1 η).mpr (two_step_master_hit_l O' hZ hU hω' hχ' hωχ' hH' hM'.2
    hSub' hElem' hB' hR' hz' h' L' hT' hv' hvq' hr' hrp' hm' hμ' ((fenv M' hN.1 η).mp hForce') hpU hDN' hD')

end YesMetaZFC.Model.Forcing.Internal
