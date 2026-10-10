import YesMetaZFC.Model.Forcing.TwoStep.Proper.SecondValue
import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Proper.Master.Name
import YesMetaZFC.Model.Forcing.TwoStep.Presentation
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem

/-! # 二步主条件的第二坐标力迫证书

在可数反射模型中应用已经证明的固定泛型结论，再将完整模型参数、二步条件
及主性一并反射。最后的接口不要求地模型可数，也不要求调用者提供泛型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

private theorem countable_second_l (e : Nat → M.Domain) (he : Function.Surjective e)
    {ω χ H c J d N K v q t μ} (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N K) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hC : M.mem C N) (hS : M.mem S N)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
    (hvq : KPair_d M v q t) (hm : Mstr_d M C S C N v) (hμ : Ng_name_d M B N μ) :
    Forces_d M B R z mstr_body_m (mstr_env_l A T μ t) q := by
  have hv := (two_step_mem_l h hvq).mp hm.1
  let ρ := mstr_env_l A T μ t
  have hρ : ∀ i, Name_d M B (ρ.bound i) :=
    Fin.cases ⟨W, hv.1, h.closed⟩ (Fin.cases hμ.1 (Fin.cases hT (fun _ => ⟨W, h.root, h.closed⟩)))
  apply forces_countable_l O hZF e he mstr_body_m mstr_body_closed_l ρ hρ hv.2.1.1 hv.2.1.2.1
  intro U hU hq η hη
  exact (mstr_sat_l _ (extension_ext_l O hZF hU) η (.bound 3) (.bound 2) (.bound 3) (.bound 1) .newest).mpr
    (two_step_master_second_value_l O hZFC hU hω hχ hωχ hH hJ hSub hElem hB hR hz hC hS h L hvq hm hq
      (hη 3) (hη 2) (hη 0) (ng_value_l O hZF hU hμ (hη 1)))

theorem two_step_master_second_l {ω χ H c J d N K v q t μ} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N K) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hC : M.mem C N) (hS : M.mem S N)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
    (hvq : KPair_d M v q t) (hm : Mstr_d M C S C N v) (hμ : Ng_name_d M B N μ) :
    Forces_d M B R z mstr_body_m (mstr_env_l A T μ t) q := by
  let ρP : Env M 9 := ((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push A).push T).push W).push C).push S
  let ρM : Env M 17 := (((((((ρP.push ω).push χ).push H).push c).push J).push d).push N).push K
  let ρ : Env M 21 := (((ρM.push v).push q).push t).push μ
  let es : Fin 4 → Term 21 := Fin.cases (.bound 1) (Fin.cases .newest (Fin.cases (.bound 15) (fun _ => .bound 16)))
  let model : Formula 1 21 := .conj (Formula.isOmega (.bound 11))
    (.conj (Formula.isRegularCardinal kpair_convention_l (.bound 10)) (.conj (.mem (.bound 11) (.bound 10))
    (.conj (h_m (𝒞 := kpair_convention_l) (.bound 10) (.bound 9))
    (.conj (smem_m (𝒞 := kpair_convention_l) (.bound 8) (.bound 9) (.bound 7))
    (.conj (ssub_m (𝒞 := kpair_convention_l) (.bound 8) (.bound 6) (.bound 9) (.bound 7) (.bound 5) (.bound 4))
    (.conj (selem_m (𝒞 := kpair_convention_l) (.bound 11) (.bound 8) (.bound 6))
    (.conj (.mem (.bound 20) (.bound 5)) (.conj (.mem (.bound 19) (.bound 5))
    (.conj (.mem (.bound 18) (.bound 5)) (.conj (.mem (.bound 13) (.bound 5)) (.mem (.bound 12) (.bound 5))))))))))))
  let step : Formula 1 21 := .conj
    (two_step_m (.bound 20) (.bound 19) (.bound 18) (.bound 17) (.bound 16) (.bound 15) (.bound 14) (.bound 13) (.bound 12))
    (.conj (cond_order_m (.bound 13) (.bound 12) (.bound 13))
    (.conj (name_m (.bound 20) (.bound 15))
    (.conj (kpair_m (.bound 3) (.bound 2) (.bound 1))
    (.conj (mstr_m (.bound 13) (.bound 12) (.bound 13) (.bound 5) (.bound 3))
      (ng_name_m (.bound 20) (.bound 5) .newest)))))
  let α : Formula 1 21 := .conj (cond_order_m (.bound 20) (.bound 19) (.bound 18)) (.conj model step)
  let β : Formula 1 21 := force_at_m mstr_body_m es (.bound 20) (.bound 19) (.bound 18) (.bound 2)
  have hes : ∀ i, (es i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α, model, step, Definitional.Formula.FreeClosed]
  have hβ : β.FreeClosed := force_at_closed_l _ _ _ _ _ _ mstr_body_closed_l hes rfl rfl rfl rfl
  have raw (X : SetTheory.Structure.{u}) (hX : X.Models ZFC) (η : Env X 21) : Formula.satisfies η α ↔
      let J := kpair_interpretation_l X hX.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hX)))
      Cond_order_d X (η.bound 20) (η.bound 19) (η.bound 18) ∧
      (X.IsOmega (η.bound 11) ∧ X.IsRegularCardinal J (η.bound 10) ∧ X.mem (η.bound 11) (η.bound 10) ∧
      H_d J (η.bound 10) (η.bound 9) ∧ Smem_d J (η.bound 8) (η.bound 9) (η.bound 7) ∧
      Ssub_d J (η.bound 8) (η.bound 6) (η.bound 9) (η.bound 7) (η.bound 5) (η.bound 4) ∧
      Selem_d J (η.bound 11) (η.bound 8) (η.bound 6) ∧ X.mem (η.bound 20) (η.bound 5) ∧
      X.mem (η.bound 19) (η.bound 5) ∧ X.mem (η.bound 18) (η.bound 5) ∧
      X.mem (η.bound 13) (η.bound 5) ∧ X.mem (η.bound 12) (η.bound 5)) ∧
      (Two_step_d X (η.bound 20) (η.bound 19) (η.bound 18) (η.bound 17) (η.bound 16) (η.bound 15)
        (η.bound 14) (η.bound 13) (η.bound 12) ∧ Cond_order_d X (η.bound 13) (η.bound 12) (η.bound 13) ∧
      Name_d X (η.bound 20) (η.bound 15) ∧ KPair_d X (η.bound 3) (η.bound 2) (η.bound 1) ∧
      Mstr_d X (η.bound 13) (η.bound 12) (η.bound 13) (η.bound 5) (η.bound 3) ∧
      Ng_name_d X (η.bound 20) (η.bound 5) (η.bound 0)) := by
    let J := kpair_interpretation_l X hX.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hX)))
    simp only [α, model, step, Formula.satisfies_conj_iff, cond_order_sat_l hX.1, Formula.satisfies_isOmega_iff,
      Formula.satisfies_isRegularCardinal_iff J hX.1, Formula.satisfies_mem_iff, h_sat_l J hX.1,
      smem_sat_l J, ssub_sat_l J, selem_sat_l J hX.1, two_step_sat_l hX.1,
      name_sat_l X hX.1, kpair_sat_l X hX.1, mstr_sat_l X hX.1, ng_name_sat_l X hX.1]
    rfl
  have result (X : SetTheory.Structure.{u}) (hX : Extensional X) (η : Env X 21) : Formula.satisfies η β ↔
      Forces_d X (η.bound 20) (η.bound 19) (η.bound 18) mstr_body_m
        (mstr_env_l (η.bound 16) (η.bound 15) (η.bound 0) (η.bound 1)) (η.bound 2) :=
    (force_at_sat_l _ η es _ _ _ _).trans (forces_env_l hX _ mstr_body_closed_l _ _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) _)
  apply (result M hZFC.1 ρ).mp
  apply FirstOrderSemantics.countable_consequence_l (Γ := ZFC) α β hα hβ
    (fun X hX e he η hp => ?_) hZFC ρ ((raw M hZFC ρ).mpr
      ⟨O, ⟨hω, hχ, hωχ, hH, ⟨hSub.source, hJ⟩, hSub, hElem, hB, hR, hz, hC, hS⟩, h, L, hT, hvq, hm, hμ⟩)
  obtain ⟨O', ⟨hω', hχ', hωχ', hH', hM', hSub', hElem', hB', hR', hz', hC', hS'⟩,
    h', L', hT', hvq', hm', hμ'⟩ := (raw X hX η).mp hp
  exact (result X hX.1 η).mpr (countable_second_l O' hX e he hω' hχ' hωχ' hH' hM'.2
    hSub' hElem' hB' hR' hz' hC' hS' h' L' hT' hvq' hm' hμ')

end YesMetaZFC.Model.Forcing.Internal
