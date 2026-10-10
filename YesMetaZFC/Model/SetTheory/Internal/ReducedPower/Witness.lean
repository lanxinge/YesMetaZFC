import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Update
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.Model.SetTheory.Internal.TruthRules

/-! # 存在量词的实际内部见证函数

先在大集合上统一选取见证，再在其余指标取固定值，得到全定义的模型内函数图。
选择只用于此统一化步骤；逆向传输和整族赋值更新均沿用 ZF 层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rp_exists_l (hZFC : M.Models ZFC) {ω D Q E U V i Z B}
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E)
    (hU : ∀ A, M.mem A U → M.MemberSubset A D) (hQ : ∃ x, M.mem x Q) (hi : M.mem i ω)
    (hB : Rp_ex_d I Q E i Z B) : Rp_holds_d I U V B ↔
      ∃ f W, Fn0_d D Q f ∧ Rp_update_d I D E V i f W ∧ Rp_holds_d I U W Z := by
  let hZF := ZFC.models_zf_l hZFC
  constructor
  · rintro ⟨A, hAU, hA⟩
    obtain ⟨z, hz⟩ := hQ
    let ρ : Env M 5 := ⟨Fin.cases z (Fin.cases Z (Fin.cases i (Fin.cases V (fun _ => A)))), fun _ => Q⟩
    let φ : BinarySchema 5 := {
      body := .disj
        (.conj (.mem (.bound 1) (.bound 6)) (.existsE (Formula.existsMem (.bound 4) (.conj
          (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 7))
          (senv_update_m (𝒞 := 𝒞) (.bound 1) (.bound 6) (.bound 2) .newest)))))
        (.conj (.neg (.mem (.bound 1) (.bound 6))) (Formula.extensionalEq .newest (.bound 2))) }
    have sat d x : φ.denote ρ d x ↔
        (M.mem d A ∧ ∃ v w, M.mem w Z ∧ M.PairMember I d v V ∧ Senv_update_d I v i x w) ∨ (¬ M.mem d A ∧ x = z) := by
      simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff,
        Formula.satisfies_orderedPairMem_iff I, senv_update_sat_l I hZF.1, Formula.satisfies_neg_iff,
        Formula.satisfies_extensionalEq_iff_eq hZF.1]
      rfl
    obtain ⟨f, hf, select⟩ := ZFC.uniformize_formula_l (kp_pair_l (ZF.modelsKP hZF)) hZFC φ ρ
      (X := D) (Y := Q) (fun d _ => by
        classical
        by_cases hd : M.mem d A
        · obtain ⟨v, hdv, hv⟩ := hA d hd
          obtain ⟨_, x, hx, w, hw, he⟩ := (hB v).mp hv
          exact ⟨x, hx, (sat d x).mpr (Or.inl ⟨hd, v, w, hw, hdv, he⟩)⟩
        · exact ⟨z, hz, (sat d z).mpr (Or.inr ⟨hd, rfl⟩)⟩)
    have hf' := fn0_of_function_l (ZF.modelsKP hZF) hf
    obtain ⟨W, hW⟩ := rp_update_exists_l I hZF hE hV hi hf'
    refine ⟨f, W, hf', hW, A, hAU, fun d hd => ?_⟩
    obtain ⟨x, _, hdx⟩ := hf'.2.1 d (hU A hAU d hd)
    rcases (sat d x).mp (select d x hdx) with ⟨_, v, w, hw, hdv, he⟩ | ⟨hn, _⟩
    · exact ⟨w, (hW.2 d w).mpr ⟨hU A hAU d hd, v, x, hdv, hdx, he⟩, hw⟩
    · exact (hn hd).elim
  · rintro ⟨f, W, hf, hW, h⟩
    exact rp_ex_update_l I hV hf hW hB h

/-- 存在量词的真值集与见证函数一并给出，所有中间集合均在模型内部构造。 -/
theorem rp_quantifier_l (hZFC : M.Models ZFC) {ω D Q E U V i}
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E)
    (hU : ∀ A, M.mem A U → M.MemberSubset A D) (hQ : ∃ x, M.mem x Q) (hi : M.mem i ω) (Z : M.Domain) :
    ∃ B, Rp_ex_d I Q E i Z B ∧ (Rp_holds_d I U V B ↔
      ∃ f W, Fn0_d D Q f ∧ Rp_update_d I D E V i f W ∧ Rp_holds_d I U W Z) := by
  obtain ⟨B, hB⟩ := rp_ex_exists_l I (ZFC.models_zf_l hZFC) Q E i Z
  exact ⟨B, hB, rp_exists_l I hZFC hE hV hU hQ hi hB⟩

/-- 直接消费合法内部程序行及其实际真值表，不假定公式码外部标准。 -/
theorem rp_quantifier_row_l (hZFC : M.Models ZFC) {ω D Q R E U V F n H r c i j Z B}
    (hF : Sfm_d I ω n F) (hH : Seval_d I Q R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 3 c i j) (hB : M.PairMember I r B H) (hZ : M.PairMember I j Z H)
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E)
    (hU : ∀ A, M.mem A U → M.MemberSubset A D) (hQ : ∃ x, M.mem x Q) :
    Rp_holds_d I U V B ↔ ∃ f W, Fn0_d D Q f ∧ Rp_update_d I D E V i f W ∧ Rp_holds_d I U W Z := by
  let hZF := ZFC.models_zf_l hZFC
  have hi : M.mem i ω := by
    rcases hF.2.2 r c hc with ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ <;>
      obtain ⟨he, rfl, rfl⟩ := sop_injective_l I (ZF.modelsKP hZF) hs ht <;> cases he
    exact ha
  apply rp_exists_l I hZFC hE hV hU hQ hi
  intro v
  have row := (seval_row_l I hZF hF hH hc hB v).trans (and_congr_right fun _ =>
    snode_decode_l I (ZF.modelsKP hZF) 3 hs)
  refine row.trans ⟨?_, ?_⟩
  · rintro ⟨hv, Z', hZ', x, w, hx, he, hw⟩
    have eq := hH.1.2.1.2 j Z' Z hZ' hZ
    exact ⟨hv, x, hx, w, eq ▸ hw, he⟩
  · rintro ⟨hv, x, hx, w, hw, he⟩
    exact ⟨hv, Z, hZ, x, w, hx, he, hw⟩

end YesMetaZFC.SetTheory.Internal
