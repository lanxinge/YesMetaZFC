import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 原公式在完整类型中的实际查询码

给原公式每个参数一个合法名字，就自动编译出类型查询。名字可以重复或置换，
并可同时引用实现元组、指定常量和参数域中的任意集合常量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_source_l {ω c Z R n s δ U D t : M.Domain}
    (hω : M.IsOmega ω) (h : Tt_realized_d I ω c Z R n s δ U D t)
    {d : Nat} (φ : Formula 1 d) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d) (a : Fin d → M.Domain)
    (names : ∀ i, Tn_name_d n U (a i)) (values : ∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) :
    ∃ p, M.mem p D ∧ (M.mem p t ↔ Formula.satisfies ρ φ) := by
  obtain ⟨N, E, hN, hE, hD⟩ := h.pool
  obtain ⟨q, m, F, k, v, hq, hv, compile⟩ := source_compile_l I hZF hω φ hφ
  obtain ⟨z, hz⟩ := sc_num_exists_l I hZF hω hq
  obtain ⟨b, hb⟩ := num_exists_l (ZF.modelsKP hZF) d
  obtain ⟨B, hB⟩ := ZF.exists_functionSpace hZF I b N
  have injective : Function.Injective v := fun i j eq =>
    Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (eq.symm ▸ hv j))
  obtain ⟨e, heB, params⟩ := senv_params_l I hZF hB ⟨n, (hN n).mpr (Or.inr (Or.inl rfl))⟩ v a injective
    (fun i => num_lt_l hZF.1 (hv i) hb i.isLt) (fun i => (hN (a i)).mpr (names i))
  have he := (hB e).mp heB
  obtain ⟨r, hr, fnr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals hZF n h.finite)
    h.tuple h.point h.constants hN (fn0_of_function_l (ZF.modelsKP hZF) he)
  obtain ⟨f, hf, fnf⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fnr) h.point
  obtain ⟨G, hG⟩ := ZF.exists_functionSpace hZF I ω Z
  have match_params i : M.PairMember I (v i) (ρ.bound i).val f :=
    (hf.2 (v i) (ρ.bound i).val).mpr ⟨num_mem_l hZF.1 hω (hv i), Or.inl
      ⟨num_lt_l hZF.1 (hv i) hb i.isLt, (hr.2 (v i) (ρ.bound i).val).mpr ⟨a i, params i, values i⟩⟩⟩
  obtain ⟨p, hp⟩ := (I).total z e
  have hbω := num_mem_l hZF.1 hω hb
  have hzω := sc_num_natural_l I hZF hω hz
  have hpD := (hD p).mpr ⟨z, hzω, e, (hE e).mpr ⟨b, hbω, he⟩, hp⟩
  refine ⟨p, hpD, (h.truth p).trans ((and_iff_right hpD).trans ?_)⟩
  exact (tt_query_decode_l I (ZF.modelsKP hZF) hp hzω hbω he.2.1 hr hf).trans
    ((sc_sat_decode_l I hZF hω hz).trans ((satisfies_decode_l I hZF.1 h.model hq hG).trans
      (compile Z R h.model.2.1 G hG f ((hG f).mpr fnf) ρ match_params)))

end YesMetaZFC.SetTheory.Internal
