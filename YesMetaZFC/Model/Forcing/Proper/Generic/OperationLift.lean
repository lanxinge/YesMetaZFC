import YesMetaZFC.Model.Forcing.Proper.Generic.Operations

/-! # 主条件把统一有限元选择提升到 N[G]

判定运算的闭包使稠密集属于 N。主条件取得 p∈N∩G 后，把 p 追加到原参数列，
见证运算的闭包再给出 N 内名称。判定的否定分支由力迫真值及泛型有向性排除。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
include O hU

/-- 已实际装配的两张运算图在同一个 N 上闭合，便统一提升全部标签及内部有限参数列。 -/
theorem ng_operation_lift_l {n} (φ : UnarySchema (n+3)) (ρ : Env M n)
    {b ω X u T S D K L N q m f l a i c d s}
    (hω : M.IsOmega ω) (hS : Fseq_space_d I ω X S) (hD : M.IsCartesianProduct I D T S)
    (hK : M.IsSetFunctionFromTo I K D X) (hL : M.IsSetFunctionFromTo I L D X)
    (hk : ∀ k A, Entry_d M k A K → Ng_dense_op_d φ ρ B R z b X k A)
    (hl : ∀ k t, Entry_d M k t L → Ng_select_op_d I φ ρ B R z b ω X u k t)
    (hNX : M.MemberSubset N X) (hKN : Fc_closed_d I ω T K N) (hLN : Fc_closed_d I ω T L N)
    (hm : Mstr_d M B R z N q) (hq : U q) (hmm : M.mem m ω) (hf : M.IsSetFunctionFromTo I f m N)
    (hlt : M.mem l T) (hla : KPair_d M l a i) (hc : Check_d M b a c) (hd : Check_d M b i d)
    (hs : Nseq_d M B b f s) (η : Env E (n+3))
    (hη : Env_val_d hZF (((ρ.push c).push d).push s) η)
    (hex : ∃ x, Ng_mem_d M B R z U X x ∧ φ.denote η x) :
    ∃ y, Ng_mem_d M B R z U N y ∧ φ.denote η y := by
  obtain ⟨k, hlf⟩ := (I).total l f
  have hfS := (hS f).mpr ⟨m, hmm, hf.mono_target_l I hNX⟩
  obtain ⟨A, _, hkA⟩ := hK.2.2 k ((hD k).mpr ⟨l, hlt, f, hfS, hlf⟩)
  have hAN := hKN A ⟨m, f, l, k, hmm, hf, hlt, hlf, hkA⟩
  obtain ⟨l', f', hk', hA⟩ := hk k A hkA
  obtain ⟨hll, hff⟩ := kpair_injective_l M hk' hlf
  subst l' f'
  obtain ⟨p, hpN, hpA, hpU⟩ := mstr_generic_l hZF hU hq hm hAN (hA.dense_l O)
  have active : Ng_rule_has_d φ ρ B R z b X l f p := by
    rcases ((hA p).mp hpA).2.2 with h | h
    · exact h
    · obtain ⟨x, ⟨t, htX, htx⟩, hφ⟩ := hex
      have hEnv := env_val_push_l hZF hη htx
      obtain ⟨r, hr, htφ⟩ := (forcing_truth_l O hZF hU φ.body φ.freeClosed _ _ hEnv).mpr hφ
      obtain ⟨v, hv, hvp, hvr⟩ := hU.directed p r hpU hr
      have hv' := hU.proper v hv
      have htφv := (forces_regular_l O hZF φ.body _ (fun a => qval_name_l (hEnv a))).1
        r v (hU.proper r hr).1 ⟨hv'.1, hv'.2, hvr⟩ htφ
      exact (h v ⟨hv'.1, hv'.2, hvp⟩ ⟨t, htX,
        (ng_rule_decode_l hZF φ ρ hla hc hd hs).mpr ⟨qval_name_l htx, htφv⟩⟩).elim
  obtain ⟨j, F, hj, hF, hEnd⟩ := ZF.fseq_end_exists_l I hZF hω hmm hf hpN
  obtain ⟨k', hk'⟩ := (I).total l F
  have hFS := (hS F).mpr ⟨j, hj, hF.mono_target_l I hNX⟩
  obtain ⟨t, _, hkt⟩ := hL.2.2 k' ((hD k').mpr ⟨l, hlt, F, hFS, hk'⟩)
  have htN := hLN t ⟨j, F, l, k', hj, hF, hlt, hk', hkt⟩
  obtain ⟨l', F', hk'', ht⟩ := hl k' t hkt
  obtain ⟨hll, hFF⟩ := kpair_injective_l M hk'' hk'
  subst l' F'
  have ht : Ng_rule_d φ ρ B R z b l f p t := by
    rcases ht with ⟨g, r, hEnd', ht⟩ | ⟨hn, _⟩
    · obtain ⟨hgf, hrp⟩ := fseq_end_unique_l I hZF.1 hEnd' hEnd
      subst g r
      exact ht
    · obtain ⟨v, hv, hv'⟩ := active
      exact (hn ⟨v, hv, f, p, hEnd, hv'⟩).elim
  obtain ⟨htName, htφ⟩ := (ng_rule_decode_l hZF φ ρ hla hc hd hs).mp ht
  obtain ⟨y, hy⟩ := name_value_l (R := R) (z := z) (U := U) htName
  exact ⟨y, ⟨t, htN, hy⟩, (forcing_truth_l O hZF hU φ.body φ.freeClosed _ _
    (env_val_push_l hZF hη hy)).mp ⟨p, hpU, htφ⟩⟩

end YesMetaZFC.Model.Forcing.Internal
