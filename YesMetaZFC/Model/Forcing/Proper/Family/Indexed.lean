import YesMetaZFC.Model.Forcing.Proper.Family.IndexedSyntax

/-! # 所有阶段共用的实际判定与选择图

一次在整个输入集合上统一选择。无有效阶段解码的输入返回固定基点；有效
输入读取真实阶段偏序和 H 的规范名称。切片定理恢复每个阶段原来的运算规格。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 两类阶段运算均在原 ZFC 中实际存在；输入域无须在外部可数。 -/
theorem ng_joint_exists_l (hZFC : M.Models ZFC) (k : Bool) (ω δ F G b w D : M.Domain) {X u}
    (hu : M.mem u X) (hX : ∀ i B, M.mem i δ → Entry_d M i B F →
      ∀ A, M.MemberSubset A B → M.mem A X) : ∃ K,
    M.IsSetFunctionFromTo (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) K D X ∧
    ∀ p t, Entry_d M p t K → Ng_joint_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) k ω δ F G b X w u p t := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 8 := (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push δ).push F).push G).push b).push X).push w).push u
  let φ : BinarySchema 8 := {
    body := ng_joint_m k (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5)
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ p t : φ.denote ρ p t ↔ Ng_joint_d I k ω δ F G b X w u p t :=
    ng_joint_sat_l I hZFC.1 _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨K, hK, hk⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := D) (Y := X) (by
    intro p _
    by_cases hi : ∃ i B R μ a, Ng_index_d I ω δ F G X p i B R μ a
    · obtain ⟨i, B, R, μ, a, hi⟩ := hi
      obtain ⟨l, f, s, _, _, ha⟩ := hi.2.2.2.2
      let η := ng_elementary_env_l w μ u
      cases k
      · obtain ⟨A, hA⟩ := ng_rule_decide_exists_l hZF (ssk_mem_s kpair_convention_l) η B R B b X l f
        exact ⟨A, hX i B hi.1 hi.2.1 A (fun p hp => ((hA p).mp hp).1),
          (hφ p A).mpr (Or.inl ⟨i, B, R, μ, a, hi, l, f, ha, hA⟩)⟩
      · by_cases ht : ∃ t, M.mem t X ∧ Ng_select_at_d I (ssk_mem_s kpair_convention_l) η B R B b ω l f t
        · obtain ⟨t, htX, ht⟩ := ht
          exact ⟨t, htX, (hφ p t).mpr (Or.inl ⟨i, B, R, μ, a, hi, l, f, ha, Or.inl ht⟩)⟩
        · exact ⟨u, hu, (hφ p u).mpr (Or.inl ⟨i, B, R, μ, a, hi, l, f, ha, Or.inr ⟨ht, rfl⟩⟩)⟩
    · exact ⟨u, hu, (hφ p u).mpr (Or.inr ⟨hi, rfl⟩)⟩)
  exact ⟨K, hK, fun p t hp => (hφ p t).mp (hk p t hp)⟩

/-- 有效阶段的唯一解码排除默认分支，并把共同选择恢复为该阶段的原运算。 -/
theorem ng_joint_resolve_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {k ω δ F G b X w u p t i B R μ a}
    (hF : ∀ i B C, Entry_d M i B F → Entry_d M i C F → B = C)
    (hG : ∀ i R S, Entry_d M i R G → Entry_d M i S G → R = S)
    (hi : Ng_index_d I ω δ F G X p i B R μ a) (h : Ng_joint_d I k ω δ F G b X w u p t) :
    Ng_index_op_d I k B R b ω X w μ u a t := by
  rcases h with ⟨j, C, S, ν, d, hj, ht⟩ | ⟨hn, _⟩
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ng_index_unique_l I hE hF hG hj hi
    exact ht
  · exact (hn ⟨i, B, R, μ, a, hi⟩).elim

/-- 一个阶段属于 N 时，共同闭包自动给出该阶段的完整判定／选择闭包。 -/
theorem ng_joint_slice_l (hZF : M.Models ZF) {k ω δ F G b X w u S T D K i B R μ}
    (hω : M.IsOmega ω)
    (hS : Fseq_space_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω X S)
    (hD : M.IsCartesianProduct (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) D T S)
    (hK : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) K D X)
    (hF : M.IsSetFunction (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F)
    (hG : M.IsSetFunction (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) G)
    (hk : ∀ p t, Entry_d M p t K → Ng_joint_d
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω δ F G b X w u p t)
    (hi : M.mem i δ) (hiX : M.mem i X) (hB : Entry_d M i B F) (hR : Entry_d M i R G)
    (hμ : Ng_name_d M B X μ) : ∃ L,
    M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) L D X ∧
    (∀ a t, Entry_d M a t L → Ng_index_op_d
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k B R b ω X w μ u a t) ∧
    ∀ N, M.mem i N → Fc_closed_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω T K N →
      Fc_closed_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω T L N := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨L, hL, hl, hc⟩ := ZF.fc_slice_l I hZF hω hS hD hK hiX
  refine ⟨L, hL, fun a t hat => ?_, hc⟩
  obtain ⟨l, f, s, p, ha, hs, hp, hpt⟩ := ((hl a t).mp hat).2
  exact ng_joint_resolve_l I hZF.1 hF.2 hG.2
    ⟨hi, hB, hR, hμ, l, f, s, hp, hs, ha⟩ (hk p t hpt)

end YesMetaZFC.Model.Forcing.Internal
