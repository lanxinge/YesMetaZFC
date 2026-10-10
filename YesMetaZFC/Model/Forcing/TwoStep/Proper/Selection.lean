import YesMetaZFC.Model.Forcing.TwoStep.Proper.Composition
import YesMetaZFC.Model.Forcing.Proper.Generic.Successor
import YesMetaZFC.Model.Forcing.TwoStep.Witness
import YesMetaZFC.Model.Forcing.Internal.Functions.Rules

/-! # 二步主加强的实际名称选择

同一个内部初等 N 同时承担地阶段和泛型阶段的主条件。可数反射模型中的
全泛型判据把第二阶段主加强的存在性变为真正的力迫证书；库内最大值原理
再选择名称，二步合成定理给出原条件的实际主加强。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u

variable {M : SetTheory.Structure.{u}} {B R z b A T t W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

/-- 可数性只用于元层反射模型的泛型判据，所有 N、条件和名称仍是对象模型中的集合。 -/
theorem two_step_countable_master_l (e : Nat → M.Domain) (he : Function.Surjective e)
    {ω E x p s} (hω : M.IsOmega ω) (hP : Proper_d I ω B R z)
    (hE : M.CardinalLessOrEqual I E ω) (h : Two_step_d M B R z b A T W C S)
    (hW : Name_pool_d M B A t W) (L : Cond_order_d M C S C) (hT : Name_d M B T)
    (hx : M.mem x C) (hxp : KPair_d M x p s)
    (hNext : Forces_d M B R z (proper_exists_m .newest (.bound 1)) (ord_env_l M A T) p) :
    ∃ N y, M.MemberSubset E N ∧ M.CardinalLessOrEqual I N ω ∧
      Below_d M C S C y x ∧ Mstr_d M C S C N y := by
  obtain ⟨hs, hp, hsm⟩ := (two_step_mem_l h hxp).mp hx
  have hsN : Name_d M B s := ⟨W, hs, h.closed⟩
  have hA : Name_d M B A := ⟨W, h.root, h.closed⟩
  -- 把两个偏序参数和旧第二坐标加入同一可数种子。
  obtain ⟨E₁, h₁⟩ := KP.exists_insert (ZF.modelsKP hZF) E B
  obtain ⟨E₂, h₂⟩ := KP.exists_insert (ZF.modelsKP hZF) E₁ R
  obtain ⟨E₃, h₃⟩ := KP.exists_insert (ZF.modelsKP hZF) E₂ z
  obtain ⟨E₄, h₄⟩ := KP.exists_insert (ZF.modelsKP hZF) E₃ s
  have hc := ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω
    (ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω hE h₁) h₂) h₃) h₄
  obtain ⟨χ, H, c, J, N, d, K, q, hχ, hωχ, hH, hJ, hSub, hElem, hEN, hN, hqp, hm, hg⟩ :=
    ng_next_master_l O hZFC hω hP hc hp.1 hp.2.1 hA hT hNext
  have hE₃N a ha := hEN a ((h₄ a).mpr (Or.inl ha))
  have hE₂N a ha := hE₃N a ((h₃ a).mpr (Or.inl ha))
  have hE₁N a ha := hE₂N a ((h₂ a).mpr (Or.inl ha))
  have hBN := hE₁N B ((h₁ B).mpr (Or.inr rfl))
  have hRN := hE₂N R ((h₂ R).mpr (Or.inr rfl))
  have hzN := hE₃N z ((h₃ z).mpr (Or.inr rfl))
  have hsN' := hEN s ((h₄ s).mpr (Or.inr rfl))
  obtain ⟨μ, hμ⟩ := ng_name_exists_l M hZF B N
  let ρ := mstr_env_l A T μ s
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases hsN (Fin.cases hμ.1 (Fin.cases hT (fun _ => hA)))
  let φ : Formula 1 4 := .existsE (.conj (.mem .newest (.bound 4)) mstr_lower_s.body)
  have hφ : φ.FreeClosed := by simp [φ, Definitional.Formula.FreeClosed, mstr_lower_s.freeClosed]
  have hf : Forces_d M B R z φ ρ q := by
    apply forces_countable_l O hZF e he φ hφ ρ hρ hm.1 hm.2.1
    intro U hU hq η hv
    let V := extension_l M hZF B R z U
    obtain ⟨Z, Q, D, hZ, hQ, hD, hMaster⟩ := hg U hU hq
    have hQeq := qval_unique_l hQ (hv 3)
    have hDeq := qval_unique_l hD (hv 2)
    have hZeq : Z = η.bound 1 := (extension_ext_l O hZF hU).eq_of_same_members _ _
      (fun y => (hZ y).trans (ng_value_l O hZF hU hμ (hv 1) y).symm)
    subst Q D Z
    have hsZ := (hZ (η.bound 0)).mpr ⟨s, hsN', hv 0⟩
    have hsQ := (qval_mem_forcing_l O hZF hU (hv 0) (hv 3)).mp
      ⟨p, hU.upward q p hq hp.1 hqp.2.2, hsm⟩
    obtain ⟨v, hvq, hvm⟩ := hMaster (η.bound 0) hsZ hsQ
    refine (Formula.satisfies_exists_iff η _).mpr ⟨v, (Formula.satisfies_conj_iff _ _ _).mpr ⟨?_, ?_⟩⟩
    · exact (Formula.satisfies_mem_iff _ _ _).mpr hvq.1
    · apply (Formula.satisfies_conj_iff _ _ _).mpr
      refine ⟨(below_sat_l V (extension_ext_l O hZF hU) _ _ _ _ _ _).mpr hvq, ?_⟩
      apply (Formula.satisfies_bind _ _ _).mpr
      exact (mstr_sat_l V (extension_ext_l O hZF hU) _ _ _ _ _ _).mpr hvm
  obtain ⟨a, y, haW, hyq, hy, hyF⟩ := two_step_witness_l O hZFC mstr_lower_s ρ 3 hρ h hW
    (below_trans_l O h.base hqp hp) hf
  obtain ⟨har, hForce⟩ := force_mstr_lower_l hZF.1 hyF
  have hBelow : Below_d M C S C y x := ⟨hy,
    (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hy)),
    (two_step_le_l h hy hx hyq hxp).mpr ⟨hqp, har⟩⟩
  exact ⟨N, y, (fun a ha => hE₁N a ((h₁ a).mpr (Or.inl ha))), hN, hBelow,
    two_step_master_l O hZFC hω hχ hωχ hH hJ.2 hSub hElem hBN hRN hzN h L hT hy hyq hm hμ hForce⟩

end YesMetaZFC.Model.Forcing.Internal
