import YesMetaZFC.Model.Forcing.Iteration.Names.Dense
import YesMetaZFC.Model.Forcing.Internal.Check.Relation
import YesMetaZFC.Model.Forcing.Internal.Maximum.Basic

/-! # 指定稠密集中的商条件名称

先以 ZF 证明稠密加强的存在力迫，再由内部最大值原理在原前缀上选取名称。
输出名称仍属于同一个 N 的商条件集，且在原模型序关系中加强输入名称。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def row_dense_s : UnarySchema 4 := {
  body := .conj (.mem .newest (.bound 4))
    (.conj (.mem .newest (.bound 3)) (entry_m .newest (.bound 1) (.bound 2)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }

def row_dense_env_l (K E V τ : M.Domain) : Env M 4 :=
  (((⟨fun _ => K, fun _ => K⟩ : Env M 1).push E).push V).push τ

/-- 遇到指定稠密集的存在力迫只需 ZF；没有先验名称选择假设。 -/
theorem row_dense_force_l (hZF : M.Models ZF) {ω χ H c J d N S α B R e D V E p τ K ν η}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H J N S)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hD : M.mem D N) (hV : M.mem V N) (hE : M.mem E N)
    (h : Row_stage_d M α B R e) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hd : Dense_set_d M D V D E) (hm : Mstr_d M B R B N p)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B e D N K)
    (hτ : Name_d M B τ) (hτK : Mem_force_d M B R B p τ K)
    (hν : Check_d M e V ν) (hη : Check_d M e E η) :
    Forces_d M B R B (.existsE row_dense_s.body) (row_dense_env_l K η ν τ) p := by
  let ρ := row_dense_env_l K η ν τ
  have hn (x s : M.Domain) (hs : Check_d M e x s) := check_name_l M (check_range_l M hZF) h.base hs
  have hρ : ∀ t : Term 4, Name_d M B (t.eval ρ) := by
    intro t
    cases t with
    | free _ => exact hK.1
    | bound i => exact Fin.cases hτ (Fin.cases (hn V ν hν) (Fin.cases (hn E η hη) (fun _ => hK.1))) i
  apply (forces_regular_l h.order hZF _ ρ hρ).2 p hm.1 hm.2.1
  intro q hq
  obtain ⟨a, v, r₀, haq, hvr, har₀, heq⟩ := hτK.2 q hq
  obtain ⟨hr₀, r, hrD, hrN, hrpre, hrv⟩ := (hK.2 v r₀).mp hvr
  obtain ⟨b, s, s₀, hba, hsN, hsD, hsE, hsr, hs₀, hspre, hbs₀⟩ :=
    row_dense_prefix_l hZF hω hχ hH hJ hSub hElem hB hR hD hV hE hrN h L k hd hrD hr₀ hrpre hm
      (below_trans_l h.order hm.1 haq hq) har₀
  obtain ⟨σ, hsσ, hσ, _⟩ := zf_check_l M hZF h.base s
  have hσK := row_quot_check_l hZF h.order h.base hK hsD hsN hs₀ hspre hsσ hba.1 hbs₀
  have hση := check_mem_force_l h.order hZF h.base hsσ hη hba.1 (h.top b hba.1) hsE
  have hσv := check_rel_force_l h.order hZF h.base hν hsσ hrv ⟨hba.1, hba.2.1, h.top b hba.1⟩ hsr
  have heq' := eq_force_lower_l h.order hZF hτ (hn r v hrv) a b haq.1 hba heq
  let φ : UnarySchema 2 := { body := entry_m (.bound 1) .newest (.bound 2) }
  have hστ : Rel_force_d M B R B ν b σ τ := (forces_name_congr_l h.order hZF φ (ord_env_l M σ ν)
    (Fin.cases hσ (fun _ => hn V ν hν)) (hn r v hrv) hτ hba.1 hba.2.1
      (eq_force_symm_l hZF hτ (hn r v hrv) heq')).mp hσv
  have hf : Forces_d M B R B row_dense_s.body (ρ.push σ) b := (forces_conj_l _ _ _ _).mpr
    ⟨(forces_mem_l hZF.1 _ _ _ _).mpr hσK, (forces_conj_l _ _ _ _).mpr
      ⟨(forces_mem_l hZF.1 _ _ _ _).mpr hση, (force_entry_l hZF.1 _ _ _ _ _).mpr hστ⟩⟩
  have hρσ : ∀ t : Term 5, Name_d M B (t.eval (ρ.push σ)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hσ (fun j => hρ (.bound j)) i
  exact ⟨b, below_trans_l h.order hq.1 hba haq,
    forces_exists_intro_l h.order hZF.1 hσ (forces_regular_l h.order hZF _ _ hρσ).1 hba.1 hf⟩

/-- 任意阶段间，自动选择进入 E∩N 的商加强名称，原前缀 p 不作加强。 -/
theorem row_dense_name_l (hZFC : M.Models ZFC) {ω χ H c J d N S α B R e D V E p τ K}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) c d H J N S)
    (hElem : Selem_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hD : M.mem D N) (hV : M.mem V N) (hE : M.mem E N)
    (h : Row_stage_d M α B R e) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) α B R D V)
    (hd : Dense_set_d M D V D E) (hm : Mstr_d M B R B N p)
    (hK : Row_quot_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) α B e D N K)
    (hτ : Name_d M B τ) (hτK : Mem_force_d M B R B p τ K) :
    ∃ σ ν η, Name_d M B σ ∧ Check_d M e V ν ∧ Check_d M e E η ∧
      Mem_force_d M B R B p σ K ∧ Mem_force_d M B R B p σ η ∧ Rel_force_d M B R B ν p σ τ := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨ν, hν, hνn, _⟩ := zf_check_l M hZF h.base V
  obtain ⟨η, hη, hηn, _⟩ := zf_check_l M hZF h.base E
  let ρ := row_dense_env_l K η ν τ
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases hτ (Fin.cases hνn (Fin.cases hηn (fun _ => hK.1)))
  obtain ⟨σ, hσ, _, hmax⟩ := maximum_l h.order hZFC row_dense_s ρ hρ
  have hex := row_dense_force_l hZF hω hχ hH hJ hSub hElem hB hR hD hV hE h L k hd hm hK hτ hτK hν hη
  have hf : Forces_d M B R B row_dense_s.body (ρ.push σ) p := (hmax p hm.1 hm.2.1).mp hex
  obtain ⟨hσK, hrest⟩ := (forces_conj_l (.mem .newest (.bound 4))
    (.conj (.mem .newest (.bound 3)) (entry_m .newest (.bound 1) (.bound 2))) (ρ.push σ) p).mp hf
  obtain ⟨hση, hστ⟩ := (forces_conj_l (.mem .newest (.bound 3)) (entry_m .newest (.bound 1) (.bound 2)) (ρ.push σ) p).mp hrest
  have hσK := (forces_mem_l hZF.1 .newest (.bound 4) (ρ.push σ) p).mp hσK
  have hση := (forces_mem_l hZF.1 .newest (.bound 3) (ρ.push σ) p).mp hση
  have hστ := (force_entry_l hZF.1 (ρ.push σ) p .newest (.bound 1) (.bound 2)).mp hστ
  exact ⟨σ, ν, η, hσ, hν, hη, hσK, hση, hστ⟩

end YesMetaZFC.Model.Forcing.Internal
