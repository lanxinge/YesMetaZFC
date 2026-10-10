import YesMetaZFC.Model.Forcing.Applications.Cohen.NameSyntax
import YesMetaZFC.Model.Forcing.Internal.Maximum.Unique
import YesMetaZFC.Model.Forcing.Internal.Reflection.Countermodel

/-! # Cohen 后继的全局名称装配

给定任意添加量名称，一次取得适用于全部正条件的条件集名称与序关系名称。
存在性与唯一性均由原 ZF 公式给出，唯一见证混合产生确定的规范名称。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)

include O hZF

/-- 添加量可以是任意名称；全局 Cohen 条件、关系和顶具有唯一的规范名称三元组。 -/
theorem cohen_names_l {κ} (hκ : Name_d M B κ) :
    ∃ A T t, Cohen_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z κ A T t ∧
      ∀ A' T' t', Cohen_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z κ A' T' t' →
        A' = A ∧ T' = T ∧ t' = t := by
  let π : Formula 1 2 := preord_m .newest (.bound 1)
  have hπ : π.FreeClosed := preord_m_freeClosed _ _ rfl rfl
  let j : Fin 2 → Term 3 := fun i => .bound i.castSucc
  let τ : Formula 1 3 := top_m (.bound 1) (.bound 2) .newest
  have hτ : τ.FreeClosed := top_m_freeClosed _ _ _ rfl rfl rfl
  let k : Fin 3 → Term 4 := fun i => .bound i.castSucc
  have hτk : (τ.bind k).FreeClosed :=
    (Definitional.Formula.freeClosed_bind_iff_of_closed _ (fun _ => rfl) _).mpr hτ
  let φ : BinarySchema 1 := {
    body := .conj (cohen_m (.bound 2) .newest (.bound 1))
      (.conj (π.bind j) (.existsE (τ.bind k)))
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed]
      exact ⟨cohen_m_freeClosed _ _ _ rfl rfl rfl,
        (Definitional.Formula.freeClosed_bind_iff_of_closed _ (fun _ => rfl) _).mpr hπ, hτk⟩ }
  let ρ : Env M 1 := ⟨fun _ => κ, fun _ => κ⟩
  let ψ : UnarySchema 1 := ⟨.existsE φ.body,
    by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed⟩
  let χ : UnarySchema 2 := ⟨φ.body, φ.freeClosed⟩
  let θ : UnarySchema 3 := ⟨τ.bind k, hτk⟩
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 1) :
      Formula.satisfies η (.existsE (.existsE φ.body)) := by
    let I := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))
    obtain ⟨Q, D, h⟩ := cohen_spec_exists_l I hN (η.bound 0)
    obtain ⟨hP, o, ho, ht⟩ := cohen_spec_top_l I hN h
    rw [Formula.satisfies_exists_iff]
    refine ⟨D, (Formula.satisfies_exists_iff _ _).mpr ⟨Q, ?_⟩⟩
    simp only [φ, Formula.satisfies_conj_iff]
    refine ⟨(cohen_sat_l I hN.1 _ _ _ _).mpr h, ?_, ?_⟩
    · rw [Formula.satisfies_bind]
      exact (preord_sat_l hN.1 _ _ _).mpr hP
    · apply (Formula.satisfies_exists_iff _ _).mpr
      refine ⟨o, ?_⟩
      rw [Formula.satisfies_bind]
      exact (top_sat_l hN.1 _ _ _ _).mpr ⟨ho, ht⟩
  have spec (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 2) Q
      (h : χ.denote η Q) : Cohen_spec_d (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN)))
        (η.bound 1) Q (η.bound 0) :=
    (cohen_sat_l _ hN.1 (η.push Q) _ _ _).mp ((Formula.satisfies_conj_iff _ _ _).mp h).1
  have uniqT (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 1) : Formula.satisfies η (unique_m ψ) := by
    apply (unique_sat_l hN.1 ψ η).mpr
    intro D D' hD hD'
    obtain ⟨Q, hQ⟩ := (Formula.satisfies_exists_iff _ _).mp hD
    obtain ⟨Q', hQ'⟩ := (Formula.satisfies_exists_iff _ _).mp hD'
    exact (cohen_spec_unique_l _ hN.1 (spec N hN (η.push D) Q hQ) (spec N hN (η.push D') Q' hQ')).2
  have uniqA (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 2) : Formula.satisfies η (unique_m χ) := by
    exact (unique_sat_l hN.1 χ η).mpr (fun Q Q' hQ hQ' =>
      (cohen_spec_unique_l _ hN.1 (spec N hN η Q hQ) (spec N hN η Q' hQ')).1)
  -- 先固定完整关系图，再固定条件集；两次均应用原 ZF 的唯一见证混合。
  obtain ⟨T, hT, hTN, ht, hUT⟩ := unique_maximum_l O hZF ψ ρ (fun _ => hκ)
    (fun p hp hz => forces_zf_valid_l O hZF _
      (by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed) valid ρ (fun _ => hκ) hp hz)
    (fun p hp hz => forces_zf_valid_l O hZF _ (unique_closed_l ψ) uniqT ρ (fun _ => hκ) hp hz)
  obtain ⟨A, hA, hAN, hf, hUA⟩ := unique_maximum_l O hZF χ (ρ.push T) (Fin.cases hT (fun _ => hκ)) ht
    (fun p hp hz => forces_zf_valid_l O hZF _ (unique_closed_l χ) uniqA (ρ.push T) (Fin.cases hT (fun _ => hκ)) hp hz)
  have hpre p (hp : M.mem p B) (hz : p ≠ z) : Forces_d M B R z π (ord_env_l M A T) p := by
    have h := (forces_conj_l _ _ _ p).mp ((forces_conj_l _ _ _ p).mp (hf p hp hz)).2 |>.1
    have h := (forces_bind_l hZF.1 π j _ p).mp h
    exact (forces_env_l hZF.1 π hπ _ (ord_env_l M A T) (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) p).mp h
  -- 在已经确定的 Cohen 偏序上，顶条件也由其语义规格唯一确定。
  let μ : Formula 1 3 := .imp (cohen_m (.bound 2) .newest (.bound 1)) (unique_m θ)
  have hμ : μ.FreeClosed := by
    simp only [μ, Definitional.Formula.FreeClosed]
    exact ⟨cohen_m_freeClosed _ _ _ rfl rfl rfl, unique_closed_l θ⟩
  have uniqTop (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 3) : Formula.satisfies η μ := by
    rw [Formula.satisfies_imp_iff]
    intro hc
    have hc := (cohen_sat_l (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))) hN.1 η _ _ _).mp hc
    apply (unique_sat_l hN.1 θ η).mpr
    intro s t hs ht
    have hs := (Formula.satisfies_bind _ _ _).mp hs
    have ht := (Formula.satisfies_bind _ _ _).mp ht
    exact cohen_spec_top_unique_l _ hN.1 hc ((top_sat_l hN.1 _ _ _ _).mp hs) ((top_sat_l hN.1 _ _ _ _).mp ht)
  have hη : ∀ v : Term 3, Name_d M B (v.eval ((ρ.push T).push A)) := by
    intro v
    cases v with
    | free _ => exact hκ
    | bound i => exact Fin.cases hA (Fin.cases hT (fun _ => hκ)) i
  have hUn p (hp : M.mem p B) (hz : p ≠ z) : Forces_d M B R z (unique_m θ) ((ρ.push T).push A) p :=
    forces_mp_l hZF.1 (forces_regular_l O hZF _ _ hη).1 (forces_regular_l O hZF _ _ hη) hp hz
      (forces_zf_valid_l O hZF μ hμ uniqTop _ (fun i => hη (.bound i)) hp hz)
      ((forces_conj_l _ _ _ p).mp (hf p hp hz)).1
  obtain ⟨t, ht, htN, htop', hUt⟩ := unique_maximum_l O hZF θ ((ρ.push T).push A) (fun i => hη (.bound i))
    (fun p hp hz => ((forces_conj_l _ _ _ p).mp ((forces_conj_l _ _ _ p).mp (hf p hp hz)).2).2) hUn
  have htop p (hp : M.mem p B) (hz : p ≠ z) : Forces_d M B R z τ (top_env_l A T t) p := by
    have h := (forces_bind_l hZF.1 τ k _ p).mp (htop' p hp hz)
    exact (forces_env_l hZF.1 τ hτ _ (top_env_l A T t)
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) p).mp h
  refine ⟨A, T, t, ⟨⟨hA, hT, ht⟩, fun s hs => hs.elim (fun he => he.symm ▸ hAN)
    (fun hs => hs.elim (fun he => he.symm ▸ hTN) (fun he => he.symm ▸ htN)),
    fun p hp hz => ((forces_conj_l _ _ _ p).mp (hf p hp hz)).1, hpre, htop⟩, ?_⟩
  -- 任意另一份规格先恢复原存在公式，再依次使用关系、条件集和顶的唯一性。
  have named A' T' (hA' : Name_d M B A') (hT' : Name_d M B T') :
      ∀ v : Term 3, Name_d M B (v.eval ((ρ.push T').push A')) := by
    intro v
    cases v with
    | free _ => exact hκ
    | bound i => exact Fin.cases hA' (Fin.cases hT' (fun _ => hκ)) i
  have top_body A' T' t'
      (h : Cohen_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z κ A' T' t')
      p (hp : M.mem p B) (hz : p ≠ z) : Forces_d M B R z θ.body (((ρ.push T').push A').push t') p := by
    apply (forces_bind_l hZF.1 τ k _ p).mpr
    exact (forces_env_l hZF.1 τ hτ _ (top_env_l A' T' t')
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) p).mpr (h.2.2.2.2 p hp hz)
  have body A' T' t'
      (h : Cohen_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z κ A' T' t')
      p (hp : M.mem p B) (hz : p ≠ z) : Forces_d M B R z χ.body ((ρ.push T').push A') p := by
    have hn : ∀ v : Term 4, Name_d M B (v.eval (((ρ.push T').push A').push t')) := by
      intro v
      cases v with
      | free _ => exact hκ
      | bound i => exact Fin.cases h.1.2.2 (fun i => named A' T' h.1.1 h.1.2.1 (.bound i)) i
    apply (forces_conj_l _ _ _ p).mpr
    refine ⟨h.2.2.1 p hp hz, (forces_conj_l _ _ _ p).mpr ⟨?_, ?_⟩⟩
    · apply (forces_bind_l hZF.1 π j _ p).mpr
      exact (forces_env_l hZF.1 π hπ _ (ord_env_l M A' T')
        (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) p).mpr (h.2.2.2.1 p hp hz)
    · exact forces_exists_intro_l O hZF.1 h.1.2.2 (forces_regular_l O hZF _ _ hn).1 hp (top_body A' T' t' h p hp hz)
  intro A' T' t' h
  have hT' : T' = T := hUT T' h.1.2.1 (h.2.1 _ (Or.inr (Or.inl rfl))) (fun p hp hz =>
    forces_exists_intro_l O hZF.1 h.1.1
      (forces_regular_l O hZF χ.body _ (named A' T' h.1.1 h.1.2.1)).1 hp (body A' T' t' h p hp hz))
  subst T'
  have hA' : A' = A := hUA A' h.1.1 (h.2.1 _ (Or.inl rfl)) (body A' T t' h)
  subst A'
  exact ⟨rfl, rfl, hUt t' h.1.2.2 (h.2.1 _ (Or.inr (Or.inr rfl))) (top_body A T t' h)⟩

/-- 同一添加量的完整规范名称三元组字面唯一，可用作内部递归的确定算子。 -/
theorem cohen_names_unique_l {κ A T t A' T' t'} (hκ : Name_d M B κ)
    (h : Cohen_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z κ A T t)
    (h' : Cohen_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z κ A' T' t') :
    A = A' ∧ T = T' ∧ t = t' := by
  obtain ⟨Q, D, o, _, hu⟩ := cohen_names_l O hZF hκ
  have he := hu A T t h
  have he' := hu A' T' t' h'
  exact ⟨he.1.trans he'.1.symm, he.2.1.trans he'.2.1.symm, he.2.2.trans he'.2.2.symm⟩

end YesMetaZFC.Model.Forcing.Internal
