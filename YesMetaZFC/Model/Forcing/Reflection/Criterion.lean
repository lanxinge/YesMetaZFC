import YesMetaZFC.Model.Forcing.TwoStep.Basic
import YesMetaZFC.Model.Forcing.Extension.Generic
import YesMetaZFC.Model.SetTheory.ProjectReflection

/-! # 任意地模型的力迫公式可数反射

初等子模型同时包含偏序、条件与全部名称参数，故原内部力迫公式逐式反射。
可数性只属于构造出的子模型，不加入原地模型的调用前提。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 同时反射原偏序、正条件、名称赋值和全部原公式的力迫关系。 -/
theorem countable_forcing_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {n p}
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) (hp : M.mem p B) (hz : p ≠ z) :
    ∃ N : SetTheory.Structure.{u}, ∃ B' R' z' p' : N.Domain, ∃ η : Env N n,
      N.Models ZF ∧ (∀ T : SetTheory.Theory, M.Models T → N.Models T) ∧
        N.mem p' B' ∧ p' ≠ z' ∧ Cond_order_d N B' R' z' ∧
        (∀ t : Term n, Name_d N B' (t.eval η)) ∧
        (∀ φ : Formula 1 n, φ.FreeClosed → (Forces_d M B R z φ ρ p ↔ Forces_d N B' R' z' φ η p')) ∧
        ∃ e : Nat → N.Domain, Function.Surjective e := by
  let σ := fenv_l ρ B R z p
  obtain ⟨A, hA, ha, hE, e, he⟩ := FirstOrderSemantics.countable_parameters_l M hZF.1 σ.bound
  let N := FirstOrderSemantics.reduct A.structure_m
  have theory (T : SetTheory.Theory) (hM : M.Models T) : N.Models T :=
    (FirstOrderSemantics.submodel_models_l A hA hZF.1 T).mpr hM
  have hN := theory ZF hZF
  let a (i : Fin (n+4)) : N.Domain := ⟨σ.bound i, ha i⟩
  let B' := a ⟨3, by omega⟩
  let R' := a ⟨2, by omega⟩
  let z' := a ⟨1, by omega⟩
  let p' := a ⟨0, by omega⟩
  have hB : B'.val = B := rfl
  have hR : R'.val = R := rfl
  have hz' : z'.val = z := rfl
  have hp' : p'.val = p := rfl
  have tr {k} (φ : Formula 1 k) (hφ : φ.FreeClosed) (δ : Env N k) :=
    FirstOrderSemantics.submodel_formula_l A hA hZF.1 hE φ hφ δ
  have hn (s : N.Domain) : Name_d N B' s ↔ Name_d M B s.val := by
    let δ := (⟨fun _ => B', fun _ => B'⟩ : Env N 1).push s
    exact (name_sat_l N hN.1 δ (.bound 1) .newest).symm.trans
      ((tr _ (name_m_freeClosed _ _ rfl rfl) δ).trans
        (name_sat_l M hZF.1 (FirstOrderSemantics.submodel_env_l A δ) (.bound 1) .newest))
  let δ := ((⟨fun _ => B', fun _ => B'⟩ : Env N 1).push R').push z'
  have hO : Cond_order_d N B' R' z' :=
    (cond_order_sat_l hN.1 δ (.bound 2) (.bound 1) .newest).mp
      ((tr _ (cond_order_m_freeClosed _ _ _ rfl rfl rfl) δ).mpr
        ((cond_order_sat_l hZF.1 (FirstOrderSemantics.submodel_env_l A δ) _ _ _).mpr O))
  obtain ⟨t, ht⟩ := KP.exists_empty (ZF.modelsKP hN)
  have htN := name_empty_l N (KP.exists_pair (ZF.modelsKP hN)) B' t ht
  let η : Env N n := ⟨fun i => a (param_shift_l i), fun _ => t⟩
  have hη i : (η.bound i).val = ρ.bound i := by
    change (fenv_l ρ B R z p).bound (param_shift_l i) = ρ.bound i
    exact congrArg (fun ξ : Env M n => ξ.bound i) (fenv_param_l M ρ B R z p)
  have hηN : ∀ s : Term n, Name_d N B' (s.eval η) := by
    intro s
    cases s with
    | free _ => exact htN
    | bound i => exact (hn (η.bound i)).mpr ((hη i).symm ▸ hρ i)
  refine ⟨N, B', R', z', p', η, hN, theory, hp, ?_, hO, hηN, ?_, e, he⟩
  · exact fun h => hz (congrArg (fun s : N.Domain => s.val) h)
  · intro φ hφ
    have h := tr (force_code_m φ) (force_code_closed_l φ hφ) (fenv_l η B' R' z' p')
    have hc : Forces_d N B' R' z' φ η p' ↔
        Forces_d M B R z φ (FirstOrderSemantics.submodel_env_l A η) p := by
      simpa only [Forces_d, Code_d, fenv_l, FirstOrderSemantics.submodel_env_push_l, hB, hR, hz', hp'] using! h
    exact (hc.trans (forces_env_l (B := B) (R := R) (z := z) hZF.1 φ hφ
      (FirstOrderSemantics.submodel_env_l A η) ρ (fun i => hη i) p)).symm

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原 ZF 与 ZFC 后果的全局力迫证书

若一个正条件不力迫正文，将条件、偏序与名称参数反射到实际可数初等子模型，
再在加强否定下构造泛型。ZF 与 ZFC 分别调用自己的保持定理，不把选择公理
加入 ZF 端点。构造保持 universe，不限制源模型外部大小或良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z)
include O

private theorem generic_counterexample_l (hZF : M.Models ZF) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) {p} (hp : M.mem p B) (hz : p ≠ z)
    (hn : ¬ Forces_d M B R z φ ρ p) :
    ∃ N : SetTheory.Structure.{u}, ∃ C S w U, ∃ hN : N.Models ZF,
      Cond_order_d N C S w ∧ Generic_d N C S w U ∧
      (∀ T : SetTheory.Theory, M.Models T → N.Models T) ∧
      ∃ η : Env (extension_l N hN C S w U) n, ¬ Formula.satisfies η φ := by
  obtain ⟨N, C, S, w, q, σ, hN, hTheory, hq, hqw, L, hσ, hφN, e, he⟩ := countable_forcing_l O hZF ρ hρ hp hz
  have hnN : ¬ Forces_d N C S w φ σ q := fun h => hn ((hφN φ hφ).mpr h)
  obtain ⟨r, hr, hneg⟩ := regular_neg_witness_l (forces_regular_l L hN φ σ hσ) hq hqw hnN
  obtain ⟨U, hU, hrU⟩ := internal_generic_l L e he hr.1 hr.2.1
  let E := extension_l N hN C S w U
  let η : Env E n := qenv_l hN σ hσ
  have hη : Env_val_d hN σ η := qenv_val_l hN σ hσ
  have hneg' : Forces_d N C S w (.neg φ) σ r := (forces_neg_l hN.1 φ σ r).mpr hneg
  refine ⟨N, C, S, w, U, hN, L, hU, hTheory, η, ?_⟩
  exact (Formula.satisfies_neg_iff η φ).mp
    ((forcing_truth_l L hN hU (.neg φ) (by simpa only [Definitional.Formula.FreeClosed] using hφ)
      σ η hη).mp ⟨r, hrU, hneg'⟩)

/-- 失败的力迫产生实际 ZF 反模型，只要求源模型满足原 ZF。 -/
theorem forcing_zf_countermodel_l (hZF : M.Models ZF) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) {p} (hp : M.mem p B) (hz : p ≠ z)
    (hn : ¬ Forces_d M B R z φ ρ p) :
    ∃ N : SetTheory.Structure.{u}, N.Models ZF ∧ ∃ η : Env N n, ¬ Formula.satisfies η φ := by
  obtain ⟨N, C, S, w, U, hN, L, hU, _, η, hη⟩ := generic_counterexample_l O hZF φ hφ ρ hρ hp hz hn
  exact ⟨extension_l N hN C S w U, preserves_zf_l L hN hU, η, hη⟩

theorem forces_zf_valid_l (hZF : M.Models ZF) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (h : ∀ N : SetTheory.Structure.{u}, N.Models ZF → ∀ η : Env N n, Formula.satisfies η φ)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) {p} (hp : M.mem p B) (hz : p ≠ z) :
    Forces_d M B R z φ ρ p := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨N, hN, η, hη⟩ := forcing_zf_countermodel_l O hZF φ hφ ρ hρ hp hz hn
  exact hη (h N hN η)

/-- 全部原 ZF 公理和模式在每个正条件上被迫使，不消费原选择公理。 -/
theorem forces_zf_l (hZF : M.Models ZF) (s : Sentence) (hs : ZF s) (ρ : Env M 0)
    {p} (hp : M.mem p B) (hz : p ≠ z) : Forces_d M B R z s.formula ρ p := by
  apply forces_zf_valid_l O hZF s.formula s.freeClosed ?_ ρ (fun i => Fin.elim0 i) hp hz
  intro N hN η
  have he : η = ⟨Fin.elim0, η.free⟩ := by
    rw [Env.mk.injEq]
    exact ⟨funext (fun i => Fin.elim0 i), rfl⟩
  rw [he]
  exact hN.2 s hs η.free

variable (hZFC : M.Models ZFC)
include hZFC

/-- 原 ZFC 的反模型额外消费已反射的选择公理及其实际保持定理。 -/
theorem forcing_countermodel_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) {p} (hp : M.mem p B) (hz : p ≠ z)
    (hn : ¬ Forces_d M B R z φ ρ p) :
    ∃ N : SetTheory.Structure.{u}, N.Models ZFC ∧ ∃ η : Env N n, ¬ Formula.satisfies η φ := by
  obtain ⟨N, C, S, w, U, hN, L, hU, hTheory, η, hη⟩ :=
    generic_counterexample_l O (ZFC.models_zf_l hZFC) φ hφ ρ hρ hp hz hn
  exact ⟨extension_l N hN C S w U, preserves_zfc_l L (hTheory ZFC hZFC) hU, η, hη⟩

/-- 原 ZFC 的任何实际语义后果在任意地模型的每个正条件上被力迫。 -/
theorem forces_valid_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (h : ∀ N : SetTheory.Structure.{u}, N.Models ZFC → ∀ η : Env N n, Formula.satisfies η φ)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) {p} (hp : M.mem p B) (hz : p ≠ z) :
    Forces_d M B R z φ ρ p := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨N, hN, η, hη⟩ := forcing_countermodel_l O hZFC φ hφ ρ hρ hp hz hn
  exact hη (h N hN η)

/-- 原 ZFC 的全部公理与模式具有统一的全局力迫证书。 -/
theorem forces_zfc_l (s : Sentence) (hs : ZFC s) (ρ : Env M 0) {p} (hp : M.mem p B) (hz : p ≠ z) :
    Forces_d M B R z s.formula ρ p := by
  apply forces_valid_l O hZFC s.formula s.freeClosed ?_ ρ (fun i => Fin.elim0 i) hp hz
  intro N hN η
  have he : η = ⟨Fin.elim0, η.free⟩ := by
    rw [Env.mk.injEq]
    exact ⟨funext (fun i => Fin.elim0 i), rfl⟩
  rw [he]
  exact hN.2 s hs η.free

end YesMetaZFC.Model.Forcing.Internal

/-! ## 带原模型定义条件的全局力迫判据

把原模型条件、名称参数和失败的力迫同时反射到实际可数模型。在该模型中
构造通过反例条件的泛型；因而可直接消费已证明的、对所有泛型成立的名称构造。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

/-- 在实际可数地模型中，遍历通过原条件的泛型即可判定力迫；只使用原 ZF。 -/
theorem forces_countable_l {M : SetTheory.Structure.{u}} {B R z : M.Domain}
    (O : Cond_order_d M B R z) (hZF : M.Models ZF) (e : Nat → M.Domain) (he : Function.Surjective e)
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (ρ : Env M n)
    (hρ : ∀ i, Name_d M B (ρ.bound i)) {p} (hp : M.mem p B) (hz : p ≠ z)
    (valid : ∀ U, Generic_d M B R z U → U p →
      ∀ η : Env (extension_l M hZF B R z U) n,
        (∀ i, Qval_d M B R z U (ρ.bound i) (η.bound i)) → Formula.satisfies η φ) :
    Forces_d M B R z φ ρ p := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨a, ha⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have haN := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B a ha
  let σ : Env M n := ⟨ρ.bound, fun _ => a⟩
  have hσ : ∀ t : Term n, Name_d M B (t.eval σ) := by
    intro t
    cases t with
    | free _ => exact haN
    | bound i => exact hρ i
  have hnσ : ¬ Forces_d M B R z φ σ p :=
    fun h => hn ((forces_env_l hZF.1 φ hφ ρ σ (fun _ => rfl) p).mpr h)
  obtain ⟨r, hr, hneg⟩ := regular_neg_witness_l (forces_regular_l O hZF φ σ hσ) hp hz hnσ
  obtain ⟨U, hU, hrU⟩ := internal_generic_l O e he hr.1 hr.2.1
  let η := qenv_l (R := R) (z := z) (U := U) hZF σ hσ
  have hv := qenv_val_l (R := R) (z := z) (U := U) hZF σ hσ
  have hnot := (Formula.satisfies_neg_iff η φ).mp
    ((forcing_truth_l O hZF hU (.neg φ) (by simpa only [Definitional.Formula.FreeClosed] using hφ)
      σ η hv).mp ⟨r, hrU, (forces_neg_l hZF.1 φ σ r).mpr hneg⟩)
  exact hnot (valid U hU (hU.upward r p hrU hp hr.2.2) η (fun i => hv (.bound i)))

/-- 同时反射原模型的指定理论及有限参数，泛型论证因而保留实际使用的公理强度。 -/
theorem source_of_generics_theory_l {Γ : SetTheory.Theory} {n} (α β : Formula 1 n) (hα : α.FreeClosed) (hβ : β.FreeClosed)
    (B R z p : Term n) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (hp : p.freeSupport = [])
    (valid : ∀ N : SetTheory.Structure.{u}, N.Models ZF → N.Models Γ → ∀ η : Env N n,
      Cond_order_d N (B.eval η) (R.eval η) (z.eval η) → Formula.satisfies η α →
      ∀ U, Generic_d N (B.eval η) (R.eval η) (z.eval η) U → U (p.eval η) → Formula.satisfies η β)
    {M : SetTheory.Structure.{u}} (hZF : M.Models ZF) (hΓ : M.Models Γ) (ρ : Env M n)
    (O : Cond_order_d M (B.eval ρ) (R.eval ρ) (z.eval ρ))
    (hpos : M.mem (p.eval ρ) (B.eval ρ)) (hne : p.eval ρ ≠ z.eval ρ) (hraw : Formula.satisfies ρ α) :
    Formula.satisfies ρ β := by
  obtain ⟨N, hE, hTheory, η, tr, e, he⟩ := FirstOrderSemantics.countable_env_l M hZF.1 ρ
  have hN := (hTheory ZF).mpr hZF
  have L : Cond_order_d N (B.eval η) (R.eval η) (z.eval η) :=
    (cond_order_sat_l hE η B R z).mp ((tr _ (cond_order_m_freeClosed _ _ _ hB hR hz)).mp
      ((cond_order_sat_l hZF.1 ρ B R z).mpr O))
  have hpos' : N.mem (p.eval η) (B.eval η) :=
    (Formula.satisfies_mem_iff η p B).mp ((tr (.mem p B)
      (by simp only [Definitional.Formula.FreeClosed]; exact ⟨hp, hB⟩)).mp
        ((Formula.satisfies_mem_iff ρ p B).mpr hpos))
  have heq : p.eval ρ = z.eval ρ ↔ p.eval η = z.eval η := by
    have hh := tr (Formula.extensionalEq p z) ((Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨hp, hz⟩)
    simpa only [Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_extensionalEq_iff_eq hE] using hh
  obtain ⟨U, hU, hpU⟩ := internal_generic_l L e he hpos' (fun hh => hne (heq.mpr hh))
  exact (tr β hβ).mpr (valid N hN ((hTheory Γ).mpr hΓ) η L ((tr α hα).mp hraw) U hU hpU)

/-- 若每个被接受的正条件泛型都给出原模型中的见证，有限参数反射消去泛型存在前提。 -/
theorem source_of_generics_l {n} (α β : Formula 1 n) (hα : α.FreeClosed) (hβ : β.FreeClosed)
    (B R z p : Term n) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (hp : p.freeSupport = [])
    (valid : ∀ N : SetTheory.Structure.{u}, N.Models ZF → ∀ η : Env N n,
      Cond_order_d N (B.eval η) (R.eval η) (z.eval η) → Formula.satisfies η α →
      ∀ U, Generic_d N (B.eval η) (R.eval η) (z.eval η) U → U (p.eval η) → Formula.satisfies η β)
    {M : SetTheory.Structure.{u}} (hZF : M.Models ZF) (ρ : Env M n)
    (O : Cond_order_d M (B.eval ρ) (R.eval ρ) (z.eval ρ))
    (hpos : M.mem (p.eval ρ) (B.eval ρ)) (hne : p.eval ρ ≠ z.eval ρ) (hraw : Formula.satisfies ρ α) :
    Formula.satisfies ρ β :=
  source_of_generics_theory_l (Γ := ZF) α β hα hβ B R z p hB hR hz hp
    (fun N hN _ => valid N hN) hZF hZF ρ O hpos hne hraw

/-- 原模型条件由实际公式 α 给出，名称参数由闭项代入指定；不要求原模型可数。 -/
theorem forces_of_generics_l {n k} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (α : Formula 1 k) (hα : α.FreeClosed) (e : Fin n → Term k) (B R z p : Term k)
    (he : ∀ i, (e i).freeSupport = []) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (hp : p.freeSupport = [])
    (valid : ∀ N : SetTheory.Structure.{u}, ∀ hN : N.Models ZF, ∀ η : Env N k,
      Cond_order_d N (B.eval η) (R.eval η) (z.eval η) →
      (∀ i, Name_d N (B.eval η) ((e i).eval η)) → N.mem (p.eval η) (B.eval η) → p.eval η ≠ z.eval η →
      Formula.satisfies η α → ∀ U, Generic_d N (B.eval η) (R.eval η) (z.eval η) U → U (p.eval η) →
      ∀ ξ : Env (extension_l N hN (B.eval η) (R.eval η) (z.eval η) U) n,
        (∀ i, Qval_d N (B.eval η) (R.eval η) (z.eval η) U ((e i).eval η) (ξ.bound i)) → Formula.satisfies ξ φ)
    {M : SetTheory.Structure.{u}} (hZF : M.Models ZF) (ρ : Env M k)
    (O : Cond_order_d M (B.eval ρ) (R.eval ρ) (z.eval ρ))
    (hn : ∀ i, Name_d M (B.eval ρ) ((e i).eval ρ))
    (hpos : M.mem (p.eval ρ) (B.eval ρ)) (hne : p.eval ρ ≠ z.eval ρ) (hraw : Formula.satisfies ρ α) :
    Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (p.eval ρ) := by
  apply Classical.byContradiction
  intro hfail
  obtain ⟨N, hE, hTheory, η, tr, f, hf⟩ := FirstOrderSemantics.countable_env_l M hZF.1 ρ
  have hN := (hTheory ZF).mpr hZF
  have L : Cond_order_d N (B.eval η) (R.eval η) (z.eval η) :=
    (cond_order_sat_l hE η B R z).mp ((tr _ (cond_order_m_freeClosed _ _ _ hB hR hz)).mp
      ((cond_order_sat_l hZF.1 ρ B R z).mpr O))
  have names i : Name_d N (B.eval η) ((e i).eval η) :=
    (name_sat_l N hE η B (e i)).mp ((tr _ (name_m_freeClosed _ _ hB (he i))).mp
      ((name_sat_l M hZF.1 ρ B (e i)).mpr (hn i)))
  have hpos' : N.mem (p.eval η) (B.eval η) :=
    (Formula.satisfies_mem_iff η p B).mp ((tr (.mem p B)
      (by simp only [Definitional.Formula.FreeClosed]; exact ⟨hp, hB⟩)).mp
        ((Formula.satisfies_mem_iff ρ p B).mpr hpos))
  have heq : p.eval ρ = z.eval ρ ↔ p.eval η = z.eval η := by
    have h := tr (Formula.extensionalEq p z) ((Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨hp, hz⟩)
    simpa only [Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_extensionalEq_iff_eq hE] using h
  have hne' : p.eval η ≠ z.eval η := fun hh => hne (heq.mpr hh)
  let σ : Env N n := ⟨fun i => (e i).eval η, η.free⟩
  have hnσ : ¬ Forces_d N (B.eval η) (R.eval η) (z.eval η) φ σ (p.eval η) := by
    intro hh
    exact hfail ((force_at_sat_l φ ρ e B R z p).mp
      ((tr (force_at_m φ e B R z p) (force_at_closed_l _ _ _ _ _ _ hφ he hB hR hz hp)).mpr
        ((force_at_sat_l φ η e B R z p).mpr hh)))
  obtain ⟨a, ha⟩ := KP.exists_empty (ZF.modelsKP hN)
  have haN := name_empty_l N (KP.exists_pair (ZF.modelsKP hN)) (B.eval η) a ha
  let δ : Env N n := ⟨σ.bound, fun _ => a⟩
  have hδ : ∀ t : Term n, Name_d N (B.eval η) (t.eval δ) := by
    intro t
    cases t with
    | free _ => exact haN
    | bound i => exact names i
  have hnδ : ¬ Forces_d N (B.eval η) (R.eval η) (z.eval η) φ δ (p.eval η) :=
    fun hh => hnσ ((forces_env_l hE φ hφ σ δ (fun _ => rfl) _).mpr hh)
  obtain ⟨r, hr, hneg⟩ := regular_neg_witness_l (forces_regular_l L hN φ δ hδ) hpos' hne' hnδ
  obtain ⟨U, hU, hrU⟩ := internal_generic_l L f hf hr.1 hr.2.1
  have hpU := hU.upward r (p.eval η) hrU hpos' hr.2.2
  let E := extension_l N hN (B.eval η) (R.eval η) (z.eval η) U
  let ξ : Env E n := qenv_l hN δ hδ
  have hv : Env_val_d hN δ ξ := qenv_val_l hN δ hδ
  have hnot : ¬ Formula.satisfies ξ φ := (Formula.satisfies_neg_iff ξ φ).mp
    ((forcing_truth_l L hN hU (.neg φ) (by simpa only [Definitional.Formula.FreeClosed] using hφ) δ ξ hv).mp
      ⟨r, hrU, (forces_neg_l hE φ δ r).mpr hneg⟩)
  exact hnot (valid N hN η L names hpos' hne' ((tr α hα).mp hraw) U hU hpU ξ (fun i => hv (.bound i)))

end YesMetaZFC.Model.Forcing.Internal
