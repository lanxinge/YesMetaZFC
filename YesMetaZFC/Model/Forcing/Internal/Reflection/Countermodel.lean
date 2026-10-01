import YesMetaZFC.Model.Forcing.Internal.Reflection.Countable

/-! # 原 ZF 与 ZFC 后果的全局力迫证书

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
