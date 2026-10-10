import YesMetaZFC.Model.Forcing.Internal.Maximum.Pool
import YesMetaZFC.Model.Forcing.Internal.Maximum.Basic

/-! # 固定条件上的库内见证选择

一般最大值原理先给出见证，再用 ZF 的同条件等值代表将它送回确定名称库。
一个名称同时实现所有正条件上的有界存在式；首阶段条件不需加强。
选择公理仅用于统一成员选择，名称库的构造和混合闭合仍只需 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 任意原公式的有界存在式，在原条件上由同一库内名称实现。 -/
theorem name_pool_maximum_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {n}
    (φ : UnarySchema n) (ρ : Env M n) (i : Fin n) (hρ : ∀ j, Name_d M B (ρ.bound j))
    {t W} (hW : Name_pool_d M B (ρ.bound i) t W) :
    ∃ s, M.mem s W ∧ ∀ p, M.mem p B → p ≠ z →
      (Forces_d M B R z (.existsE (.conj (.mem .newest (Term.bound i).weaken) φ.body)) ρ p ↔
        Mem_force_d M B R z p s (ρ.bound i) ∧ Forces_d M B R z φ.body (ρ.push s) p) := by
  let hZF := ZFC.models_zf_l hZFC
  let η : Env M n := ⟨ρ.bound, fun _ => ρ.bound i⟩
  have hη : ∀ a : Term n, Name_d M B (a.eval η) := by
    intro a
    cases a with
    | free _ => exact hρ i
    | bound j => exact hρ j
  let χ : UnarySchema n := {
    body := .conj (.mem .newest (Term.bound i).weaken) φ.body
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed]
      exact ⟨⟨rfl, rfl⟩, φ.freeClosed⟩ }
  obtain ⟨v, hv, _, hMax⟩ := maximum_l O hZFC χ η hρ
  obtain ⟨s, hsW, hRep⟩ := name_pool_represent_l O hZF hW hv
  have hs : Name_d M B s := ⟨W, hsW, hW.closed⟩
  have hηs : ∀ a : Term (n+1), Name_d M B (a.eval (η.push s)) := by
    intro a
    cases a with
    | free j => exact hη (.free j)
    | bound j => exact Fin.cases hs (fun j => hη (.bound j)) j
  refine ⟨s, hsW, fun p hp hz => ?_⟩
  have hm : Forces_d M B R z (.existsE χ.body) η p ↔ Forces_d M B R z χ.body (η.push s) p := by
    constructor
    · intro hex
      have hvχ := (hMax p hp hz).mp hex
      have hvA := (forces_mem_l hZF.1 _ _ _ p).mp ((forces_conj_l _ _ _ p).mp hvχ).1
      exact (forces_name_congr_l O hZF χ η hρ hv hs hp hz
        (eq_force_symm_l hZF hs hv (hRep p hvA))).mp hvχ
    · exact forces_exists_intro_l O hZF.1 hs (forces_regular_l O hZF χ.body _ hηs).1 hp
  have hc := (forces_env_l hZF.1 (.existsE χ.body)
    (by simpa only [Definitional.Formula.FreeClosed] using χ.freeClosed) ρ η (fun _ => rfl) p).trans
    (hm.trans (forces_env_l hZF.1 χ.body χ.freeClosed (ρ.push s) (η.push s) (fun _ => rfl) p).symm)
  exact hc.trans ((forces_conj_l _ _ _ p).trans
    (and_congr (forces_mem_l hZF.1 _ _ _ p) Iff.rfl))

end YesMetaZFC.Model.Forcing.Internal
