import YesMetaZFC.Model.Forcing.Internal.Maximum.Member
import YesMetaZFC.Model.Forcing.Internal.Maximum.WitnessPool
import YesMetaZFC.Model.Forcing.Internal.Maximum.Normal

/-! # 原公式的内部最大值原理

先由原收集模式把可能见证收紧到一个内部集合，再构造见证名称集并选择其统一
成员名称。一个名称同时实现全部正条件上的存在力迫，不假设外部泛型或良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 加权名称的每个条目满足正文时，被迫属于它的名称也满足正文。 -/
private theorem predicate_name_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {n}
    (φ : Formula 1 (n+1)) (ρ : Env M n) (hρ : ∀ v : Term n, Name_d M B (v.eval ρ)) {A}
    (hA : ∀ s b, Entry_d M s b A → Name_d M B s ∧ M.mem b B ∧ Forces_d M B R z φ (ρ.push s) b)
    {p t} (hp : M.mem p B) (hz : p ≠ z) (ht : Name_d M B t) (hm : Mem_force_d M B R z p t A) :
    Forces_d M B R z φ (ρ.push t) p := by
  have push {s} (hs : Name_d M B s) : ∀ v : Term (n+1), Name_d M B (v.eval (ρ.push s)) := by
    intro v
    cases v with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  apply (forces_regular_l O hZF φ _ (push ht)).2 p hp hz
  intro q hq
  obtain ⟨r, s, b, hr, hsb, hrb, he⟩ := hm.2 q hq
  obtain ⟨hs, hb, hφ⟩ := hA s b hsb
  have hφr := (forces_regular_l O hZF φ _ (push hs)).1 b r hb ⟨hr.1, hr.2.1, hrb⟩ hφ
  have hc := forces_congr_below_l O hZF φ (ρ.push t) (ρ.push s) (push ht) (push hs) hr.1 (fun v => by
    cases v with
    | free i => exact eq_force_refl_l O hZF hr.1 (hρ (.free i))
    | bound i => exact Fin.cases he (fun i => eq_force_refl_l O hZF hr.1 (hρ (.bound i))) i)
  exact ⟨r, hr, (hc r (below_refl_l O hr.1 hr.2.1)).mpr hφr⟩

/-- 一次生成原公式的最大值见证名称；仅要求实际有限参数均为名称。 -/
private theorem maximum_raw_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {n}
    (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) :
    ∃ t, Name_d M B t ∧ ∀ p, M.mem p B → p ≠ z →
      (Forces_d M B R z (.existsE φ.body) ρ p ↔ Forces_d M B R z φ.body (ρ.push t) p) := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hen := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  let η : Env M n := ⟨ρ.bound, fun _ => e⟩
  have hη : ∀ t : Term n, Name_d M B (t.eval η) := by
    intro t
    cases t with
    | free _ => exact hen
    | bound i => exact hρ i
  obtain ⟨A, hA, hSound, hPool⟩ := witness_pool_l hZF φ η
  obtain ⟨t, ht, hmax⟩ := member_maximum_l O hZFC hA
  have hηt : ∀ v : Term (n+1), Name_d M B (v.eval (η.push t)) := by
    intro v
    cases v with
    | free i => exact hη (.free i)
    | bound i => exact Fin.cases ht (fun i => hη (.bound i)) i
  have hr := forces_regular_l O hZF φ.body (η.push t) hηt
  refine ⟨t, ht, fun p hp hz => ?_⟩
  have hm : Forces_d M B R z (.existsE φ.body) η p ↔ Forces_d M B R z φ.body (η.push t) p := by
    constructor
    · intro hex
      apply hr.2 p hp hz
      intro q hq
      obtain ⟨r, hqr, v, hv, hφ⟩ := forces_exists_dense_l hZF.1 hex q hq
      obtain ⟨s, hsa⟩ := hPool r hqr.1 v hv hφ
      have hsN := (name_entry_l M hA hsa).1
      have hmem := hmax r s (mem_force_entry_l O hZF hqr.1 hsN hqr.1 hsa (O.refl r hqr.1))
      refine ⟨r, hqr, predicate_name_l O hZF φ.body η hη ?_ hqr.1 hqr.2.1 ht hmem⟩
      intro a b hab
      exact ⟨(name_entry_l M hA hab).1, (name_entry_l M hA hab).2, hSound a b hab⟩
    · exact forces_exists_intro_l O hZF.1 ht hr.1 hp
  exact (forces_env_l hZF.1 (.existsE φ.body)
    (by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed) ρ η (fun _ => rfl) p).trans
    (hm.trans (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push t) (η.push t) (fun _ => rfl) p).symm)

/-- 最大值名称直接返回规范固定点，供后继名称与递归装配统一使用。 -/
theorem maximum_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {n}
    (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) :
    ∃ t, Name_d M B t ∧
      Norm_name_d M (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R z t t ∧
      ∀ p, M.mem p B → p ≠ z →
        (Forces_d M B R z (.existsE φ.body) ρ p ↔ Forces_d M B R z φ.body (ρ.push t) p) := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨t, ht, hMax⟩ := maximum_raw_l O hZFC φ ρ hρ
  obtain ⟨q, _, hNorm, hq, he⟩ := norm_name_exists_l O hZF ht
  exact ⟨q, hq, hNorm, fun p hp hz => (hMax p hp hz).trans
    (forces_name_congr_l O hZF φ ρ hρ ht hq hp hz (eq_force_symm_l hZF hq ht (he p hp hz)))⟩

end YesMetaZFC.Model.Forcing.Internal
