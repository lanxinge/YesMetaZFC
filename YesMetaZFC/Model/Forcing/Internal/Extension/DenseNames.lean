import YesMetaZFC.Model.Forcing.Internal.Maximum.Patch
import YesMetaZFC.Model.Forcing.Internal.Reflection.Countermodel
import YesMetaZFC.Model.Forcing.Proper.Master.Syntax
import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! # 7.23 所需的地模型稠密集名称库

先在地模型中取条件集名称的混合闭库，再分离全局被迫为稠密集的名称。
任意泛型扩张中的稠密集先正规化到该库，再用条件集本身作后备见证修补。
因此同一个地模型集合覆盖所有扩张中的稠密集；不枚举整个地模型，也不使用
宿主幂集代替模型幂集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {B R z A T : M.Domain}

def dn_s : UnarySchema 2 := {
  body := dense_set_m (.bound 1) (.bound 2) (.bound 1) .newest }

/-- 条件域本身是稠密集；排除值取域本身，由基础公理保证它不是条件。 -/
theorem dense_full_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hA : Name_d M B A) (hT : Name_d M B T) {p} (hp : M.mem p B) (hz : p ≠ z)
    (pre : Forces_d M B R z (preord_m .newest (.bound 1)) (ord_env_l M A T) p) :
    Forces_d M B R z dn_s.body ((ord_env_l M A T).push A) p := by
  let φ : Formula 1 2 := preord_m .newest (.bound 1)
  let e : Fin 2 → Term 3 := Fin.cases (.bound 1) (fun _ => .bound 2)
  let ψ := φ.bind e
  let ρ := (ord_env_l M A T).push A
  have hc : ψ.FreeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases rfl (fun _ => rfl)) _).mpr (preord_m_freeClosed _ _ rfl rfl)
  have names : ∀ a : Term 3, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact hT
    | bound i => exact Fin.cases hA (Fin.cases hA (fun _ => hT)) i
  have forced : Forces_d M B R z ψ ρ p := (forces_bind_l hZF.1 φ e ρ p).mpr
    ((forces_env_l hZF.1 φ (preord_m_freeClosed _ _ rfl rfl) (ord_env_l M A T)
      (Definitional.Env.substitute ρ e) (Fin.cases rfl (fun _ => rfl)) p).mp pre)
  let α : Formula 1 3 := .conj ψ (Formula.extensionalEq .newest (.bound 1))
  have hcα : α.FreeClosed := ⟨hc, by simp -implicitDefEqProofs⟩
  have hα : Forces_d M B R z α ρ p := (forces_conj_l _ _ _ _).mpr
    ⟨forced, (code_eq_l M hZF.1 B R z .newest (.bound 1) ρ p).mpr (eq_force_refl_l O hZF hp hA)⟩
  have rule := forces_zf_valid_l O hZF (.imp α dn_s.body) ⟨hcα, dn_s.freeClosed⟩
    (fun N hN η => by
      simp only [Formula.satisfies_imp_iff, α, Formula.satisfies_conj_iff, ψ, Formula.satisfies_bind,
        φ, preord_sat_l hN.1, Formula.satisfies_extensionalEq_iff_eq hN.1, dn_s, dense_set_sat_l N hN.1]
      intro ⟨h, eq⟩
      rw [eq]
      exact ⟨fun q hq => ⟨hq, fun eq => KP.mem_irrefl_d (ZF.modelsKP hN) _ (eq ▸ hq)⟩,
        fun q hq hz => ⟨q, ⟨hq, hz, h.1 q hq⟩, hq⟩⟩)
    ρ (fun i => names (.bound i)) hp hz
  exact forces_mp_l hZF.1 (forces_regular_l O hZF α ρ names).1
    (forces_regular_l O hZF dn_s.body ρ names) hp hz rule hα

/-- 一次在地模型中装配名称库，并证明它覆盖任意实际泛型扩张中的全部稠密集。 -/
theorem dense_names_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hA : Name_d M B A) (hT : Name_d M B T)
    (pre : ∀ p, M.mem p B → p ≠ z →
      Forces_d M B R z (preord_m .newest (.bound 1)) (ord_env_l M A T) p) :
    ∃ W D, Name_pool_d M B A A W ∧
      (∀ s, M.mem s D ↔ M.mem s W ∧ ∀ p, M.mem p B → p ≠ z →
        Forces_d M B R z dn_s.body ((ord_env_l M A T).push s) p) ∧
      ∀ U, Generic_d M B R z U → ∀ C S K : (extension_l M hZF B R z U).Domain,
        Qval_d M B R z U A C → Qval_d M B R z U T S →
        Dense_set_d (extension_l M hZF B R z U) C S C K →
        ∃ s, M.mem s D ∧ Qval_d M B R z U s K := by
  let ρ := ord_env_l M A T
  have fallback p hp hz := dense_full_force_l O hZF hA hT hp hz (pre p hp hz)
  obtain ⟨W, pool⟩ := name_pool_exists_l M hZF hA hA
  let δ := ((ρ.push B).push R).push z
  let e : Fin 3 → Term 6 := Fin.cases .newest (Fin.cases (.bound 4) (fun _ => .bound 5))
  let χ : UnarySchema 5 := {
    body := force_all_m dn_s.body e (.bound 3) (.bound 2) (.bound 1)
    freeClosed := force_all_closed_l _ _ _ _ _ dn_s.freeClosed
      (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl rfl rfl }
  have spec s : χ.denote δ s ↔ ∀ p, M.mem p B → p ≠ z →
      Forces_d M B R z dn_s.body (ρ.push s) p := by
    rw [UnarySchema.denote, force_all_sat_l hZF.1]
    apply forall_congr'; intro p
    apply imp_congr_right; intro _
    apply imp_congr_right; intro _
    exact forces_env_l hZF.1 dn_s.body dn_s.freeClosed _ _
      (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) p
  obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF χ δ W
  have hd' s := (hd s).trans (and_congr_right fun _ => spec s)
  refine ⟨W, D, pool, hd', ?_⟩
  intro U generic C S K valueA valueT dense
  obtain ⟨s, _, value⟩ := value_name_l K
  obtain ⟨q, hq, valueq⟩ : ∃ q, M.mem q W ∧ Qval_d M B R z U q K := by
    obtain ⟨H, hull, bound⟩ := pool
    obtain ⟨q, _, hq, _, vq⟩ := normalize_name_l O hZF generic hull.closed hull.left value valueA
      (fun x hx => (dense.1 x hx).1)
    exact ⟨q, (bound q).mpr (fun p hp => by
      obtain ⟨a, b, ha, hb, pair⟩ := hq p hp
      exact ⟨a, b, pair, ha, hb⟩), vq⟩
  let E := extension_l M hZF B R z U
  let η : Env E 3 := (ord_env_l E C S).push K
  have values : Env_val_d hZF (ρ.push q) η := by
    intro a
    cases a with
    | free _ => exact valueT
    | bound i => exact Fin.cases valueq (Fin.cases valueA (fun _ => valueT)) i
  have truth : Formula.satisfies η dn_s.body :=
    (dense_set_sat_l E (extension_ext_l O hZF generic) η _ _ _ _).mpr dense
  obtain ⟨p, hp, forced⟩ := (forcing_truth_l O hZF generic dn_s.body dn_s.freeClosed (ρ.push q) η values).mpr truth
  obtain ⟨a, ha, all, eq⟩ := name_pool_patch_l O hZF dn_s ρ (Fin.cases hA (fun _ => hT))
    pool hq pool.left fallback
  obtain ⟨V, hv⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B a from ⟨W, ha, pool.closed⟩)
  have same : V = K := (qval_eq_l O hZF generic hv valueq).mp ⟨p, hp, eq p (generic.proper p hp).1 forced⟩
  exact ⟨a, (hd' a).mpr ⟨ha, all⟩, same ▸ hv⟩

end YesMetaZFC.Model.Forcing.Internal
