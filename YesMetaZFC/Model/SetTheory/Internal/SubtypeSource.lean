import YesMetaZFC.Model.SetTheory.Internal.SubtypeColumn
import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure

/-! # 固定子类型查询从传递证书层向上读取

名字域、原列和七个槽位见证均由原存在式给出；其余矩阵全部有界。
因此只用传递性即可读出原查询，既不改变查询码，也不要求证书层满足 KP。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
include hKP hX

theorem ts_query_source_l {d} (ρ : Env N d) (ω n κ τ m U w b z q : Term d) (σ : Fin 7 → Term d)
    (h : Formula.satisfies ρ (ts_query_m ω n κ τ m U w b z q σ)) :
    Ts_query_d (ω.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val (m.eval ρ).val
      (U.eval ρ).val (w.eval ρ).val (b.eval ρ).val (fun i => (σ i).eval ρ |>.val) (z.eval ρ).val (q.eval ρ).val := by
  simp only [ts_query_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff] at h
  obtain ⟨constants, A, C, v₀, v₁, v₂, v₃, v₄, v₅, v₆, names, fn, old, slots, values, pair⟩ := h
  have Δ {k} (η : Env N k) (φ : Formula 1 k) (hd : φ.IsDelta0) (h : Formula.satisfies η φ) :=
    (rt_model_delta_l hX nx hd η).mp h
  have names := Δ _ _ (tn_names0_delta_l ..) names
  have fn := Δ _ _ (fn0_delta_l ..) fn
  have values := Δ _ _ (ts_names_delta_l ..) values
  have pair := Δ _ _ (kpair0_delta_l ..) pair
  simp only [tn_names0_sat_l hKP, fn0_sat_l hKP.1, ts_names_sat_l hKP.1, kpair0_sat_l hKP.1,
    @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at names fn values pair
  have entry {k} (η : Env N k) (a c F : Term k) (h : Formula.satisfies η (rd_entry0_m a c F)) :
      Rd_entry_d (a.eval η).val (c.eval η).val (F.eval η).val := by
    simpa only [rd_entry0_sat_l hKP.1, @eval_image_env_l N M Subtype.val] using Δ η _ (rd_entry0_delta_l ..) h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := slots
  have h₀ := entry _ _ _ _ h₀
  have h₁ := entry _ _ _ _ h₁
  have h₂ := entry _ _ _ _ h₂
  have h₃ := entry _ _ _ _ h₃
  have h₄ := entry _ _ _ _ h₄
  have h₅ := entry _ _ _ _ h₅
  have h₆ := entry _ _ _ _ h₆
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at h₀ h₁ h₂ h₃ h₄ h₅ h₆
  simp only [Definitional.Term.eval_weaken] at old
  refine ⟨constants, A.val, C.val, _, names, fn, ?_,
    Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄
      (Fin.cases h₅ (Fin.cases h₆ (fun i => Fin.elim0 i))))))), values, pair⟩
  intro i hi
  have own := entry _ _ _ _ (old ⟨i, hX (n.eval ρ).val (n.eval ρ).property i hi⟩ hi)
  change Rd_entry_d i i C.val at own
  exact own

theorem ts_subtype_source_l {d} (ρ : Env N d) (ω n κ τ m U w b z u : Term d) (σ : Fin 7 → Term d)
    (h : Formula.satisfies ρ (ts_subtype_m ω n κ τ m U w b z u σ)) :
    Ts_subtype_d (ω.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val (m.eval ρ).val
      (U.eval ρ).val (w.eval ρ).val (b.eval ρ).val (fun i => (σ i).eval ρ |>.val) (z.eval ρ).val (u.eval ρ).val := by
  simp only [ts_subtype_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff] at h
  obtain ⟨ht, sub, q, query, mem⟩ := h
  have subset := (rt_model_delta_l hX nx (φ := Formula.subset n m) (.atom ..) ρ).mp sub
  have sub : M.MemberSubset (n.eval ρ).val (m.eval ρ).val := by
    simpa only [Structure.MemberSubset, @eval_image_env_l N M Subtype.val] using (Formula.satisfies_subset_iff _ n m).mp subset
  have code := ts_query_source_l hKP hX nx _ _ _ _ _ _ _ _ _ _ _ _ query
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at code
  simp only [Definitional.Term.eval_weaken (ℳ := N), Definitional.Term.eval_newest (ℳ := N)] at mem
  exact ⟨ht, sub, q.val, code, mem⟩

end YesMetaZFC.SetTheory.Internal
