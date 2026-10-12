import YesMetaZFC.Model.SetTheory.Internal.TypeProgramSyntax
import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure

/-! # 原查询名字列的向上读取

只解包原存在见证，再传输有界矩阵；源不需要满足 KP。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
include hKP hX

theorem tt_code0_source_l {d} (ρ : Env N d) (n U z p : Term d)
    (valid : Formula.satisfies ρ (tt_code0_m n U z p)) :
    Tt_code_d (n.eval ρ).val (U.eval ρ).val (z.eval ρ).val (p.eval ρ).val (Fin.elim0 : Fin 0 → M.Domain) := by
  simp only [tt_code0_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨A, C, b, matrix⟩ := valid
  have up := (rt_model_delta_l hX nx
    (.conj (tn_names0_delta_l ..) (.conj (num0_delta_l 0 _) (.conj (fn0_delta_l ..) (kpair0_delta_l ..)))) _).mp matrix
  have full : Formula.satisfies (image_env_l Subtype.val ρ) (tt_code0_m n U z p) := by
    simp only [tt_code0_m, Formula.satisfies_exists_iff]
    exact ⟨A.val, C.val, b.val, by simpa only [@image_env_push_l N M Subtype.val] using up⟩
  simpa only [@eval_image_env_l N M Subtype.val] using (tt_code0_sat_l hKP _ _ _ _ _).mp full

theorem tt_code2_source_l {d} (ρ : Env N d) (n U z p a b : Term d)
    (valid : Formula.satisfies ρ (tt_code2_m n U z p a b)) :
    Tt_code_d (n.eval ρ).val (U.eval ρ).val (z.eval ρ).val (p.eval ρ).val
      (Fin.cases (a.eval ρ).val (fun _ => (b.eval ρ).val) : Fin 2 → M.Domain) := by
  simp only [tt_code2_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨A, C, l, matrix⟩ := valid
  have up := (rt_model_delta_l hX nx (.conj (tn_names0_delta_l ..) (.conj (num0_delta_l 2 _)
    (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj
      (.forallMem _ (.imp (num0_delta_l 0 _) (rd_entry0_delta_l ..)))
      (.forallMem _ (.imp (num0_delta_l 1 _) (rd_entry0_delta_l ..)))))))) _).mp matrix
  have full : Formula.satisfies (image_env_l Subtype.val ρ) (tt_code2_m n U z p a b) := by
    simp only [tt_code2_m, Formula.satisfies_exists_iff]
    exact ⟨A.val, C.val, l.val, by simpa only [@image_env_push_l N M Subtype.val] using up⟩
  simpa only [@eval_image_env_l N M Subtype.val] using (tt_code2_sat_l hKP _ _ _ _ _ _ _).mp full

theorem tg_guard_code_source_l {d} (ρ : Env N d) (n κ U l z p : Term d)
    (valid : Formula.satisfies ρ (tg_guard_code_m n κ U l z p)) :
    Tg_guard_code_d (n.eval ρ).val (κ.eval ρ).val (U.eval ρ).val (l.eval ρ).val (z.eval ρ).val (p.eval ρ).val := by
  simp only [tg_guard_code_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨b, k, C, A, matrix⟩ := valid
  have up := (rt_model_delta_l hX nx (.conj (KP.succ0_delta_l ..) (.conj (KP.succ0_delta_l ..)
    (.conj (tn_names0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..)
      (.conj (kpair0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..)) (rd_entry0_delta_l ..)))))))) _).mp matrix
  have full : Formula.satisfies (image_env_l Subtype.val ρ) (tg_guard_code_m n κ U l z p) := by
    simp only [tg_guard_code_m, Formula.satisfies_exists_iff]
    exact ⟨b.val, k.val, C.val, A.val, by simpa only [@image_env_push_l N M Subtype.val] using up⟩
  simpa only [@eval_image_env_l N M Subtype.val] using (tg_guard_code_sat_l hKP _ _ _ _ _ _ _).mp full

end YesMetaZFC.SetTheory.Internal
