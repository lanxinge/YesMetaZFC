import YesMetaZFC.Model.SetTheory.Internal.TypeProgramSource
import YesMetaZFC.Model.SetTheory.Internal.TypeNamesSource

/-! # 同一查询名字列回到传递源

列图和槽位由原查询对回收，完整名字域由源内构造给出。
因此程序码和查询都不改变；反射只检查有界矩阵。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
include hKP hX

theorem tt_code0_reflect_l {ω : M.Domain} (hω : M.IsOmega ω) (hw : M.mem ω X)
    {d} (ρ : Env N d) (n U z p : Term d) {A : M.Domain} (hA : M.mem A X)
    (names : Tn_names_d (n.eval ρ).val (U.eval ρ).val A)
    (code : Tt_code_d (n.eval ρ).val (U.eval ρ).val (z.eval ρ).val (p.eval ρ).val (Fin.elim0 : Fin 0 → M.Domain)) :
    Formula.satisfies ρ (tt_code0_m n U z p) := by
  obtain ⟨A', C, b, names', nb, fn, pair, _⟩ := code
  have eq := hKP.1.eq_of_same_members A' A (fun x => (names' x).trans (names x).symm)
  subst A'
  let a₀ : (N).Domain := ⟨A, hA⟩
  let c₀ : (N).Domain := ⟨C, (pair.mem_l M hX (p.eval ρ).property).2⟩
  let b₀ : (N).Domain := ⟨b, hX ω hw b (num_mem_l hKP.1 hω nb)⟩
  simp only [tt_code0_m, Formula.satisfies_exists_iff]
  refine ⟨a₀, c₀, b₀, ?_⟩
  apply (rt_model_delta_l hX nx
    (.conj (tn_names0_delta_l ..) (.conj (num0_delta_l 0 _) (.conj (fn0_delta_l ..) (kpair0_delta_l ..)))) _).mpr
  simp only [Formula.satisfies_conj_iff, tn_names0_sat_l hKP, num0_sat_l hKP.1, fn0_sat_l hKP.1,
    kpair0_sat_l hKP.1, @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨names, nb, fn, pair⟩

theorem tt_code2_reflect_l {ω : M.Domain} (hω : M.IsOmega ω) (hw : M.mem ω X)
    {d} (ρ : Env N d) (n U z p a b : Term d) {A : M.Domain} (hA : M.mem A X)
    (names : Tn_names_d (n.eval ρ).val (U.eval ρ).val A)
    (code : Tt_code_d (n.eval ρ).val (U.eval ρ).val (z.eval ρ).val (p.eval ρ).val
      (Fin.cases (a.eval ρ).val (fun _ => (b.eval ρ).val) : Fin 2 → M.Domain)) :
    Formula.satisfies ρ (tt_code2_m n U z p a b) := by
  obtain ⟨A', C, l, names', nl, fn, pair, slots⟩ := code
  have eq := hKP.1.eq_of_same_members A' A (fun x => (names' x).trans (names x).symm)
  subst A'
  let a₀ : (N).Domain := ⟨A, hA⟩
  let c₀ : (N).Domain := ⟨C, (pair.mem_l M hX (p.eval ρ).property).2⟩
  let l₀ : (N).Domain := ⟨l, hX ω hw l (num_mem_l hKP.1 hω nl)⟩
  simp only [tt_code2_m, Formula.satisfies_exists_iff]
  refine ⟨a₀, c₀, l₀, ?_⟩
  apply (rt_model_delta_l hX nx (.conj (tn_names0_delta_l ..) (.conj (num0_delta_l 2 _)
    (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj
      (.forallMem _ (.imp (num0_delta_l 0 _) (rd_entry0_delta_l ..)))
      (.forallMem _ (.imp (num0_delta_l 1 _) (rd_entry0_delta_l ..)))))))) _).mpr
  simp only [Formula.satisfies_conj_iff, tn_names0_sat_l hKP, num0_sat_l hKP.1, fn0_sat_l hKP.1,
    kpair0_sat_l hKP.1, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1,
    @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨names, nl, fn, pair, fun i _ => slots 0 i, fun i _ => slots 1 i⟩

theorem tg_guard_code_reflect_l {d} (ρ : Env N d) (n κ U l z p : Term d)
    {A : M.Domain} (hA : M.mem A X) (names : Tn_names_d (n.eval ρ).val (U.eval ρ).val A)
    (code : Tg_guard_code_d (n.eval ρ).val (κ.eval ρ).val (U.eval ρ).val (l.eval ρ).val (z.eval ρ).val (p.eval ρ).val) :
    Formula.satisfies ρ (tg_guard_code_m n κ U l z p) := by
  obtain ⟨b, k, C, A', hb, hl, names', fn, pair, cp, old, last⟩ := code
  have eq := hKP.1.eq_of_same_members A' A (fun x => (names' x).trans (names x).symm)
  subst A'
  have hC := (cp.mem_l M hX (p.eval ρ).property).2
  let b₀ : (N).Domain := ⟨b, hX (l.eval ρ).val (l.eval ρ).property b hl.predecessor_mem⟩
  let k₀ : (N).Domain := ⟨k, (rd_entry_transitive_l hX hC last).2⟩
  let c₀ : (N).Domain := ⟨C, hC⟩
  let a₀ : (N).Domain := ⟨A, hA⟩
  simp only [tg_guard_code_m, Formula.satisfies_exists_iff]
  refine ⟨b₀, k₀, c₀, a₀, ?_⟩
  apply (rt_model_delta_l hX nx (.conj (KP.succ0_delta_l ..) (.conj (KP.succ0_delta_l ..)
    (.conj (tn_names0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..)
      (.conj (kpair0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..)) (rd_entry0_delta_l ..)))))))) _).mpr
  simp only [Formula.satisfies_conj_iff, KP.succ0_sat_l hKP.1, tn_names0_sat_l hKP, fn0_sat_l hKP.1,
    kpair0_sat_l hKP.1, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hKP.1,
    @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨hb, hl, names, fn, pair, cp, old, last⟩

end YesMetaZFC.SetTheory.Internal
