import YesMetaZFC.SetTheory.Descriptive.GameAvoid
import YesMetaZFC.SetTheory.Ord.DefinableMinimum

/-! # 避让策略的全部内部有限前缀

若一条服从策略的对局进入 II 获胜区，取模型内部最早进入的长度。
其前驱局面尚在补集中，两位玩家的闭包性质都排除这一步。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_avoid_run_l {ω X F J B W Z Q e σ f : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (strategies : M.IsFunctionSpace I Z F X) (positions : Cg_ii_d I ω X F J B W Q)
    (he : ∀ x, ¬ M.mem x e) (root : ¬ M.mem e Q)
    (avoid : ∀ s x, Rd_entry_d s x σ → Cg_avoid_d I ω X J Q s x)
    (hf : M.mem f B) (follows : Cg_follows_d I true ω J σ f) :
    ∀ s, M.mem s F → M.MemberSubset s f → ¬ M.mem s Q := by
  classical
  have ff := (runs f).mp hf
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Q).push f
  let φ : UnarySchema 4 := { body := set[5] ⟪⌜(.newest : Term 5)⌝ₛ ∈ ⌜(.bound 4 : Term 5)⌝ₛ ∧
    (∃ t ∈ ⌜(.bound 2 : Term 5)⌝ₛ, ⌜fn0_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, t) ∧
      t ⊆ ⌜(.bound 1 : Term 5)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ M.mem n ω ∧ ∃ t, M.mem t Q ∧ Fn0_d n X t ∧ M.MemberSubset t f := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
    rfl
  intro s hs sf hit
  obtain ⟨k, hk, fs⟩ := (space s).mp hs
  obtain ⟨n, no, hn, least⟩ := ZF.ordinal_min_l hZF φ ρ (hω.members_areOrdinals hZF k hk)
    ((sat k).mpr ⟨hk, s, hit, fn0_of_function_l (ZF.modelsKP hZF) fs, sf⟩)
  obtain ⟨hn, t, ht, ft₀, tf⟩ := (sat n).mp hn
  have ft := fn0_function_l (ZF.modelsKP hZF) ft₀
  have nonempty : ∃ x, M.mem x n := by
    apply Classical.byContradiction
    intro empty
    have eq : t = e := hZF.1.eq_of_same_members t e (fun p => iff_of_false (fun hp => by
      obtain ⟨i, hi, _, _, _⟩ := ft₀.1 p hp
      exact empty ⟨i, hi⟩) (he p))
    exact root (eq ▸ ht)
  obtain ⟨i, hi, next⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hn nonempty
  obtain ⟨p, fp, pr, _⟩ := ds_prefix_l I hZF hω ff hi
  have pf := (ds_restrict_iff_l I fp ff.1).mp pr
  have outside : ¬ M.mem p Q := fun hp => least i next.predecessor_mem ((sat i).mpr
    ⟨hi, p, hp, fn0_of_function_l (ZF.modelsKP hZF) fp, pf⟩)
  have tr := (ds_restrict_iff_l I ft ff.1).mpr tf
  have pt := ds_prefix_mono_l I fp ft.1 pr tr (no.transitive i next.predecessor_mem)
  obtain ⟨x, hx, read⟩ := ff.2.2 i hi
  have endt : Fseq_end_d I ω t p x := ⟨n, i,
    ⟨⟨hn, no, ft.1, ft.2.1⟩, hi, next, ⟨hi, (hω.isOrdinal hZF).mem hi, fp.1, fp.2.1⟩,
      (ds_restrict_iff_l I fp ft.1).mpr pt, (tr.2 i x).mpr ⟨next.predecessor_mem, read⟩⟩⟩
  by_cases turn : M.mem i J
  · exact avoid p x (follows i hi turn p pr x read) i
      (fn0_of_function_l (ZF.modelsKP hZF) fp) turn outside t endt ht
  · exact outside (cg_ii_some_l hZF hω space runs strategies positions hi fp hx turn endt ht)

end YesMetaZFC.SetTheory.Descriptive
