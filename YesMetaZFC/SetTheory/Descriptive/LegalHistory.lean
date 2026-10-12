import YesMetaZFC.SetTheory.Descriptive.FirstViolationRead

/-! # 全部有限轮均合法的内部历史树

逐步检查集合 L 只检查最新走法；本树要求历史的每个前缀都通过检查。
它与首次违规后吸收的胜负树各司其职，二者均由同一实际检查集合构造。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Cg_legal_d (F L G : M.Domain) : Prop := ∀ h,
  M.mem h G ↔ M.mem h F ∧ ∀ q, M.mem q F → M.MemberSubset q h → M.mem q L

def cg_legal_m {d} (F L G : Term d) : Formula 1 d := set[d] ⟪∀ h,
  h ∈ ⌜G⌝ₛ ↔ h ∈ ⌜F⌝ₛ ∧ (∀ q ∈ ⌜F⌝ₛ, q ⊆ h → q ∈ ⌜L⌝ₛ)⟫
derive_free_closed cg_legal_m

theorem cg_legal_sat_l {d} (ρ : Env M d) (F L G : Term d) :
    Formula.satisfies ρ (cg_legal_m F L G) ↔ Cg_legal_d (M := M) (F.eval ρ) (L.eval ρ) (G.eval ρ) := by
  simp only [cg_legal_m, Cg_legal_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem cg_legal_l (hKP : M.Models KP) (F L : M.Domain) : ∃ G, Cg_legal_d (M := M) F L G ∧ Tree_d F G := by
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push L
  let φ : Delta0UnarySchema 2 := {
    body := set[3] ⟪∀ q ∈ ⌜(.bound 2 : Term 3)⌝ₛ, q ⊆ ⌜(.newest : Term 3)⌝ₛ → q ∈ ⌜(.bound 1 : Term 3)⌝ₛ⟫
    delta0 := .forallMem _ (.imp (.atom _ _ _) (.mem _ _)) }
  obtain ⟨G, sep⟩ := KP.separation_exists_d hKP φ ρ F
  have legal : Cg_legal_d F L G := by
    intro h
    refine (sep h).trans (and_congr Iff.rfl ?_)
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
    rfl
  exact ⟨G, legal, fun h hh => ((legal h).mp hh).1, fun h hh q hq sub =>
    (legal q).mpr ⟨hq, fun t ht tq => ((legal h).mp hh).2 t ht (fun x hx => sub x (tq x hx))⟩⟩

theorem Cg_legal_d.current_l {F L G h : M.Domain} (legal : Cg_legal_d (M := M) F L G) (hh : M.mem h G) : M.mem h L :=
  ((legal h).mp hh).2 h ((legal h).mp hh).1 (fun _ hx => hx)

theorem Cg_legal_d.prefix_l {F L G h q : M.Domain} (legal : Cg_legal_d (M := M) F L G)
    (hh : M.mem h G) (hq : M.mem q F) (sub : M.MemberSubset q h) : M.mem q G :=
  (legal q).mpr ⟨hq, fun t ht tq => ((legal h).mp hh).2 t ht (fun x hx => sub x (tq x hx))⟩

end YesMetaZFC.SetTheory.Descriptive
