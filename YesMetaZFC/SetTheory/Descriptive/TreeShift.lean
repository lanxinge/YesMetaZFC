import YesMetaZFC.SetTheory.Descriptive.SequenceCons

/-! # 无约束首项的树

把任意首字母接到原节点之前，并加入空根。该树的分支恰为原分支的一项延迟，
原树或字母表为空时也适用。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Tr_shift_d (z F T S : M.Domain) : Prop := ∀ t, M.mem t S ↔ M.mem t F ∧
  (t = z ∨ ∃ a s, M.mem s T ∧ Cons_d I z a s t)

def tr_shift_m {d} (z F T S : Term d) : Formula 1 d := set[d] ⟪∀ t,
  t ∈ ⌜S⌝ₛ ↔ t ∈ ⌜F⌝ₛ ∧ (t = ⌜z⌝ₛ ∨ (∃ a s, s ∈ ⌜T⌝ₛ ∧ ⌜cons_m (𝒞 := 𝒞)⌝ₚ(⌜z⌝ₛ,a,s,t)))⟫
derive_free_closed tr_shift_m

theorem tr_shift_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z F T S : Term d) :
    Formula.satisfies ρ (tr_shift_m (𝒞 := 𝒞) z F T S) ↔ Tr_shift_d I (z.eval ρ) (F.eval ρ) (T.eval ρ) (S.eval ρ) := by
  simp only [tr_shift_m, Tr_shift_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff, cons_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem tr_shift_exists_l (hZF : M.Models ZF) (z F T : M.Domain) : ∃ S, Tr_shift_d I z F T S := by
  let ρ : Env M 2 := ⟨fun i => [z, T].get i, fun _ => z⟩
  let φ : UnarySchema 2 := {
    body := .disj (Formula.extensionalEq .newest (.bound 1))
      (.existsE (.existsE (.conj (.mem .newest (.bound 4)) (cons_m (𝒞 := 𝒞) (.bound 3) (.bound 1) .newest (.bound 2))))) }
  obtain ⟨S, hs⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨S, fun t => (hs t).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, cons_sat_l I hZF.1]; rfl

variable (hZF : M.Models ZF)
include hZF

theorem Tr_shift_d.tree_l {ω X z F T S : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T) (shift : Tr_shift_d I z F T S) : Tree_d F S := by
  refine ⟨fun t ht => ((shift t).mp ht).1, fun t ht q hq sub => (shift q).mpr ⟨hq, ?_⟩⟩
  rcases ((shift t).mp ht).2 with rfl | ⟨a, s, hs, cs⟩
  · exact Or.inl (hZF.1.eq_of_same_members q _ fun x => iff_of_false (fun hx => hz x (sub x hx)) (hz x))
  · rcases cons_cases_l I hZF hw space hz hq with eq | ⟨b, r, _, hr, cr⟩
    · exact Or.inl eq
    · obtain ⟨n, hn, fr⟩ := (space r).mp hr
      have rs := ((cons_subset_l I hZF hw hz hn fr cr cs).mp sub).2
      exact Or.inr ⟨b, r, tree.2 s hs r hr rs, cr⟩

theorem Tr_shift_d.branch_l {ω X z F T S a f g : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (ha : M.mem a X) (space : Fseq_space_d I ω X F) (subT : M.MemberSubset T F)
    (shift : Tr_shift_d I z F T S) (cons : Cons_d I z a f g) : Branch_d F S g ↔ Branch_d F T f := by
  constructor
  · intro branch s hs sf
    obtain ⟨n, hn, fs⟩ := (space s).mp hs
    obtain ⟨k, t, hk, _, ft, ct⟩ := cons_exists_l I hZF hw hz ha hn fs
    have tg := (cons_subset_l I hZF hw hz hn fs ct cons).mpr ⟨rfl, sf⟩
    rcases ((shift t).mp (branch t ((space t).mpr ⟨k, hk, ft⟩) tg)).2 with eq | ⟨b, r, hr, cr⟩
    · exact (cons_ne_empty_l I hz ct eq).elim
    · obtain ⟨m, hm, fr⟩ := (space r).mp (subT r hr)
      exact ((cons_injective_l I hZF hw hz hn hm fs fr ct cr).2).symm ▸ hr
  · intro branch t ht tg
    refine (shift t).mpr ⟨ht, ?_⟩
    rcases cons_cases_l I hZF hw space hz ht with eq | ⟨b, s, _, hs, cs⟩
    · exact Or.inl eq
    · obtain ⟨n, hn, fs⟩ := (space s).mp hs
      exact Or.inr ⟨b, s, branch s hs ((cons_subset_l I hZF hw hz hn fs cs cons).mp tg).2, cs⟩

end YesMetaZFC.SetTheory.Descriptive
