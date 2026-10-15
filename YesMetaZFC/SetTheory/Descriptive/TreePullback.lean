import YesMetaZFC.SetTheory.Card.FiniteSequenceRecode
import YesMetaZFC.SetTheory.Descriptive.Tree

/-! # 字母映射下树的逆像

实际分离构造逆像树。逐项复合保留前缀，故任意内部无限列属于逆像树体，
当且仅当其像属于原树体；映射无需单射或满射。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Tr_pull_d (f F T S : M.Domain) : Prop := ∀ p, M.mem p S ↔
  M.mem p F ∧ ∃ q, M.mem q T ∧ Fseq_recode_d I f p q

def tr_pull_m {d} (f F T S : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜S⌝ₛ ↔ p ∈ ⌜F⌝ₛ ∧ (∃ q ∈ ⌜T⌝ₛ, ⌜fseq_recode_m (𝒞 := 𝒞)⌝ₚ(⌜f⌝ₛ,p,q))⟫
derive_free_closed tr_pull_m

theorem tr_pull_sat_l {d} (ρ : Env M d) (f F T S : Term d) :
    Formula.satisfies ρ (tr_pull_m (𝒞 := 𝒞) f F T S) ↔ Tr_pull_d I (f.eval ρ) (F.eval ρ) (T.eval ρ) (S.eval ρ) := by
  simp only [tr_pull_m, Tr_pull_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff,
    fseq_recode_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem tr_pull_exists_l (hZF : M.Models ZF) (f F T : M.Domain) : ∃ S, Tr_pull_d I f F T S := by
  let ρ : Env M 2 := ⟨fun i => [f, T].get i, fun _ => f⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 3))
    (fseq_recode_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest)) }
  obtain ⟨S, hs⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨S, fun p => (hs p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fseq_recode_sat_l I]; rfl

variable (hZF : M.Models ZF)
include hZF

theorem Tr_pull_d.tree_l {ω X Y f F G T S : M.Domain}
    (ff : M.IsSetFunctionFromTo I f X Y) (space : Fseq_space_d I ω X F)
    (target : Fseq_space_d I ω Y G) (tree : Tree_d G T) (pull : Tr_pull_d I f F T S) : Tree_d F S := by
  refine ⟨fun p hp => ((pull p).mp hp).1, fun p hp r hr sub => ?_⟩
  obtain ⟨_, q, hq, pq⟩ := (pull p).mp hp
  obtain ⟨n, hn, fr⟩ := (space r).mp hr
  obtain ⟨s, fs, rs⟩ := ZF.fseq_compose_l I hZF ff fr
  exact (pull r).mpr ⟨hr, s, tree.2 q hq s ((target s).mpr ⟨n, hn, fs⟩) (rs.mono_l I pq sub), rs⟩

theorem Tr_pull_d.branch_l {ω X Y f F G T S p q : M.Domain} (hw : M.IsOmega ω)
    (ff : M.IsSetFunctionFromTo I f X Y) (space : Fseq_space_d I ω X F)
    (target : Fseq_space_d I ω Y G) (pull : Tr_pull_d I f F T S)
    (fp : M.IsSetFunctionFromTo I p ω X) (pq : Fseq_recode_d I f p q) : Branch_d F S p ↔ Branch_d G T q := by
  have fq := pq.function_l I hZF ff fp
  constructor
  · intro branch r hr rq
    obtain ⟨n, hn, fr⟩ := (target r).mp hr
    obtain ⟨s, fs, sp, _⟩ := ds_prefix_l I hZF hw fp hn
    obtain ⟨v, fv, sv⟩ := ZF.fseq_compose_l I hZF ff fs
    have vq := sv.mono_l I pq ((ds_restrict_iff_l I fs fp.1).mp sp)
    have eq := ((ds_restrict_iff_l I fv fq.1).mpr vq).eq hZF.1 ((ds_restrict_iff_l I fr fq.1).mpr rq)
    obtain ⟨_, t, ht, st⟩ := (pull s).mp (branch s ((space s).mpr ⟨n, hn, fs⟩) ((ds_restrict_iff_l I fs fp.1).mp sp))
    exact (st.unique_l I hZF.1 sv).trans eq ▸ ht
  · intro branch s hs sp
    obtain ⟨n, hn, fs⟩ := (space s).mp hs
    obtain ⟨t, ft, st⟩ := ZF.fseq_compose_l I hZF ff fs
    exact (pull s).mpr ⟨hs, t, branch t ((target t).mpr ⟨n, hn, ft⟩) (st.mono_l I pq sp), st⟩

end YesMetaZFC.SetTheory.Descriptive
