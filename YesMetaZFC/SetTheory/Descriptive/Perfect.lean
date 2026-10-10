import YesMetaZFC.SetTheory.Descriptive.Perfect.Branches
import YesMetaZFC.SetTheory.Descriptive.Analytic.Diagonal

/-! # 解析集与有码 Borel 集的完美集定理

完美指闭且无孤立点。结论构造模型内部的非空完美子集；分裂导集消失时则
构造实际可数编号。所有实数、序数阶段和递归轨道都属于原模型，只需 ZF。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Perfect_d (A B P : M.Domain) : Prop := Cl_d A B P ∧ ∀ x s, M.mem x P → M.mem s A → M.MemberSubset s x →
  ∃ y, M.mem y P ∧ M.MemberSubset s y ∧ y ≠ x
def perfect_m {d} (A B P : Term d) : Formula 1 d := .conj (cl_m A B P) (.forallE (.forallE (.imp
  (.mem (.bound 1) P.weaken.weaken) (.imp (.mem .newest A.weaken.weaken) (.imp (Formula.subset .newest (.bound 1))
  (Formula.existsMem P.weaken.weaken (.conj (Formula.subset (.bound 1) .newest) (.neg (Formula.extensionalEq .newest (.bound 2))))))))))
derive_free_closed perfect_m
theorem perfect_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A B P : Term d) :
    Formula.satisfies ρ (perfect_m A B P) ↔ Perfect_d (M := M) (A.eval ρ) (B.eval ρ) (P.eval ρ) := by
  simp only [perfect_m, Perfect_d, Formula.satisfies_conj_iff, cl_sat_l, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

theorem pw_noisolated_l (hZF : M.Models ZF) {ω A B J U L R a x s} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U)
    (hx : M.mem x B) (path : Pw_d I ω J U L R a x) (hsa : M.mem s A) (hsx : M.MemberSubset s x) :
    ∃ y, M.mem y B ∧ Pw_d I ω J U L R a y ∧ M.MemberSubset s y ∧ y ≠ x := by
  classical
  obtain ⟨n, hn, hsf⟩ := (hA s).mp hsa
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  obtain ⟨H, hh, hz, next⟩ := ZFC.iterate_l I hZF hB.1 hf.1 ha
  have it : It_d I ω U F a H := ⟨hh, hz, next⟩
  have step b c (hb : M.PairMember I b c F) := ((hf.2 b c).mp hb).2.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  obtain ⟨b, hb, hnb⟩ := hh.2.2 n hn
  have wb : Walk_d I ω J U L R a n b x := ⟨F, hf, H, it, hnb⟩
  obtain ⟨m, _, hbf⟩ := (hA b).mp (hs.1 b hb)
  obtain ⟨u, v, pb⟩ := fp_decode_l I hZF hA hJ (hs.1 b hb)
  have uf := (fp_at_l I hZF hJ pb hbf).1
  have sub : M.MemberSubset s u := ds_prefix_mono_l I hsf uf.1
    ((ds_restrict_iff_l I hsf ((hB.2 x).mp hx).1).mpr hsx)
    ((ds_restrict_iff_l I uf ((hB.2 x).mp hx).1).mpr ((pre_iff_l I hZF.1 hJ pb).mp (path n b hn wb)))
    (split_iter_length_l I hZF hB.1 hA hJ hs it step n hn b m hnb hbf)
  obtain ⟨c, _, hc⟩ := hs.2.1.2.2 b hb
  obtain ⟨d, _, hd⟩ := hs.2.2.1.2.2 b hb
  obtain ⟨e, child, bad⟩ : ∃ e, (M.PairMember I b e L ∨ M.PairMember I b e R) ∧ ¬ Pre_d I ω J e x := by
    by_cases pc : Pre_d I ω J c x
    · exact ⟨d, Or.inr hd, fun pd => pre_disjoint_l I hZF.1 hJ (hs.2.2.2 b c d hc hd).2.2 ((hB.2 x).mp hx).1 pc pd⟩
    · exact ⟨c, Or.inl hc, pc⟩
  have he := child.elim hs.2.1.output_mem_of_pairMember hs.2.2.1.output_mem_of_pairMember
  obtain ⟨y, hy, py⟩ := pw_nonempty_l I hZF hB hA hJ hs he
  have ey := pw_pre_l I hZF hB.1 hs he py
  have by' := pw_prepend_l I hZF hB hA hJ hs hy child py
  have uy := (pre_iff_l I hZF.1 hJ pb).mp (pw_pre_l I hZF hB.1 hs hb by')
  exact ⟨y, hy, pw_ancestor_l I hZF hB hA hJ hs ha n hn b x y hy wb by',
    fun p hp => uy p (sub p hp), fun eqn => bad (eqn ▸ ey)⟩

theorem splitting_perfect_l (hZF : M.Models ZF) {ω A B J U T} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hc : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hT : Tree_d A T) (sub : M.MemberSubset U T) (hne : ∃ a, M.mem a U)
    (split : ∀ a, M.mem a U → Sp_d I ω J U a) : ∃ P, Perfect_d A B P ∧ (∃ x, M.mem x P) ∧
      ∀ x, M.mem x P → ∃ y p, M.mem y B ∧ M.mem p B ∧ Rp_d I J x y p ∧ Branch_d A T p := by
  obtain ⟨L, R, hs⟩ := splitting_l I hZF hB.1 hc (fun a ha => hT.1 a (sub a ha)) split
  obtain ⟨a, ha⟩ := hne
  obtain ⟨P, hp, ep⟩ := pw_closed_l I hZF hB hA hJ hs ha
  obtain ⟨x, hx, px⟩ := pw_nonempty_l I hZF hB hA hJ hs ha
  refine ⟨P, ⟨hp, fun x s hx hsA hsx => ?_⟩, ⟨x, (ep x).mpr ⟨hx, px⟩⟩, fun x hx => ?_⟩
  · obtain ⟨y, hy, py, sub, ne⟩ := pw_noisolated_l I hZF hB hA hJ hs ha ((ep x).mp hx).1 ((ep x).mp hx).2 hsA hsx
    exact ⟨y, (ep y).mpr ⟨hy, py⟩, sub, ne⟩
  · exact pw_realize_l I hZF hB hA hJ hs ha hT sub ((ep x).mp hx).1 ((ep x).mp hx).2

/-- 解析集的可数／含非空完美子集二择一，两个分支都返回实际模型对象。 -/
theorem an_perfect_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hc : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hk : An_d I ω A B J K) : M.CardinalLessOrEqual I K ω ∨
      ∃ P, Perfect_d A B P ∧ (∃ x, M.mem x P) ∧ M.MemberSubset P K := by
  classical
  obtain ⟨T, hT⟩ := (an_tree_iff_l I hZF hB hA hc hJ).mp hk
  obtain ⟨α, U, _, hu, stable⟩ := sd_stable_l I hZF ω J T
  -- 非空稳定核给出全分裂系统；空稳定核给出“消失前缀 → 唯一实数”的可数满射。
  by_cases hn : ∃ a, M.mem a U
  · obtain ⟨P, hp, ne, branch⟩ := splitting_perfect_l I hZF hB hA hc hJ hT.1 (sd_sub_l I hu) hn (fun a ha => (stable a).mp ha)
    refine Or.inr ⟨P, hp, ne, fun x hx => ?_⟩
    obtain ⟨y, p, hy, hpB, pair, path⟩ := branch x hx
    obtain ⟨_, C, body, proj⟩ := hT
    exact (proj x).mpr ⟨hp.1.1 x hx, y, p, hy, hpB, pair, (body p).mpr ⟨hpB, path⟩⟩
  · exact Or.inl (sd_empty_countable_l I hZF hB hA hc hJ hT hu (fun a ha => hn ⟨a, ha⟩))

theorem borel_perfect_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hc : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hk : Borel_d I ω A A B K) : M.CardinalLessOrEqual I K ω ∨
      ∃ P, Perfect_d A B P ∧ (∃ x, M.mem x P) ∧ M.MemberSubset P K :=
  an_perfect_l I hZF hB hA hc hJ (borel_an_l I hZF hB hA hc hJ hk)

/-- 从 ZF 模型直接构造完美集定理所需的空间、可数基及配对。 -/
theorem dst_perfect_l (hZF : M.Models ZF) : ∃ ω A B J,
    Baire_d I ω B ∧ Fseq_space_d I ω ω A ∧ M.CardinalLessOrEqual I A ω ∧ Npair_d I ω J ∧
    ∀ K, An_d I ω A B J K → M.CardinalLessOrEqual I K ω ∨
      ∃ P, Perfect_d A B P ∧ (∃ x, M.mem x P) ∧ M.MemberSubset P K := by
  obtain ⟨ω, _, B, _, A, _, hB, _, _, hA, hc, _, _⟩ := ds_spaces_l I hZF
  obtain ⟨J, hJ⟩ := npair_exists_l I hZF hB.1
  exact ⟨ω, A, B, J, hB, hA, hc, hJ, fun _ h => an_perfect_l I hZF hB hA hc hJ h⟩

end YesMetaZFC.SetTheory.Descriptive
